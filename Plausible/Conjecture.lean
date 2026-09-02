/-
Copyright (c) 2024 Plausible Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

public section

/-!
# Conjecture Engine

Hypothesis-style testing: generate bytes, interpret via `Strategy`, shrink bytes.
No per-type `Shrinkable` needed. See https://hypothesis.works/articles/how-hypothesis-works/
-/

namespace Plausible.Conjecture

instance : Repr ByteArray where
  reprPrec ba _ :=
    let hex := ba.toList.map fun b =>
      let hi := b.toNat / 16
      let lo := b.toNat % 16
      let toHexDigit n := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
      s!"{toHexDigit hi}{toHexDigit lo}"
    Repr.addAppParen s!"ByteArray.mk #{hex}" 0

/-- Interval [start, stop) in the byte buffer. Shrinking prefers complete spans. -/
structure Span where
  start : Nat
  stop : Nat
  label : String := ""
  deriving Repr, BEq, Inhabited

inductive Status where
  | valid | interesting | invalid | overrun
  deriving Repr, BEq, Inhabited

/-- Byte buffer with span annotations for shrinking. -/
structure ChoiceSequence where
  buffer : ByteArray
  spans : Array Span
  index : Nat := 0
  spanStack : List Nat := []
  maxSize : Nat := 8 * 1024
  deriving Repr, Inhabited

namespace ChoiceSequence

def empty (maxSize : Nat := 8 * 1024) : ChoiceSequence :=
  { buffer := ByteArray.empty, spans := #[], maxSize }

def ofBytes (bytes : ByteArray) (maxSize : Nat := 8 * 1024) : ChoiceSequence :=
  { buffer := bytes, spans := #[], maxSize }

def size (cs : ChoiceSequence) : Nat := cs.buffer.size
def remaining (cs : ChoiceSequence) : Nat := cs.buffer.size - cs.index
def exhausted (cs : ChoiceSequence) : Bool := cs.index >= cs.buffer.size

def lexLt (cs1 cs2 : ChoiceSequence) : Bool :=
  let b1 := cs1.buffer
  let b2 := cs2.buffer
  -- Shorter is smaller
  if b1.size < b2.size then true
  else if b1.size > b2.size then false
  else
    -- Same size: lexicographic on bytes
    let rec go (i : Nat) : Bool :=
      if i >= b1.size then false  -- equal
      else if b1.get! i < b2.get! i then true
      else if b1.get! i > b2.get! i then false
      else go (i + 1)
    go 0

end ChoiceSequence

inductive DrawResult (α : Type) where
  | ok (value : α) (cs : ChoiceSequence)
  | overrun
  deriving Inhabited

abbrev StrategyM (α : Type) := ChoiceSequence → DrawResult α

instance : Monad StrategyM where
  pure a := fun cs => .ok a cs
  bind ma f := fun cs =>
    match ma cs with
    | .ok a cs' => f a cs'
    | .overrun => .overrun

instance : MonadExcept Unit StrategyM where
  throw _ := fun _ => .overrun
  tryCatch ma handler := fun cs =>
    match ma cs with
    | .overrun => handler () cs
    | result => result

namespace StrategyM

def drawBytes (n : Nat) : StrategyM ByteArray := fun cs =>
  if cs.index + n > cs.buffer.size then .overrun
  else .ok (cs.buffer.extract cs.index (cs.index + n)) { cs with index := cs.index + n }

def drawByte : StrategyM UInt8 := do
  let bytes ← drawBytes 1
  return bytes.get! 0

def startSpan : StrategyM Unit := fun cs =>
  .ok () { cs with spanStack := cs.index :: cs.spanStack }

def endSpan (label : String := "") : StrategyM Unit := fun cs =>
  match cs.spanStack with
  | [] => .ok () cs
  | start :: rest =>
    .ok () { cs with spans := cs.spans.push { start, stop := cs.index, label }, spanStack := rest }

def withSpan (label : String := "") (m : StrategyM α) : StrategyM α := do
  startSpan
  let result ← m
  endSpan label
  return result

def getSize : StrategyM Nat := fun cs =>
  .ok (cs.remaining / 10 |>.max 1) cs

end StrategyM

class Strategy (α : Type) where
  draw : StrategyM α

namespace Strategy

instance instStrategyNat : Strategy Nat where
  draw := StrategyM.withSpan "Nat" do
    let bytes ← StrategyM.drawBytes 8
    return (List.range 8).foldl (init := 0) fun acc i => acc * 256 + (bytes.get! i).toNat

def natBelow (n : Nat) : StrategyM Nat := StrategyM.withSpan "Nat<" do
  return (← instStrategyNat.draw) % n

def natRange (lo hi : Nat) : StrategyM Nat := StrategyM.withSpan "Nat[]" do
  return lo + (← instStrategyNat.draw) % (hi - lo + 1)

instance : Strategy Bool where
  draw := StrategyM.withSpan "Bool" do
    return (← StrategyM.drawByte) % 2 == 1

instance : Strategy Int where
  draw := StrategyM.withSpan "Int" do
    let magnitude ← instStrategyNat.draw
    let negative ← Strategy.draw (α := Bool)
    return if negative then -magnitude else magnitude

instance : Strategy UInt8 where
  draw := StrategyM.withSpan "UInt8" StrategyM.drawByte

instance : Strategy UInt64 where
  draw := StrategyM.withSpan "UInt64" do
    let bytes ← StrategyM.drawBytes 8
    return (List.range 8).foldl (init := (0 : UInt64)) fun acc i => acc * 256 + (bytes.get! i).toUInt64

instance : Strategy Char where
  draw := StrategyM.withSpan "Char" do
    return Char.ofNat (32 + (← StrategyM.drawByte).toNat % 95)  -- printable ASCII

partial def list (elem : StrategyM α) : StrategyM (List α) := StrategyM.withSpan "List" do
  if !(← Strategy.draw (α := Bool)) then return []
  return (← elem) :: (← list elem)

instance instStrategyList [Strategy α] : Strategy (List α) where
  draw := list Strategy.draw

instance [Strategy α] : Strategy (Array α) where
  draw := StrategyM.withSpan "Array" do return (← instStrategyList.draw).toArray

instance : Strategy String where
  draw := StrategyM.withSpan "String" do return String.ofList (← instStrategyList (α := Char).draw)

instance [Strategy α] : Strategy (Option α) where
  draw := StrategyM.withSpan "Option" do
    if ← Strategy.draw (α := Bool) then return some (← Strategy.draw)
    return none

instance [Strategy α] [Strategy β] : Strategy (α × β) where
  draw := StrategyM.withSpan "Prod" do return (← Strategy.draw, ← Strategy.draw)

instance [Strategy α] [Strategy β] : Strategy (Sum α β) where
  draw := StrategyM.withSpan "Sum" do
    if ← Strategy.draw (α := Bool) then return .inl (← Strategy.draw)
    return .inr (← Strategy.draw)

instance {n : Nat} : Strategy (Fin n.succ) where
  draw := StrategyM.withSpan "Fin" do
    let raw ← instStrategyNat.draw
    return ⟨raw % n.succ, Nat.mod_lt raw (Nat.zero_lt_succ n)⟩

end Strategy

namespace Shrinker

def deleteSpans (cs : ChoiceSequence) : List ChoiceSequence :=
  cs.spans.toList.filterMap fun span =>
    if span.stop <= cs.buffer.size then
      some { cs with
        buffer := cs.buffer.extract 0 span.start ++ cs.buffer.extract span.stop cs.buffer.size
        spans := #[]
        index := 0
      }
    else none

def reduceBytes (cs : ChoiceSequence) : List ChoiceSequence :=
  List.range cs.buffer.size |>.filterMap fun i =>
    let byte := cs.buffer.get! i
    if byte > 0 then some { cs with buffer := cs.buffer.set! i (byte / 2), spans := #[], index := 0 }
    else none

def zeroSpans (cs : ChoiceSequence) : List ChoiceSequence :=
  cs.spans.toList.filterMap fun span =>
    if span.stop <= cs.buffer.size then
      let newBuffer := Id.run do
        let mut buf := cs.buffer
        for i in [span.start:span.stop] do
          buf := buf.set! i 0
        return buf
      some { cs with buffer := newBuffer, spans := #[], index := 0 }
    else none

def sortedByteReductions (cs : ChoiceSequence) : List ChoiceSequence :=
  let indexed := List.range cs.buffer.size |>.map fun i => (i, cs.buffer.get! i)
  let sorted := indexed.filter (·.2 > 0) |>.toArray.qsort (fun a b => a.2 > b.2) |>.toList
  sorted.filterMap fun (i, byte) =>
    some { cs with buffer := cs.buffer.set! i (byte / 2), spans := #[], index := 0 }

def shrink (cs : ChoiceSequence) : List ChoiceSequence :=
  deleteSpans cs ++ zeroSpans cs ++ sortedByteReductions cs

def filterSmaller (original : ChoiceSequence) (candidates : List ChoiceSequence) : List ChoiceSequence :=
  candidates.filter (·.lexLt original)

end Shrinker

def generateRandom (size : Nat) : IO ChoiceSequence := do
  let mut buf := ByteArray.empty
  for _ in [:size] do
    buf := buf.push (← IO.rand 0 255).toUInt8
  return { buffer := buf, spans := #[], maxSize := size * 2 }

def defaultDbPath : System.FilePath := ".plausible" / "examples"

structure DbEntry where
  testName : String
  choiceSeq : ByteArray
  timestamp : Nat
  deriving Repr

namespace ExampleDb

def ensureDir (path : System.FilePath := defaultDbPath) : IO Unit :=
  IO.FS.createDirAll path

def save (testName : String) (cs : ChoiceSequence) (path : System.FilePath := defaultDbPath) : IO Unit := do
  ensureDir path
  IO.FS.writeBinFile (path / s!"{testName}.bin") cs.buffer

def load (testName : String) (path : System.FilePath := defaultDbPath) : IO (Option ChoiceSequence) := do
  let filename := path / s!"{testName}.bin"
  if ← filename.pathExists then
    return some (ChoiceSequence.ofBytes (← IO.FS.readBinFile filename))
  return none

def listTests (path : System.FilePath := defaultDbPath) : IO (List String) := do
  if ← path.pathExists then
    return (← path.readDir).toList.filterMap fun entry =>
      if entry.fileName.endsWith ".bin" then some (entry.fileName.dropEnd 4).toString
      else none
  return []

end ExampleDb

inductive HealthWarning where
  | tooSlow (avgMs : Float)
  | filterTooMuch (ratio : Float)
  | dataTooLarge (avgBytes : Float)
  deriving Repr

namespace HealthCheck

def checkSpeed (totalMs : Float) (numExamples : Nat) : Option HealthWarning :=
  let avgMs := totalMs / numExamples.toFloat
  if avgMs > 200.0 then some (.tooSlow avgMs) else none

def checkFilterRatio (validCount invalidCount : Nat) : Option HealthWarning :=
  let total := validCount + invalidCount
  if total > 0 then
    let ratio := invalidCount.toFloat / total.toFloat
    if ratio > 0.5 then some (.filterTooMuch ratio) else none
  else none

def checkDataSize (totalBytes : Nat) (numExamples : Nat) : Option HealthWarning :=
  let avgBytes := totalBytes.toFloat / (if numExamples > 0 then numExamples.toFloat else 1.0)
  if avgBytes > 4096.0 then some (.dataTooLarge avgBytes) else none

def runAll (totalMs : Float) (validCount invalidCount : Nat) (totalBytes : Nat) : List HealthWarning :=
  [checkSpeed totalMs (validCount + invalidCount),
   checkFilterRatio validCount invalidCount,
   checkDataSize totalBytes validCount].filterMap id

end HealthCheck

def negInfinity : Float := -1.0e308

structure TargetState where
  bestScore : Float := negInfinity
  bestChoiceSeq : Option ChoiceSequence := none
  observations : Array (Float × ChoiceSequence) := #[]
  deriving Inhabited

namespace Targeted

def observe (score : Float) (cs : ChoiceSequence) (state : TargetState) : TargetState :=
  let newObs := state.observations.push (score, cs)
  if score > state.bestScore then
    { bestScore := score, bestChoiceSeq := some cs, observations := newObs }
  else
    { state with observations := newObs }

def mutate (cs : ChoiceSequence) (mutationRate : Float := 0.1) : IO ChoiceSequence := do
  let mut buf := cs.buffer
  for i in [:cs.buffer.size] do
    if (← IO.rand 0 100).toFloat / 100.0 < mutationRate then
      buf := buf.set! i (← IO.rand 0 255).toUInt8
  return { cs with buffer := buf, spans := #[], index := 0 }

def selectForMutation (state : TargetState) : IO (Option ChoiceSequence) := do
  if state.observations.isEmpty then return none
  let sorted := state.observations.toList.toArray.qsort (fun a b => a.1 > b.1)
  let topCount := (sorted.size / 4).max 1
  return some sorted[← IO.rand 0 (topCount - 1)]!.2

end Targeted

structure Config where
  numTests : Nat := 100
  initialSize : Nat := 64
  maxSize : Nat := 8 * 1024
  useDb : Bool := true
  healthChecks : Bool := true
  targeted : Bool := false
  mutationRate : Float := 0.1
  traceShrink : Bool := false
  quiet : Bool := false
  deriving Repr, Inhabited

structure TestRun where
  status : Status
  choiceSeq : ChoiceSequence
  shrinkSteps : Nat := 0
  healthWarnings : List HealthWarning := []
  targetState : TargetState := {}
  deriving Inhabited

def runStrategy [Strategy α] (cs : ChoiceSequence) : Option (α × ChoiceSequence) :=
  match Strategy.draw (α := α) cs with
  | .ok value cs' => some (value, cs')
  | .overrun => none

partial def shrinkLoop [Strategy α] (test : α → Bool) (cs : ChoiceSequence)
    (maxSteps : Nat := 1000) (trace : Bool := false) : ChoiceSequence × Nat :=
  let rec go (current : ChoiceSequence) (steps : Nat) (fuel : Nat) : ChoiceSequence × Nat :=
    if fuel == 0 then (current, steps)
    else
      let candidates := Shrinker.shrink current |> Shrinker.filterSmaller current
      match candidates.find? fun c =>
        match runStrategy (α := α) c with
        | some (value, _) => !test value
        | none => false
      with
      | some smaller =>
        if trace then
          dbgTrace s!"[Shrink] {current.size} → {smaller.size} bytes" fun _ =>
            go smaller (steps + 1) (fuel - 1)
        else
          go smaller (steps + 1) (fuel - 1)
      | none => (current, steps)
  go cs 0 maxSteps

end Plausible.Conjecture
