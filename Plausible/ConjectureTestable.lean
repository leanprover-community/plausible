/-
Copyright (c) 2024 Plausible Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

public import Plausible.Conjecture
public import Plausible.Testable

public section

/-!
# Conjecture-based Testable

This module integrates the Conjecture engine with Plausible's Testable framework.

## Key Benefits

1. **No Shrinkable instances needed**: Shrinking happens at the byte level
2. **Better shrinking**: The Conjecture engine can shrink compositionally
3. **Example persistence**: Counterexamples are saved and replayed
4. **Health checks**: Automatic detection of slow/problematic generators
5. **Targeted testing**: Guide the search toward interesting regions

## Usage

```lean
-- Use the Conjecture engine to test a property
#conjecture ∀ n : Nat, n < 100 → n * n < 10000

-- Or programmatically
def myTest : IO Unit := do
  Plausible.Conjecture.Testable.check "myTest" (∀ n : Nat, n + 0 = n)
```
-/

namespace Plausible.Conjecture

open Plausible

/-- Configuration for Conjecture-based testing -/
structure ConjectureConfig where
  /-- Number of test cases to generate -/
  numTests : Nat := 100
  /-- Maximum size of choice sequences (in bytes) -/
  maxBytes : Nat := 8 * 1024
  /-- Maximum shrink steps -/
  maxShrinkSteps : Nat := 1000
  /-- Enable shrinking -/
  shrink : Bool := true
  /-- Trace shrinking steps -/
  traceShrink : Bool := false
  /-- Enable health checks -/
  healthChecks : Bool := true
  /-- Enable example database (persistence) -/
  useExampleDb : Bool := true
  /-- Test name for example database -/
  testName : String := ""
  /-- Enable targeted testing -/
  targeted : Bool := false
  /-- Quiet mode (no output) -/
  quiet : Bool := false
  deriving Inhabited, Repr

/-- Result of a Conjecture-based test -/
inductive ConjectureResult where
  /-- All tests passed -/
  | success (numTests : Nat)
  /-- Found a counterexample -/
  | failure (counterexample : String) (shrinkSteps : Nat) (choiceSeq : ChoiceSequence)
  /-- Gave up due to too many invalid examples -/
  | gaveUp (numInvalid : Nat)
  /-- Error during testing -/
  | error (message : String)
  deriving Inhabited

namespace ConjectureResult

def isSuccess : ConjectureResult → Bool
  | .success _ => true
  | _ => false

def isFailure : ConjectureResult → Bool
  | .failure _ _ _ => true
  | _ => false

def toString : ConjectureResult → String
  | .success n => s!"Success: {n} tests passed"
  | .failure ce shrinks _ => s!"Failure: {ce} (after {shrinks} shrinks)"
  | .gaveUp n => s!"Gave up after {n} invalid examples"
  | .error msg => s!"Error: {msg}"

instance : ToString ConjectureResult := ⟨toString⟩

end ConjectureResult

/-- A property that can be tested using the Conjecture engine -/
class ConjectureTestable (p : Prop) where
  /-- The type used to generate test inputs -/
  InputType : Type
  /-- Strategy for generating inputs from bytes -/
  strategy : Strategy InputType
  /-- Convert input to a proposition result -/
  test : InputType → Bool
  /-- Repr instance for displaying counterexamples -/
  repr : InputType → String

namespace ConjectureTestable

/-- Run a single test case -/
def runOne [ConjectureTestable p] (cs : ChoiceSequence) : Option (Bool × String × ChoiceSequence) :=
  match ConjectureTestable.strategy.draw cs with
  | .ok value cs' =>
    let result := ConjectureTestable.test (p := p) value
    let repr := ConjectureTestable.repr (p := p) value
    some (result, repr, cs')
  | .overrun => none

/-- Shrink a failing choice sequence -/
def shrinkFailure [inst : ConjectureTestable p] (cs : ChoiceSequence) (cfg : ConjectureConfig) :
    ChoiceSequence × Nat :=
  if !cfg.shrink then (cs, 0)
  else
    let test (input : inst.InputType) : Bool := inst.test input
    @shrinkLoop inst.InputType inst.strategy test cs cfg.maxShrinkSteps cfg.traceShrink

/-- Run the test suite -/
def runSuite [ConjectureTestable p] (cfg : ConjectureConfig) : IO ConjectureResult := do
  let startTime ← IO.monoMsNow

  -- Check for saved failing examples first
  if cfg.useExampleDb && cfg.testName != "" then
    if let some savedCs ← ExampleDb.load cfg.testName then
      match runOne (p := p) savedCs with
      | some (false, repr, _) =>
        if !cfg.quiet then
          IO.println s!"[Conjecture] Replayed saved counterexample: {repr}"
        return .failure repr 0 savedCs
      | _ => pure ()  -- Saved example no longer fails, continue testing

  let mut numValid := 0
  let mut numInvalid := 0
  let mut totalBytes := 0

  for _ in [:cfg.numTests] do
    -- Generate random bytes
    let cs ← generateRandom cfg.maxBytes

    match runOne (p := p) cs with
    | none =>
      -- Overrun - not enough bytes
      numInvalid := numInvalid + 1
    | some (true, _, cs') =>
      -- Test passed
      numValid := numValid + 1
      totalBytes := totalBytes + cs'.index
    | some (false, repr, cs') =>
      -- Test failed! Shrink and report
      -- Trim to only the used bytes and reset index for shrinking
      let usedBytes := cs'.buffer.extract 0 cs'.index
      let csForShrink : ChoiceSequence := {
        buffer := usedBytes
        spans := cs'.spans
        index := 0
        maxSize := cs'.maxSize
      }
      let (shrunkCs, shrinkSteps) := shrinkFailure (p := p) csForShrink cfg

      -- Get the shrunk counterexample
      let finalRepr := match runOne (p := p) shrunkCs with
        | some (_, r, _) => r
        | none => repr

      -- Save to example database
      if cfg.useExampleDb && cfg.testName != "" then
        ExampleDb.save cfg.testName shrunkCs

      return .failure finalRepr shrinkSteps shrunkCs

  let endTime ← IO.monoMsNow
  let totalMs := (endTime - startTime).toFloat

  -- Run health checks
  if cfg.healthChecks && !cfg.quiet then
    let warnings := HealthCheck.runAll totalMs numValid numInvalid totalBytes
    for warning in warnings do
      IO.println s!"[Conjecture Warning] {Repr.reprPrec warning 0}"

  if numInvalid > cfg.numTests / 2 then
    return .gaveUp numInvalid
  else
    return .success numValid

end ConjectureTestable

/-- Check a property using the Conjecture engine -/
def check [ConjectureTestable p] (testName : String := "") (cfg : ConjectureConfig := {}) : IO Unit := do
  let cfg := { cfg with testName }
  let result ← ConjectureTestable.runSuite (p := p) cfg
  match result with
  | .success n =>
    if !cfg.quiet then
      IO.println s!"✓ {n} tests passed"
  | .failure ce shrinks _ =>
    throw <| IO.userError s!"✗ Counterexample found: {ce} (after {shrinks} shrinks)"
  | .gaveUp n =>
    IO.println s!"⚠ Gave up after {n} invalid examples"
  | .error msg =>
    throw <| IO.userError s!"Error: {msg}"

/-- Check a property and return the result -/
def checkResult [ConjectureTestable p] (testName : String := "") (cfg : ConjectureConfig := {}) :
    IO ConjectureResult := do
  let cfg := { cfg with testName }
  ConjectureTestable.runSuite (p := p) cfg

-- Instance for decidable propositions about Nat
instance natPropTestable {f : Nat → Prop} [DecidablePred f] : ConjectureTestable (∀ n : Nat, f n) where
  InputType := Nat
  strategy := Strategy.instStrategyNat
  test := fun n => decide (f n)
  repr := fun n => s!"n := {n}"

-- Instance for decidable propositions about Bool
instance boolPropTestable {f : Bool → Prop} [DecidablePred f] : ConjectureTestable (∀ b : Bool, f b) where
  InputType := Bool
  strategy := inferInstance
  test := fun b => decide (f b)
  repr := fun b => s!"b := {b}"

-- Instance for decidable propositions about pairs of Nats
instance natPairPropTestable {f : Nat → Nat → Prop} [∀ n m, Decidable (f n m)] :
    ConjectureTestable (∀ n m : Nat, f n m) where
  InputType := Nat × Nat
  strategy := inferInstance
  test := fun (n, m) => decide (f n m)
  repr := fun (n, m) => s!"n := {n}, m := {m}"

-- Instance for decidable propositions about Int
instance intPropTestable {f : Int → Prop} [DecidablePred f] : ConjectureTestable (∀ n : Int, f n) where
  InputType := Int
  strategy := inferInstance
  test := fun n => decide (f n)
  repr := fun n => s!"n := {n}"

-- Instance for decidable propositions about String
instance stringPropTestable {f : String → Prop} [DecidablePred f] :
    ConjectureTestable (∀ s : String, f s) where
  InputType := String
  strategy := inferInstance
  test := fun s => decide (f s)
  repr := fun s => s!"s := \"{s}\""

-- Instance for decidable propositions about Lists
instance listPropTestable {α} [Strategy α] [Repr α] {f : List α → Prop} [DecidablePred f] :
    ConjectureTestable (∀ xs : List α, f xs) where
  InputType := List α
  strategy := inferInstance
  test := fun xs => decide (f xs)
  repr := fun xs => s!"xs := {repr xs}"

-- Instance for implication (guarded properties)
instance impTestable {p : Prop} {q : Prop} [Decidable p] [ConjectureTestable q] :
    ConjectureTestable (p → q) where
  InputType := ConjectureTestable.InputType (p := q)
  strategy := ConjectureTestable.strategy (p := q)
  test := fun input =>
    if decide p then ConjectureTestable.test (p := q) input else true
  repr := ConjectureTestable.repr (p := q)

end Plausible.Conjecture
