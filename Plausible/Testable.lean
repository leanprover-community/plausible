/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
import Lean.Elab.Tactic.Config
import Plausible.Sampleable
import Batteries


/-!
# `Testable` Class

Testable propositions have a procedure that can generate counter-examples
together with a proof that they invalidate the proposition.

This is a port of the Haskell QuickCheck library.

## Creating Customized Instances

The type classes `Testable`, `SampleableExt` and `Shrinkable` are the
means by which `Plausible` creates samples and tests them. For instance,
the proposition `∀ i j : Nat, i ≤ j` has a `Testable` instance because `Nat`
is sampleable and `i ≤ j` is decidable. Once `Plausible` finds the `Testable`
instance, it can start using the instance to repeatedly creating samples
and checking whether they satisfy the property. Once it has found a
counter-example it will then use a `Shrinkable` instance to reduce the
example. This allows the user to create new instances and apply
`Plausible` to new situations.

### What do I do if I'm testing a property about my newly defined type?

Let us consider a type made for a new formalization:

```lean
structure MyType where
  x : Nat
  y : Nat
  h : x ≤ y
  deriving Repr
```

How do we test a property about `MyType`? For instance, let us consider
`Testable.check <| ∀ a b : MyType, a.y ≤ b.x → a.x ≤ b.y`. Writing this
property as is will give us an error because we do not have an instance
of `Shrinkable MyType` and `SampleableExt MyType`. We can define one as follows:

```lean
instance : Shrinkable MyType where
  shrink := fun ⟨x, y, _⟩ =>
    let proxy := Shrinkable.shrink (x, y - x)
    proxy.map (fun (fst, snd) => ⟨fst, fst + snd, by omega⟩)

instance : SampleableExt MyType :=
  SampleableExt.mkSelfContained do
    let x ← SampleableExt.interpSample Nat
    let xyDiff ← SampleableExt.interpSample Nat
    return ⟨x, x + xyDiff, by omega⟩
```

Again, we take advantage of the fact that other types have useful
`Shrinkable` implementations, in this case `Prod`.

## Main definitions

* `Testable` class
* `Testable.check`: a way to test a proposition using random examples

## References

* https://hackage.haskell.org/package/QuickCheck

-/

namespace Plausible

/-- Result of trying to disprove `p` -/
inductive TestResult (p : Prop) where
  /--
  Succeed when we find another example satisfying `p`.
  In `success h`, `h` is an optional proof of the proposition.
  Without the proof, all we know is that we found one example
  where `p` holds. With a proof, the one test was sufficient to
  prove that `p` holds and we do not need to keep finding examples.
  -/
  | success : Unit ⊕' p → TestResult p
  /--
  Give up when a well-formed example cannot be generated.
  `gaveUp n` tells us that `n` invalid examples were tried.
  -/
  | gaveUp : Nat → TestResult p
  /--
  A counter-example to `p`; the strings specify values for the relevant variables.
  `failure h vs n` also carries a proof that `p` does not hold. This way, we can
  guarantee that there will be no false positive. The last component, `n`,
  is the number of times that the counter-example was shrunk.
  -/
  | failure : ¬ p → List String → Nat → TestResult p
  deriving Inhabited

/-- Configuration for testing a property. -/
structure Configuration where
  /--
  How many test instances to generate.
  -/
  numInst : Nat := 100
  /--
  The maximum size of the values to generate.
  -/
  maxSize : Nat := 100
  numRetries : Nat := 10
  /--
  Enable tracing of values that didn't fulfill preconditions and were thus discarded.
  -/
  traceDiscarded : Bool := false
  /--
  Enable tracing of values that fulfilled the property and were thus discarded.
  -/
  traceSuccesses : Bool := false
  /--
  Enable basic tracing of shrinking.
  -/
  traceShrink : Bool := false
  /--
  Enable tracing of all attempted values during shrinking.
  -/
  traceShrinkCandidates : Bool := false
  /--
  Hard code the seed to use for the RNG
  -/
  randomSeed : Option Nat := none
  /--
  Disable output.
  -/
  quiet : Bool := false
  deriving Inhabited

open Lean in
instance : ToExpr Configuration where
  toTypeExpr := mkConst `Configuration
  toExpr cfg := mkApp9 (mkConst ``Configuration.mk)
    (toExpr cfg.numInst) (toExpr cfg.maxSize) (toExpr cfg.numRetries) (toExpr cfg.traceDiscarded)
    (toExpr cfg.traceSuccesses) (toExpr cfg.traceShrink) (toExpr cfg.traceShrinkCandidates)
    (toExpr cfg.randomSeed) (toExpr cfg.quiet)

/--
Allow elaboration of `Configuration` arguments to tactics.
-/
declare_config_elab elabConfig Configuration

/--
`PrintableProp p` allows one to print a proposition so that
`Plausible` can indicate how values relate to each other.
It's basically a poor man's delaborator.
-/
class PrintableProp (p : Prop) where
  printProp : String

export PrintableProp (printProp)

variable {p q : Prop}

instance (priority := low) : PrintableProp p where
  printProp := "⋯"

/-- `Testable p` uses random examples to try to disprove `p`. -/
class Testable (p : Prop) where
  run (cfg : Configuration) (minimize : Bool) : Gen (TestResult p)

def NamedBinder (_n : String) (p : Prop) : Prop := p

namespace TestResult

def toString : TestResult p → String
  | success (PSum.inl _) => "success (no proof)"
  | success (PSum.inr _) => "success (proof)"
  | gaveUp n => s!"gave {n} times"
  | failure _ counters _ => s!"failed {counters}"

instance : ToString (TestResult p) := ⟨toString⟩

/-- Applicative combinator proof carrying test results. -/
def combine {p q : Prop} : Unit ⊕' (p → q) → Unit ⊕' p → Unit ⊕' q
  | PSum.inr f, PSum.inr proof => PSum.inr <| f proof
  | _, _ => PSum.inl ()

/-- Combine the test result for properties `p` and `q` to create a test for their conjunction. -/
def and : TestResult p → TestResult q → TestResult (p ∧ q)
  | failure h xs n, _ => failure (fun h2 => h h2.left) xs n
  | _, failure h xs n => failure (fun h2 => h h2.right) xs n
  | success h1, success h2 => success <| combine (combine (PSum.inr And.intro) h1) h2
  | gaveUp n, gaveUp m => gaveUp <| n + m
  | gaveUp n, _ => gaveUp n
  | _, gaveUp n => gaveUp n

/-- Combine the test result for properties `p` and `q` to create a test for their disjunction. -/
def or : TestResult p → TestResult q → TestResult (p ∨ q)
  | failure h1 xs n, failure h2 ys m =>
    let h3 := fun h =>
      match h with
      | Or.inl h3 => h1 h3
      | Or.inr h3 => h2 h3
    failure h3 (xs ++ ys) (n + m)
  | success h, _ => success <| combine (PSum.inr Or.inl) h
  | _, success h => success <| combine (PSum.inr Or.inr) h
  | gaveUp n, gaveUp m => gaveUp <| n + m
  | gaveUp n, _ => gaveUp n
  | _, gaveUp n => gaveUp n

/-- If `q → p`, then `¬ p → ¬ q` which means that testing `p` can allow us
to find counter-examples to `q`. -/
def imp (h : q → p) (r : TestResult p)
    (p : Unit ⊕' (p → q) := PSum.inl ()) : TestResult q :=
  match r with
  | failure h2 xs n => failure (mt h h2) xs n
  | success h2 => success <| combine p h2
  | gaveUp n => gaveUp n

/-- Test `q` by testing `p` and proving the equivalence between the two. -/
def iff (h : q ↔ p) (r : TestResult p) : TestResult q :=
  imp h.mp r (PSum.inr h.mpr)

/-- When we assign a value to a universally quantified variable,
we record that value using this function so that our counter-examples
can be informative. -/
def addInfo (x : String) (h : q → p) (r : TestResult p)
    (p : Unit ⊕' (p → q) := PSum.inl ()) : TestResult q :=
  if let failure h2 xs n := r then
    failure (mt h h2) (x :: xs) n
  else
    imp h r p

/-- Add some formatting to the information recorded by `addInfo`. -/
def addVarInfo {γ : Type _} [Repr γ] (var : String) (x : γ) (h : q → p) (r : TestResult p)
    (p : Unit ⊕' (p → q) := PSum.inl ()) : TestResult q :=
  addInfo s!"{var} := {repr x}" h r p

def isFailure : TestResult p → Bool
  | failure _ _ _ => true
  | _ => false

end TestResult

namespace Configuration

/-- A configuration with all the trace options enabled, useful for debugging. -/
def verbose : Configuration where
  traceDiscarded := true
  traceSuccesses := true
  traceShrink := true
  traceShrinkCandidates := true

end Configuration

namespace Testable

open TestResult

def runProp (p : Prop) [Testable p] : Configuration → Bool → Gen (TestResult p) := Testable.run

/-- A `dbgTrace` with special formatting -/
def slimTrace {m : Type → Type _} [Pure m] (s : String) : m PUnit :=
  dbgTrace s!"[Plausible: {s}]" (fun _ => pure ())

instance andTestable [Testable p] [Testable q] : Testable (p ∧ q) where
  run := fun cfg min => do
    let xp ← runProp p cfg min
    let xq ← runProp q cfg min
    return and xp xq

instance orTestable [Testable p] [Testable q] : Testable (p ∨ q) where
  run := fun cfg min => do
    let xp ← runProp p cfg min
    -- As a little performance optimization we can just not run the second
    -- test if the first succeeds
    match xp with
    | success (PSum.inl h) => return success (PSum.inl h)
    | success (PSum.inr h) => return success (PSum.inr <| Or.inl h)
    | _ =>
      let xq ← runProp q cfg min
      return or xp xq

instance iffTestable [Testable ((p ∧ q) ∨ (¬ p ∧ ¬ q))] : Testable (p ↔ q) where
  run := fun cfg min => do
    let h ← runProp ((p ∧ q) ∨ (¬ p ∧ ¬ q)) cfg min
    have := by
      constructor
      · intro h
        simp [h, Classical.em]
      · intro h
        rcases h with ⟨hleft, hright⟩ | ⟨hleft, hright⟩ <;> simp [hleft, hright]
    return iff this h

variable {var : String}

instance decGuardTestable [PrintableProp p] [Decidable p] {β : p → Prop} [∀ h, Testable (β h)] :
    Testable (NamedBinder var <| ∀ h, β h) where
  run := fun cfg min => do
    if h : p then
      let res := runProp (β h) cfg min
      let s := printProp p
      (fun r => addInfo s!"guard: {s}" (· <| h) r (PSum.inr <| fun q _ => q)) <$> res
    else if cfg.traceDiscarded || cfg.traceSuccesses then
      let res := fun _ => return gaveUp 1
      let s := printProp p
      slimTrace s!"discard: Guard {s} does not hold"; res
    else
      return gaveUp 1

instance forallTypesTestable {f : Type → Prop} [Testable (f Int)] :
    Testable (NamedBinder var <| ∀ x, f x) where
  run := fun cfg min => do
    let r ← runProp (f Int) cfg min
    return addVarInfo var "Int" (· <| Int) r

-- TODO: only in mathlib: @[pp_with_univ]
instance (priority := 100) forallTypesULiftTestable.{u}
    {f : Type u → Prop} [Testable (f (ULift.{u} Int))] :
    Testable (NamedBinder var <| ∀ x, f x) where
  run cfg min := do
    let r ← runProp (f (ULift Int)) cfg min
    pure <| addVarInfo var "ULift Int" (· <| ULift Int) r

/--
Format the counter-examples found in a test failure.
-/
def formatFailure (s : String) (xs : List String) (n : Nat) : String :=
  let counter := String.intercalate "\n" xs
  let parts := [
    "\n===================",
    s,
    counter,
    s!"({n} shrinks)",
    "-------------------"
  ]
  String.intercalate "\n" parts

/--
Increase the number of shrinking steps in a test result.
-/
def addShrinks (n : Nat) : TestResult p → TestResult p
  | TestResult.failure p xs m => TestResult.failure p xs (m + n)
  | p => p

universe u in
instance {α : Type u} {m : Type u → Type _} [Pure m] : Inhabited (OptionT m α) :=
  ⟨(pure none : m (Option α))⟩

variable {α : Sort _}

/-- Shrink a counter-example `x` by using `Shrinkable.shrink x`, picking the first
candidate that falsifies a property and recursively shrinking that one.
The process is guaranteed to terminate because `shrink x` produces
a proof that all the values it produces are smaller (according to `SizeOf`)
than `x`. -/
partial def minimizeAux [SampleableExt α] {β : α → Prop} [∀ x, Testable (β x)] (cfg : Configuration)
    (var : String) (x : SampleableExt.proxy α) (n : Nat) :
    OptionT Gen (Σ x, TestResult (β (SampleableExt.interp x))) := do
  let candidates := SampleableExt.shrink.shrink x
  if cfg.traceShrinkCandidates then
    slimTrace s!"Candidates for {var} := {repr x}:\n  {repr candidates}"
  for candidate in candidates do
    if cfg.traceShrinkCandidates then
      slimTrace s!"Trying {var} := {repr candidate}"
    let res ← OptionT.lift <| Testable.runProp (β (SampleableExt.interp candidate)) cfg true
    if res.isFailure then
      if cfg.traceShrink then
        slimTrace s!"{var} shrunk to {repr candidate} from {repr x}"
      let currentStep := OptionT.lift <| return Sigma.mk candidate (addShrinks (n + 1) res)
      let nextStep := minimizeAux cfg var candidate (n + 1)
      return ← (nextStep <|> currentStep)
  if cfg.traceShrink then
    slimTrace s!"No shrinking possible for {var} := {repr x}"
  failure

/-- Once a property fails to hold on an example, look for smaller counter-examples
to show the user. -/
def minimize [SampleableExt α] {β : α → Prop} [∀ x, Testable (β x)] (cfg : Configuration)
    (var : String) (x : SampleableExt.proxy α) (r : TestResult (β <| SampleableExt.interp x)) :
    Gen (Σ x, TestResult (β <| SampleableExt.interp x)) := do
  if cfg.traceShrink then
     slimTrace "Shrink"
     slimTrace s!"Attempting to shrink {var} := {repr x}"
  let res ← OptionT.run <| minimizeAux cfg var x 0
  return res.getD ⟨x, r⟩

/-- Test a universal property by creating a sample of the right type and instantiating the
bound variable with it. -/
instance varTestable [SampleableExt α] {β : α → Prop} [∀ x, Testable (β x)] :
    Testable (NamedBinder var <| ∀ x : α, β x) where
  run := fun cfg min => do
    let x ← SampleableExt.sample
    if cfg.traceSuccesses || cfg.traceDiscarded then
      slimTrace s!"{var} := {repr x}"
    let r ← Testable.runProp (β <| SampleableExt.interp x) cfg false
    let ⟨finalX, finalR⟩ ←
      if isFailure r then
        if cfg.traceSuccesses then
          slimTrace s!"{var} := {repr x} is a failure"
        if min then
          minimize cfg var x r
        else
          pure ⟨x, r⟩
      else
        pure ⟨x, r⟩
    return addVarInfo var finalX (· <| SampleableExt.interp finalX) finalR

/-- Test a universal property about propositions -/
instance propVarTestable {β : Prop → Prop} [∀ b : Bool, Testable (β b)] :
  Testable (NamedBinder var <| ∀ p : Prop, β p)
where
  run := fun cfg min =>
    imp (fun h (b : Bool) => h b) <$> Testable.runProp (NamedBinder var <| ∀ b : Bool, β b) cfg min

instance (priority := high) unusedVarTestable {β : Prop} [Nonempty α] [Testable β] :
  Testable (NamedBinder var (α → β))
where
  run := fun cfg min => do
    if cfg.traceDiscarded || cfg.traceSuccesses then
      slimTrace s!"{var} is unused"
    let r ← Testable.runProp β cfg min
    let finalR := addInfo s!"{var} is irrelevant (unused)" id r
    return imp (· <| Classical.ofNonempty) finalR (PSum.inr <| fun x _ => x)

instance (priority := 2000) subtypeVarTestable {p : α → Prop} {β : α → Prop}
    [∀ x, PrintableProp (p x)]
    [∀ x, Testable (β x)]
    [SampleableExt (Subtype p)] {var'} :
    Testable (NamedBinder var <| (x : α) → NamedBinder var' <| p x → β x) where
  run cfg min :=
    letI (x : Subtype p) : Testable (β x) :=
      { run := fun cfg min => do
          let r ← Testable.runProp (β x.val) cfg min
          return addInfo s!"guard: {printProp (p x)} (by construction)" id r (PSum.inr id) }
    do
      let r ← @Testable.run (∀ x : Subtype p, β x.val) (@varTestable var _ _ _ _) cfg min
      have := by simp [Subtype.forall, NamedBinder]
      return iff this r

instance (priority := low) decidableTestable {p : Prop} [PrintableProp p] [Decidable p] :
    Testable p where
  run := fun _ _ =>
    if h : p then
      return success (PSum.inr h)
    else
      let s := printProp p
      return failure h [s!"issue: {s} does not hold"] 0

end Testable

section PrintableProp

variable {α : Type _}

instance Eq.printableProp [Repr α] {x y : α} : PrintableProp (x = y) where
  printProp := s!"{repr x} = {repr y}"

instance Ne.printableProp [Repr α] {x y : α} : PrintableProp (x ≠ y) where
  printProp := s!"{repr x} ≠ {repr y}"

instance LE.printableProp [Repr α] [LE α] {x y : α} : PrintableProp (x ≤ y) where
  printProp := s!"{repr x} ≤ {repr y}"

instance LT.printableProp [Repr α] [LT α] {x y : α} : PrintableProp (x < y) where
  printProp := s!"{repr x} < {repr y}"

variable {x y : Prop}

instance And.printableProp [PrintableProp x] [PrintableProp y] : PrintableProp (x ∧ y) where
  printProp := s!"{printProp x} ∧ {printProp y}"

instance Or.printableProp [PrintableProp x] [PrintableProp y] : PrintableProp (x ∨ y) where
  printProp := s!"{printProp x} ∨ {printProp y}"

instance Iff.printableProp [PrintableProp x] [PrintableProp y] : PrintableProp (x ↔ y) where
  printProp := s!"{printProp x} ↔ {printProp y}"

instance Imp.printableProp [PrintableProp x] [PrintableProp y] : PrintableProp (x → y) where
  printProp := s!"{printProp x} → {printProp y}"

instance Not.printableProp [PrintableProp x] : PrintableProp (¬x) where
  printProp := s!"¬{printProp x}"

instance True.printableProp : PrintableProp True where
  printProp := "True"

instance False.printableProp : PrintableProp False where
  printProp := "False"

instance Bool.printableProp {b : Bool} : PrintableProp b where
  printProp := if b then "true" else "false"

end PrintableProp

section IO
open TestResult

/-- Execute `cmd` and repeat every time the result is `gaveUp` (at most `n` times). -/
def retry (cmd : Rand (TestResult p)) : Nat → Rand (TestResult p)
  | 0 => return TestResult.gaveUp 1
  | n+1 => do
    let r ← cmd
    match r with
    | .success hp => return success hp
    | .failure h xs n => return failure h xs n
    | .gaveUp _ => retry cmd n

/-- Count the number of times the test procedure gave up. -/
def giveUp (x : Nat) : TestResult p → TestResult p
  | success (PSum.inl ()) => gaveUp x
  | success (PSum.inr p) => success <| (PSum.inr p)
  | gaveUp n => gaveUp <| n + x
  | TestResult.failure h xs n => failure h xs n

/-- Try `n` times to find a counter-example for `p`. -/
def Testable.runSuiteAux (p : Prop) [Testable p] (cfg : Configuration) :
    TestResult p → Nat → Rand (TestResult p)
  | r, 0 => return r
  | r, n+1 => do
    let size := (cfg.numInst - n - 1) * cfg.maxSize / cfg.numInst
    if cfg.traceSuccesses then
      slimTrace s!"New sample"
      slimTrace s!"Retrying up to {cfg.numRetries} times until guards hold"
    let x ← retry (ReaderT.run (Testable.runProp p cfg true) ⟨size⟩) cfg.numRetries
    match x with
    | success (PSum.inl ()) => runSuiteAux p cfg r n
    | gaveUp g => runSuiteAux p cfg (giveUp g r) n
    | _ => return x

/-- Try to find a counter-example of `p`. -/
def Testable.runSuite (p : Prop) [Testable p] (cfg : Configuration := {}) : Rand (TestResult p) :=
  Testable.runSuiteAux p cfg (success <| PSum.inl ()) cfg.numInst

/-- Run a test suite for `p` in `BaseIO` using the global RNG in `stdGenRef`. -/
def Testable.checkIO (p : Prop) [Testable p] (cfg : Configuration := {}) : BaseIO (TestResult p) :=
  letI : MonadLift Id BaseIO := ⟨fun f => return Id.run f⟩
  match cfg.randomSeed with
  | none => runRand (Testable.runSuite p cfg)
  | some seed => runRandWith seed (Testable.runSuite p cfg)

end IO

namespace Decorations

open Lean

/-- Traverse the syntax of a proposition to find universal quantifiers
quantifiers and add `NamedBinder` annotations next to them. -/
partial def addDecorations (e : Expr) : MetaM Expr :=
  Meta.transform e fun expr => do
    if not (← Meta.inferType expr).isProp then
      return .done expr
    else if let Expr.forallE name type body data := expr then
      let newType ← addDecorations type
      let newBody ← Meta.withLocalDecl name data type fun fvar => do
        return (← addDecorations (body.instantiate1 fvar)).abstract #[fvar]
      let rest := Expr.forallE name newType newBody data
      return .done <| (← Meta.mkAppM `Plausible.NamedBinder #[mkStrLit name.toString, rest])
    else
      return .continue

/-- `DecorationsOf p` is used as a hint to `mk_decorations` to specify
that the goal should be satisfied with a proposition equivalent to `p`
with added annotations. -/
abbrev DecorationsOf (_p : Prop) := Prop

open Elab.Tactic
open Meta

/-- In a goal of the shape `⊢ DecorationsOf p`, `mk_decoration` examines
the syntax of `p` and adds `NamedBinder` around universal quantifications
to improve error messages. This tool can be used in the declaration of a
function as follows:
```lean
def foo (p : Prop) (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : ...
```
`p` is the parameter given by the user, `p'` is a definitionally equivalent
proposition where the quantifiers are annotated with `NamedBinder`.
-/
scoped elab "mk_decorations" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  if let .app (.const ``Decorations.DecorationsOf _) body := goalType then
    closeMainGoal `mk_decorations (← addDecorations body)

end Decorations

open Decorations in
/-- Run a test suite for `p` and throw an exception if `p` does not hold. -/
def Testable.check (p : Prop) (cfg : Configuration := {})
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : Lean.CoreM PUnit := do
  match ← Testable.checkIO p' cfg with
  | TestResult.success _ => if !cfg.quiet then Lean.logWarning "Unable to find a counter-example"
  | TestResult.gaveUp n =>
    if !cfg.quiet then
      let msg := s!"Gave up after failing to generate values that fulfill the preconditions {n} times."
      Lean.logWarning msg
  | TestResult.failure _ xs n =>
    let msg := "Found a counter-example!"
    if cfg.quiet then
      Lean.throwError msg
    else
      Lean.throwError <| formatFailure msg xs n

-- #eval Testable.check (∀ (x y z a : Nat) (h1 : 3 < x) (h2 : 3 < y), x - y = y - x)
--   Configuration.verbose
-- #eval Testable.check (∀ x : Nat, ∀ y : Nat, x + y = y + x) Configuration.verbose
-- #eval Testable.check (∀ (x : (Nat × Nat)), x.fst - x.snd - 10 = x.snd - x.fst - 10)
--   Configuration.verbose
-- #eval Testable.check (∀ (x : Nat) (h : 10 < x), 5 < x) Configuration.verbose

@[nolint docBlame]
macro tk:"#test " e:term : command => `(command| #eval%$tk Testable.check $e)

-- #test ∀ (x : Nat) (h : 5 < x), 10 < x
-- #test ∀ (x : Nat) (h : 10 < x), 5 < x

end Plausible
