/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
import Lean.Elab.Tactic.Config
import Plausible.Sampleable
import Plausible.Testable
open Lean

/-!
# `MetaTestable` Class

MetaTestable propositions have a procedure that can generate counter-examples
together with a proof that they invalidate the proposition.

This is a port of the Haskell QuickCheck library.

## Creating Customized Instances

The type classes `MetaTestable`, `SampleableExt` and `Shrinkable` are the
means by which `Plausible` creates samples and tests them. For instance,
the proposition `∀ i j : Nat, i ≤ j` has a `MetaTestable` instance because `Nat`
is sampleable and `i ≤ j` is decidable. Once `Plausible` finds the `MetaTestable`
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
`MetaTestable.check <| ∀ a b : MyType, a.y ≤ b.x → a.x ≤ b.y`. Writing this
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

* `MetaTestable` class
* `MetaTestable.check`: a way to test a proposition using random examples

## References

* https://hackage.haskell.org/package/QuickCheck

-/

namespace Plausible

section Matching
open Lean Meta
/-!
# Matching propositions of specific forms
-/
def existsProp? (e: Expr) : MetaM (Option Expr × Option Expr) := do
  let u ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (mkSort u)
  let prop := mkSort levelZero
  let fmly ← mkArrow α prop
  let mvar ← mkFreshExprMVar (some fmly)
  let e' ←  mkAppM ``Exists #[mvar]
  if ← isDefEq e' e then
    return (← Lean.getExprMVarAssignment? mvar.mvarId!, ← Lean.getExprMVarAssignment? α.mvarId!)
  else
    return (none, none)

def orProp? (e: Expr) : MetaM (Option Expr × Option Expr) := do
  let prop := mkSort levelZero
  let α ← mkFreshExprMVar prop
  let β ← mkFreshExprMVar prop
  let e' ← mkAppM ``Or #[α, β]
  if ← isDefEq e' e then
    return (← Lean.getExprMVarAssignment? α.mvarId!, ← Lean.getExprMVarAssignment? β.mvarId!)
  else
    return (none, none)

def andProp? (e: Expr) : MetaM (Option Expr × Option Expr) := do
  let prop := mkSort levelZero
  let α ← mkFreshExprMVar prop
  let β ← mkFreshExprMVar prop
  let e' ← mkAppM ``And #[α, β]
  if ← isDefEq e' e then
    return (← Lean.getExprMVarAssignment? α.mvarId!, ← Lean.getExprMVarAssignment? β.mvarId!)
  else
    return (none, none)

#check mkFreshLevelMVar

def forallProp? (e: Expr) : MetaM (Option Expr × Option Expr) := do
  let u ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (mkSort u)
  let prop := mkSort levelZero
  let fmly ← mkArrow α prop
  let mvar ← mkFreshExprMVar (some fmly)
  let e' ← withLocalDeclD `x α fun x => do
    let y ← mkAppM' mvar #[x]
    mkForallFVars #[x] y
  if ← isDefEq e' e then
    return (← Lean.getExprMVarAssignment? mvar.mvarId!, ← Lean.getExprMVarAssignment? α.mvarId!)
  else
    return (none, none)

def impProp? (e: Expr) : MetaM (Option Expr × Option Expr) := do
  let prop := mkSort levelZero
  let α ← mkFreshExprMVar prop
  let β ← mkFreshExprMVar prop
  let e' ←  mkArrow α β
  if ← isDefEq e' e then
    return (← Lean.getExprMVarAssignment? α.mvarId!, ← Lean.getExprMVarAssignment? β.mvarId!)
  else
    return (none, none)

def eqlProp? (e: Expr): MetaM (Option (Expr × Expr × Expr)) := do
  let level ←  mkFreshLevelMVar
  let u := mkSort level
  let α ← mkFreshExprMVar u
  let a ← mkFreshExprMVar α
  let b ← mkFreshExprMVar α
  let e' ← mkAppM ``Eq #[a, b]
  if ← isDefEq e' e then
    let α? ← Lean.getExprMVarAssignment? α.mvarId!
    let a? ← Lean.getExprMVarAssignment? a.mvarId!
    let b? ← Lean.getExprMVarAssignment? b.mvarId!
    let triple : Option (Expr × Expr × Expr) := do
      let α ← α?
      let a ← a?
      let b ← b?
      return (α, a, b)
    return triple
  else
    return none

def equality? (e: Expr): MetaM (Option (Expr × Expr × Expr)) := do
  let level ←  mkFreshLevelMVar
  let u := mkSort level
  let α ← mkFreshExprMVar u
  let a ← mkFreshExprMVar α
  let b ← mkFreshExprMVar α
  let e' ← mkAppM ``Eq #[a, b]
  let c ← mkFreshExprMVar e'
  if ← isDefEq c e then
    let α? ← Lean.getExprMVarAssignment? α.mvarId!
    let a? ← Lean.getExprMVarAssignment? a.mvarId!
    let b? ← Lean.getExprMVarAssignment? b.mvarId!
    let triple : Option (Expr × Expr × Expr) := do
      let α ← α?
      let a ← a?
      let b ← b?
      return (α, a, b)
    return triple
  else
    return none
end Matching


/-- Result of trying to disprove `p` -/
inductive MetaTestResult (p : Prop) where
  /--
  Succeed when we find another example satisfying `p`.
  In `success h`, `h` is an optional proof of the proposition.
  Without the proof, all we know is that we found one example
  where `p` holds. With a proof, the one test was sufficient to
  prove that `p` holds and we do not need to keep finding examples.
  -/
  | success : Unit ⊕' p → MetaTestResult p
  /--
  Give up when a well-formed example cannot be generated.
  `gaveUp n` tells us that `n` invalid examples were tried.
  -/
  | gaveUp : Nat → MetaTestResult p
  /--
  There was a mismatch between `p` and the expression representing `p`
  -/
  | mismatch : String → MetaTestResult p
  /--
  A counter-example to `p`; the strings specify values for the relevant variables.
  `failure h vs n` also carries a proof that `p` does not hold. This way, we can
  guarantee that there will be no false positive. The last component, `n`,
  is the number of times that the counter-example was shrunk.
  -/
  | failure : ¬ p → Expr → List String → Nat → MetaTestResult p
  deriving Inhabited


/-- `MetaTestable p` uses random examples to try to disprove `p`. -/
class MetaTestable (p : Prop) where
  run (cfg : Configuration) (minimize : Bool) (propExpr : Expr) :  Gen (MetaTestResult p)


namespace MetaTestResult

def toString : MetaTestResult p → String
  | success (PSum.inl _) => "success (no proof)"
  | success (PSum.inr _) => "success (proof)"
  | gaveUp n => s!"gave {n} times"
  | failure _ _ counters _ => s!"failed {counters}"
  | mismatch s => s!"Mismatch: {s}"

instance : ToString (MetaTestResult p) := ⟨toString⟩

/-- Applicative combinator proof carrying test results. -/
def combine {p q : Prop} : Unit ⊕' (p → q) → Unit ⊕' p → Unit ⊕' q
  | PSum.inr f, PSum.inr proof => PSum.inr <| f proof
  | _, _ => PSum.inl ()

/-- Combine the test result for properties `p` and `q` to create a test for their conjunction. -/
def and : MetaTestResult p → MetaTestResult q → MetaTestResult (p ∧ q)
  | failure h pf xs n, _ =>
    failure (fun h2 => h h2.left) pf xs n
  | _, failure h pf xs n => failure (fun h2 => h h2.right) pf  xs n
  | success h1, success h2 => success <| combine (combine (PSum.inr And.intro) h1) h2
  | gaveUp n, gaveUp m => gaveUp <| n + m
  | gaveUp n, _ => gaveUp n
  | _, gaveUp n => gaveUp n
  | mismatch s, _ => mismatch s
  | _, mismatch s => mismatch s

/-- Combine the test result for properties `p` and `q` to create a test for their disjunction. -/
def or : MetaTestResult p → MetaTestResult q → MetaTestResult (p ∨ q)
  | failure h1 pf1 xs n, failure h2 pf2 ys m =>
    let h3 := fun h =>
      match h with
      | Or.inl h3 => h1 h3
      | Or.inr h3 => h2 h3
    failure h3 pf1 (xs ++ ys) (n + m)
  | success h, _ => success <| combine (PSum.inr Or.inl) h
  | _, success h => success <| combine (PSum.inr Or.inr) h
  | gaveUp n, gaveUp m => gaveUp <| n + m
  | gaveUp n, _ => gaveUp n
  | _, gaveUp n => gaveUp n
  | mismatch s, _ => mismatch s
  | _, mismatch s => mismatch s

/-- If `q → p`, then `¬ p → ¬ q` which means that testing `p` can allow us
to find counter-examples to `q`. -/
def imp (h : q → p) (r : MetaTestResult p)
    (p : Unit ⊕' (p → q) := PSum.inl ()) : MetaTestResult q :=
  match r with
  | failure h2 pf xs n => failure (mt h h2) pf xs n
  | success h2 => success <| combine p h2
  | gaveUp n => gaveUp n
  | mismatch s => mismatch s

/-- Test `q` by testing `p` and proving the equivalence between the two. -/
def iff (h : q ↔ p) (r : MetaTestResult p) : MetaTestResult q :=
  imp h.mp r (PSum.inr h.mpr)

/-- When we assign a value to a universally quantified variable,
we record that value using this function so that our counter-examples
can be informative. -/
def addInfo (x : String) (h : q → p) (r : MetaTestResult p)
    (p : Unit ⊕' (p → q) := PSum.inl ()) : MetaTestResult q :=
  if let failure h2 pf xs n := r then
    failure (mt h h2) pf (x :: xs) n
  else
    imp h r p

/-- Add some formatting to the information recorded by `addInfo`. -/
def addVarInfo {γ : Type _} [Repr γ] (var : String) (x : γ) (h : q → p) (r : MetaTestResult p)
    (p : Unit ⊕' (p → q) := PSum.inl ()) : MetaTestResult q :=
  addInfo s!"{var} := {repr x}" h r p

def isFailure : MetaTestResult p → Bool
  | failure .. => true
  | _ => false

end MetaTestResult


namespace MetaTestable

open MetaTestResult

def runProp (p : Prop) [MetaTestable p] : Configuration → Bool → Expr → Gen (MetaTestResult p) := MetaTestable.run

/-- A `dbgTrace` with special formatting -/
def slimTrace {m : Type → Type _} [Pure m] (s : String) : m PUnit :=
  dbgTrace s!"[Plausible: {s}]" (fun _ => pure ())

instance andTestable [MetaTestable p] [MetaTestable q] : MetaTestable (p ∧ q) where
  run := fun cfg min e => do
  -- let pair ← andProp? e
  -- match ← andProp? e with
  -- | (some e₁, some e₂) => do
    let xp ← runProp p cfg min e
    let xq ← runProp q cfg min e
    return and xp xq
  -- | _ => return sorry

instance orTestable [MetaTestable p] [MetaTestable q] : MetaTestable (p ∨ q) where
  run := fun cfg min e => do
    let xp ← runProp p cfg min e
    -- As a little performance optimization we can just not run the second
    -- test if the first succeeds
    match xp with
    | success (PSum.inl h) => return success (PSum.inl h)
    | success (PSum.inr h) => return success (PSum.inr <| Or.inl h)
    | _ =>
      let xq ← runProp q cfg min e
      return or xp xq

instance iffTestable [MetaTestable ((p ∧ q) ∨ (¬ p ∧ ¬ q))] : MetaTestable (p ↔ q) where
  run := fun cfg min e => do
    let h ← runProp ((p ∧ q) ∨ (¬ p ∧ ¬ q)) cfg min e
    have := by
      constructor
      · intro h
        simp [h, Classical.em]
      · intro h
        rcases h with ⟨hleft, hright⟩ | ⟨hleft, hright⟩ <;> simp [hleft, hright]
    return iff this h

variable {var : String}

instance decGuardTestable [PrintableProp p] [Decidable p] {β : p → Prop} [∀ h, MetaTestable (β h)] :
    MetaTestable (NamedBinder var <| ∀ h, β h) where
  run := fun cfg min e => do
    if h : p then
      let res := runProp (β h) cfg min e
      let s := printProp p
      (fun r => addInfo s!"guard: {s}" (· <| h) r (PSum.inr <| fun q _ => q)) <$> res
    else if cfg.traceDiscarded || cfg.traceSuccesses then
      let res := fun _ => return gaveUp 1
      let s := printProp p
      slimTrace s!"discard: Guard {s} does not hold"; res
    else
      return gaveUp 1

instance forallTypesTestable {f : Type → Prop} [MetaTestable (f Int)] :
    MetaTestable (NamedBinder var <| ∀ x, f x) where
  run := fun cfg min e => do
    let r ← runProp (f Int) cfg min e
    return addVarInfo var "Int" (· <| Int) r

-- TODO: only in mathlib: @[pp_with_univ]
instance (priority := 100) forallTypesULiftTestable.{u}
    {f : Type u → Prop} [MetaTestable (f (ULift.{u} Int))] :
    MetaTestable (NamedBinder var <| ∀ x, f x) where
  run cfg min e := do
    let r ← runProp (f (ULift Int)) cfg min e
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
def addShrinks (n : Nat) : MetaTestResult p → MetaTestResult p
  | MetaTestResult.failure p pf xs m => MetaTestResult.failure p pf xs (m + n)
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
partial def minimizeAux [SampleableExt α] {β : α → Prop} [∀ x, MetaTestable (β x)] (cfg : Configuration)
    (var : String) (x : SampleableExt.proxy α) (n : Nat) :
    OptionT Gen (Σ x, MetaTestResult (β (SampleableExt.interp x))) := do
  let candidates := SampleableExt.shrink.shrink x
  if cfg.traceShrinkCandidates then
    slimTrace s!"Candidates for {var} := {repr x}:\n  {repr candidates}"
  for candidate in candidates do
    if cfg.traceShrinkCandidates then
      slimTrace s!"Trying {var} := {repr candidate}"
    let res ← OptionT.lift <| MetaTestable.runProp (β (SampleableExt.interp candidate)) cfg true sorry
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
def minimize [SampleableExt α] {β : α → Prop} [∀ x, MetaTestable (β x)] (cfg : Configuration)
    (var : String) (x : SampleableExt.proxy α) (r : MetaTestResult (β <| SampleableExt.interp x)) :
    Gen (Σ x, MetaTestResult (β <| SampleableExt.interp x)) := do
  if cfg.traceShrink then
     slimTrace "Shrink"
     slimTrace s!"Attempting to shrink {var} := {repr x}"
  let res ← OptionT.run <| minimizeAux cfg var x 0
  return res.getD ⟨x, r⟩

/-- Test a universal property by creating a sample of the right type and instantiating the
bound variable with it. -/
instance varTestable [SampleableExt α] {β : α → Prop} [∀ x, MetaTestable (β x)] :
    MetaTestable (NamedBinder var <| ∀ x : α, β x) where
  run := fun cfg min e => do
    let x ← SampleableExt.sample
    if cfg.traceSuccesses || cfg.traceDiscarded then
      slimTrace s!"{var} := {repr x}"
    let r ← MetaTestable.runProp (β <| SampleableExt.interp x) cfg false e
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
instance propVarTestable {β : Prop → Prop} [∀ b : Bool, MetaTestable (β b)] :
  MetaTestable (NamedBinder var <| ∀ p : Prop, β p)
where
  run := fun cfg min e =>
    imp (fun h (b : Bool) => h b) <$> MetaTestable.runProp (NamedBinder var <| ∀ b : Bool, β b) cfg min e

instance (priority := high) unusedVarTestable {β : Prop} [Nonempty α] [MetaTestable β] :
  MetaTestable (NamedBinder var (α → β))
where
  run := fun cfg min e => do
    if cfg.traceDiscarded || cfg.traceSuccesses then
      slimTrace s!"{var} is unused"
    let r ← MetaTestable.runProp β cfg min e
    let finalR := addInfo s!"{var} is irrelevant (unused)" id r
    return imp (· <| Classical.ofNonempty) finalR (PSum.inr <| fun x _ => x)

instance (priority := 2000) subtypeVarTestable {p : α → Prop} {β : α → Prop}
    [∀ x, PrintableProp (p x)]
    [∀ x, MetaTestable (β x)]
    [SampleableExt (Subtype p)] {var'} :
    MetaTestable (NamedBinder var <| (x : α) → NamedBinder var' <| p x → β x) where
  run cfg min e :=
    letI (x : Subtype p) : MetaTestable (β x) :=
      { run := fun cfg min e => do
          let r ← MetaTestable.runProp (β x.val) cfg min e
          return addInfo s!"guard: {printProp (p x)} (by construction)" id r (PSum.inr id) }
    do
      let r ← @MetaTestable.run (∀ x : Subtype p, β x.val) (@varTestable var _ _ _ _) cfg min e
      have := by simp [Subtype.forall, NamedBinder]
      return iff this r

instance (priority := low) decidableTestable {p : Prop} [PrintableProp p] [Decidable p] :
    MetaTestable p where
  run := fun _ _ _ =>
    if h : p then
      return success (PSum.inr h)
    else
      let s := printProp p
      return failure h sorry [s!"issue: {s} does not hold"] 0

end MetaTestable

#check PrintableProp


section IO
open MetaTestResult

namespace MetaTestable
/-- Execute `cmd` and repeat every time the result is `gaveUp` (at most `n` times). -/
def retry (cmd : Rand (MetaTestResult p)) : Nat → Rand (MetaTestResult p)
  | 0 => return MetaTestResult.gaveUp 1
  | n+1 => do
    let r ← cmd
    match r with
    | .success hp => return success hp
    | .failure h pf xs n => return failure h pf xs n
    | .gaveUp _ => retry cmd n
    | .mismatch s => return .mismatch s

/-- Count the number of times the test procedure gave up. -/
def giveUp (x : Nat) : MetaTestResult p → MetaTestResult p
  | success (PSum.inl ()) => gaveUp x
  | success (PSum.inr p) => success <| (PSum.inr p)
  | gaveUp n => gaveUp <| n + x
  | MetaTestResult.failure h pf xs n => failure h pf xs n
  | mismatch _ => gaveUp x

end MetaTestable

/-- Try `n` times to find a counter-example for `p`. -/
def MetaTestable.runSuiteAux (p : Prop) [MetaTestable p] (cfg : Configuration) :
    MetaTestResult p → Nat → Rand (MetaTestResult p)
  | r, 0 => return r
  | r, n+1 => do
    let size := (cfg.numInst - n - 1) * cfg.maxSize / cfg.numInst
    if cfg.traceSuccesses then
      slimTrace s!"New sample"
      slimTrace s!"Retrying up to {cfg.numRetries} times until guards hold"
    let x ← retry (ReaderT.run (MetaTestable.runProp p cfg true sorry) ⟨size⟩) cfg.numRetries
    match x with
    | success (PSum.inl ()) => runSuiteAux p cfg r n
    | gaveUp g => runSuiteAux p cfg (giveUp g r) n
    | _ => return x

/-- Try to find a counter-example of `p`. -/
def MetaTestable.runSuite (p : Prop) [MetaTestable p] (cfg : Configuration := {}) : Rand (MetaTestResult p) :=
  MetaTestable.runSuiteAux p cfg (success <| PSum.inl ()) cfg.numInst

/-- Run a test suite for `p` in `BaseIO` using the global RNG in `stdGenRef`. -/
def MetaTestable.checkIO (p : Prop) [MetaTestable p] (cfg : Configuration := {}) : BaseIO (MetaTestResult p) :=
  letI : MonadLift Id BaseIO := ⟨fun f => return Id.run f⟩
  match cfg.randomSeed with
  | none => runRand (MetaTestable.runSuite p cfg)
  | some seed => runRandWith seed (MetaTestable.runSuite p cfg)

end IO

open Decorations in
/-- Run a test suite for `p` and throw an exception if `p` does not hold. -/
def MetaTestable.check (p : Prop) (cfg : Configuration := {})
    (p' : Decorations.DecorationsOf p := by mk_decorations) [MetaTestable p'] : Lean.CoreM PUnit := do
  match ← MetaTestable.checkIO p' cfg with
  | MetaTestResult.success _ => if !cfg.quiet then Lean.logInfo "Unable to find a counter-example"
  | MetaTestResult.gaveUp n =>
    if !cfg.quiet then
      let msg := s!"Gave up after failing to generate values that fulfill the preconditions {n} times."
      Lean.logWarning msg
  | MetaTestResult.mismatch s =>
    if !cfg.quiet then
      let msg := s!"Mismatch: {s}"
      Lean.logWarning msg
  | MetaTestResult.failure _ _ xs n =>
    let msg := "Found a counter-example!"
    if cfg.quiet then
      Lean.throwError msg
    else
      Lean.throwError <| formatFailure msg xs n

-- #eval MetaTestable.check (∀ (x y z a : Nat) (h1 : 3 < x) (h2 : 3 < y), x - y = y - x)
--   Configuration.verbose
-- #eval MetaTestable.check (∀ x : Nat, ∀ y : Nat, x + y = y + x) Configuration.verbose
-- #eval MetaTestable.check (∀ (x : (Nat × Nat)), x.fst - x.snd - 10 = x.snd - x.fst - 10)
--   Configuration.verbose
-- #eval MetaTestable.check (∀ (x : Nat) (h : 10 < x), 5 < x) Configuration.verbose

macro tk:"#test " e:term : command => `(command| #eval%$tk MetaTestable.check $e)

-- #test ∀ (x : Nat) (h : 5 < x), 10 < x
-- #test ∀ (x : Nat) (h : 10 < x), 5 < x

end Plausible