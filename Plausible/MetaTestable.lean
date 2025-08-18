/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
import Lean.Meta
import Lean.Elab.Tactic.Config
import Plausible.Sampleable
import Plausible.Testable
import Plausible.MGen
open Lean

/-!
# `MetaTestable` Class

MetaTestable propositions have a procedure that can generate counter-examples together with a proof that they invalidate the proposition. This is a refinement of the `Testable` class.

Instances of `Testable` are built using `Sampleable` instances. For `MetaTestable` instances, we also need an expression for the proxy in a sampleable type, which is an additional requirement.

## Main definitions

* `MetaTestable` class
* `MetaTestable.check`: a way to test a proposition using random examples, givng a proof of the counter-example
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

def notProp? (e: Expr) : MetaM (Option Expr) := do
  let prop := mkSort levelZero
  let α ← mkFreshExprMVar prop
  let e' ← mkAppM ``Not #[α]
  if ← isDefEq e' e then
    return (← Lean.getExprMVarAssignment? α.mvarId!)
  else
    return none

def forallProp? (e: Expr) : MetaM (Option Expr × Option Expr) := do
  let u ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (mkSort u)
  let prop := mkSort levelZero
  let fmlyType ← mkArrow α prop
  let fmly ← mkFreshExprMVar (some fmlyType)
  let e' ← withLocalDeclD `x α fun x => do
    let y ← mkAppM' fmly #[x]
    mkForallFVars #[x] y
  if ← isDefEq e' e then
    return (← Lean.getExprMVarAssignment? fmly.mvarId!, ← Lean.getExprMVarAssignment? α.mvarId!)
  else
    return (none, none)

def forallPropProp? (e: Expr) : MetaM (Option Expr × Option Expr × Option Expr) := do
  let u ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (mkSort u)
  let prop := mkSort levelZero
  let fmlyType ← mkArrow α prop
  let fmly ← mkFreshExprMVar (some fmlyType)
  let p ← mkFreshExprMVar (some fmlyType)
  let e' ← withLocalDeclD `x α fun x => do
    let y ← mkAppM' fmly #[x]
    let y' ← mkAppM' p #[x]
    let cod ← mkArrow y' y
    mkForallFVars #[x] cod
  if ← isDefEq e' e then
    return (← Lean.getExprMVarAssignment? p.mvarId!, ← Lean.getExprMVarAssignment? fmly.mvarId!, ← Lean.getExprMVarAssignment? α.mvarId!)
  else
    return (none, none, none)

def impProp? (e: Expr) : MetaM (Option Expr × Option Expr) := do
  let u ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (mkSort u)
  let prop := mkSort levelZero
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

def iffProp? (e: Expr): MetaM (Option (Expr × Expr)) := do
  let prop := mkSort levelZero
  let α ← mkFreshExprMVar prop
  let β ← mkFreshExprMVar prop
  let e' ← mkAppM ``Iff #[α , β]
  if ← isDefEq e' e then
    let α? ← Lean.getExprMVarAssignment? α.mvarId!
    let β? ← Lean.getExprMVarAssignment? β.mvarId!
    let pair : Option (Expr × Expr) := do
      let α ← α?
      let β  ← β?
      return (α, β)
    return pair
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

open Lean Meta

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
  A counter-example to `p`; the strings specify values for the relevant variables.
  `failure h vs n` also carries a proof that `p` does not hold. This way, we can
  guarantee that there will be no false positive. The last component, `n`,
  is the number of times that the counter-example was shrunk.
  -/
  | failure : ¬ p → Option Expr → List String → Nat → MetaTestResult p
  deriving Inhabited


/-- `MetaTestable p` uses random examples to try to disprove `p`. -/
class MetaTestable (p : Prop) where
  runExpr (cfg : Configuration) (minimize : Bool) (propExpr? : Option Expr) :  MGen (MetaTestResult p)


namespace MetaTestResult

def toString : MetaTestResult p → String
  | success (PSum.inl _) => "success (no proof)"
  | success (PSum.inr _) => "success (proof)"
  | gaveUp n => s!"gave {n} times"
  | failure _ _ counters _ => s!"failed {counters}"

instance : ToString (MetaTestResult p) := ⟨toString⟩

/-- Applicative combinator proof carrying test results. -/
def combine {p q : Prop} : Unit ⊕' (p → q) → Unit ⊕' p → Unit ⊕' q
  | PSum.inr f, PSum.inr proof => PSum.inr <| f proof
  | _, _ => PSum.inl ()

def checkDisproof (pf prop: Expr) : MetaM Unit := do
  let negProp ← mkAppM ``Not #[prop]
  let pfType ← inferType pf
  unless ← isDefEq pfType negProp do
    throwError m!"Expected a proof of {negProp}, got proof of {← ppExpr pfType}"

/-- Combine the test result for properties `p` and `q` to create a test for their conjunction. -/
def and : MetaTestResult p → MetaTestResult q → Option Expr →  MetaM (MetaTestResult (p ∧ q))
  | failure h pf? xs n, _, e? => do
    let pf'? ←
    match e? with
    | none => pure none
    | some e =>
        let (some e₁, some e₂) ← andProp? e | throwError m!"Expected an `And` proposition, got {← ppExpr e}"
        pf?.mapM fun pf => withLocalDeclD `h e fun h => do
        let x ← mkAppOptM ``And.left #[e₁, e₂, h]
        let e' ←  mkAppM' pf #[x]
        mkLambdaFVars #[h] e'
      -- checkDisproof pf' e
    return failure (fun h2 => h h2.left) pf'? xs n
  | _, failure h pf? xs n, e? => do
    let pf' ←
      match e? with
      | none => pure none
      | some e =>
        let (some e₁, some e₂)  ← andProp? e | throwError m!"Expected an `And` proposition, got {← ppExpr e}"
        pf?.mapM fun pf => withLocalDeclD `h e fun h => do
          let x ← mkAppOptM ``And.right #[e₁, e₂, h]
          let e' ← mkAppM' pf #[x]
          mkLambdaFVars #[h] e'
      -- checkDisproof pf' e
    return failure (fun h2 => h h2.right) pf' xs n
  | success h1, success h2, _ =>
    return success <| combine (combine (PSum.inr And.intro) h1) h2
  | gaveUp n, gaveUp m, _ => return gaveUp <| n + m
  | gaveUp n, _, _ => return gaveUp n
  | _, gaveUp n, _ => return gaveUp n


/-- Combine the test result for properties `p` and `q` to create a test for their disjunction. -/
def or : MetaTestResult p → MetaTestResult q → Option Expr →  MetaM (MetaTestResult (p ∨ q))
  | failure h1 pf1 xs n, failure h2 pf2 ys m, e? => do
    let pf ←
      match e? with
      | none => pure none
      | some e =>
        let (some α, some β) ← orProp? e | throwError m!"Expected an `Or` proposition, got {← ppExpr e}"
        let motive ← withLocalDeclD `h e fun h => do
          mkLambdaFVars #[h] <| mkConst ``False
        mkAppOptM ``Or.rec #[α, β, motive, pf1, pf2]
    let h3 := fun h =>
      match h with
      | Or.inl h3 => h1 h3
      | Or.inr h3 => h2 h3
    -- checkDisproof pf e
    return failure h3 pf (xs ++ ys) (n + m)
  | success h, _, _ => return success <|  combine (PSum.inr Or.inl) h
  | _, success h, _ => return success <|  combine (PSum.inr Or.inr) h
  | gaveUp n, gaveUp m, _ => return gaveUp <| n + m
  | gaveUp n, _, _ => return gaveUp n
  | _, gaveUp n, _ => return gaveUp n

/-- If `q → p`, then `¬ p → ¬ q` which means that testing `p` can allow us
to find counter-examples to `q`. -/
def imp (h : q → p) (hExp?: Option Expr) (r : MetaTestResult p)
    (p : Unit ⊕' (p → q) := PSum.inl ()) : MetaM (MetaTestResult q) :=
  match r with
  | failure h2 pf? xs n => do
    let pf' ←
      hExp?.bindM fun hExp => pf?.mapM fun pf => mkAppM ``mt #[hExp, pf]
    return failure (mt h h2) pf' xs n
  | success h2 => return success <| combine p h2
  | gaveUp n => return gaveUp n

/-- Test `q` by testing `p` and proving the equivalence between the two. -/
def iff (h : q ↔ p) (hExp? : Option Expr) (r : MetaTestResult p) : MetaM (MetaTestResult q) := do
  let hExp' ← hExp?.mapM  fun hExp => mkAppM ``Iff.mp #[hExp]
  imp h.mp hExp' r (PSum.inr h.mpr)

/-- When we assign a value to a universally quantified variable,
we record that value using this function so that our counter-examples
can be informative. -/
def addInfo (x : String) (h : q → p) (hExp?: Option Expr) (r : MetaTestResult p)
    (p : Unit ⊕' (p → q) := PSum.inl ()) : (MetaM <| MetaTestResult q) := do
  if let failure h2 pf? xs n := r then
    let pf' ← hExp?.bindM fun hExp => pf?.mapM fun pf => mkAppM ``mt #[hExp, pf]
    return failure (mt h h2) pf' (x :: xs) n
  else
    imp h hExp? r p

/-- Add some formatting to the information recorded by `addInfo`. -/
def addVarInfo {γ : Type _} [Repr γ] (var : String) (x : γ) (h : q → p) (hExp: Option Expr) (r : MetaTestResult p)
    (p : Unit ⊕' (p → q) := PSum.inl ()) : MetaM (MetaTestResult q) := do
  addInfo s!"{var} := {repr x}" h (hExp: Option Expr) r p

def isFailure : MetaTestResult p → Bool
  | failure .. => true
  | _ => false

end MetaTestResult


namespace MetaTestable

open MetaTestResult


def runPropExpr (p : Prop) [MetaTestable p] : Configuration → Bool → Option Expr → MGen (MetaTestResult p) := fun cfg b e => do
  runExpr cfg b e

/-- A `dbgTrace` with special formatting -/
def slimTrace {m : Type → Type _} [Pure m] (s : String) : m PUnit :=
  dbgTrace s!"[Plausible: {s}]" (fun _ => pure ())


instance andTestable [MetaTestable p] [MetaTestable q] : MetaTestable (p ∧ q) where
  runExpr := fun cfg min e? => do
    let (e₁, e₂) ← match e? with
      | some e => do
        let (some e₁, some e₂) ← andProp? e | throwError m!"Expected an `And` proposition, got {← ppExpr e}"
        pure (some e₁, some e₂)
      | none => pure (none, none)
    let xp ← runPropExpr p cfg min e₁
    let xq ← runPropExpr q cfg min e₂
    and xp xq e?

instance orTestable [MetaTestable p] [MetaTestable q] : MetaTestable (p ∨ q) where
  runExpr := fun cfg min e? => do
    let (e₁, e₂) ← match e? with
      | some e => do
        let (some e₁, some e₂) ← orProp? e | throwError m!"Expected an `Or` proposition, got {← ppExpr e}"
        pure (some e₁, some e₂)
      | none => pure (none, none)
    let xp ← runPropExpr p cfg min e₁
    -- As a little performance optimization we can just not run the second
    -- test if the first succeeds
    match xp with
    | success (PSum.inl h) => return success (PSum.inl h)
    | success (PSum.inr h) => return success (PSum.inr <| Or.inl h)
    | _ =>
      let xq ← runPropExpr q cfg min e₂
      or xp xq e?

theorem iff_resolve (p q : Prop) : (p ↔ q) ↔ p ∧ q ∨ ¬p ∧ ¬q := by
  constructor
  · intro h
    simp [h, Classical.em]
  · intro h
    rcases h with ⟨hleft, hright⟩ | ⟨hleft, hright⟩ <;> simp [hleft, hright]

instance iffTestable [MetaTestable ((p ∧ q) ∨ (¬ p ∧ ¬ q))] : MetaTestable (p ↔ q) where
  runExpr := fun cfg min e? => do
    let hExp ←
      match e? with
      | none => pure none
      | some e => do
        let some (α, β) ← iffProp? e | throwError m!"Expected an `Iff` proposition, got {← ppExpr e}"
        mkAppM ``iff_resolve #[α, β]
    let h ← runPropExpr ((p ∧ q) ∨ (¬ p ∧ ¬ q)) cfg min e?
    iff (iff_resolve p q) hExp h

variable {var : String}

instance decGuardTestable [PrintableProp p] [Decidable p] {β : p → Prop} [∀ h, MetaTestable (β h)] :
    MetaTestable (NamedBinder var <| ∀ h, β h) where
  runExpr := fun cfg min e? => do
    if h : p then
    match e? with
    | none =>
      let res := runPropExpr (β h) cfg min none
      let s := printProp p
      ← (fun r => addInfo s!"guard: {s}" (· <| h) none r (PSum.inr <| fun q _ => q)) <$> res
    | some e =>
      let (some βExp, some pExp) ← forallProp? e | throwError m!"Expected a `Forall` proposition, got {← ppExpr e}"
      let h' := (· <| h)
      let yExp ←
        mkAppM' βExp #[pExp]
      let res := runPropExpr (β h) cfg min yExp
      let decInstType ← mkAppM ``Decidable #[pExp]
      let inst ← synthInstance decInstType
      let falseRefl ← mkAppM ``Eq.refl #[mkConst ``false]
      let pf ← mkAppOptM ``of_decide_eq_true #[pExp, inst, falseRefl]
      let cod := mkApp βExp pf
      let hExp ←
        withLocalDeclD `x (← mkArrow pExp cod) fun x => do
        let y ← mkAppM' x #[cod]
        mkLambdaFVars #[x] y
      let s := printProp p
      ← (fun r => addInfo s!"guard: {s}" h' hExp r (PSum.inr <| fun q _ => q)) <$> res
    else if cfg.traceDiscarded || cfg.traceSuccesses then
      let res := fun _ => return gaveUp 1
      let s := printProp p
      slimTrace s!"discard: Guard {s} does not hold"; res
    else
      return gaveUp 1

instance forallTypesTestable {f : Type → Prop} [MetaTestable (f Int)] :
    MetaTestable (NamedBinder var <| ∀ x, f x) where
  runExpr := fun cfg min e => do
    let r ← runPropExpr (f Int) cfg min e
    addVarInfo var "Int"  (· <| Int) e r

-- TODO: only in mathlib: @[pp_with_univ]
instance (priority := 100) forallTypesULiftTestable.{u}
    {f : Type u → Prop} [MetaTestable (f (ULift.{u} Int))] :
    MetaTestable (NamedBinder var <| ∀ x, f x) where
  runExpr cfg min e := do
    let r ← runPropExpr (f (ULift Int)) cfg min e
    addVarInfo var "ULift Int" (· <| ULift Int) e r

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
partial def minimizeAux [SampleableExt α]  {β : α → Prop} [∀ x, MetaTestable (β x)] (αExp? βExp?: Option Expr) (cfg : Configuration)
    (var : String) (x : SampleableExt.proxy α) (n : Nat) :
    OptionT MGen (Σ x, MetaTestResult (β (SampleableExt.interp x))) := do
  let candidates := SampleableExt.shrink.shrink x
  if cfg.traceShrinkCandidates then
    slimTrace s!"Candidates for {var} := {repr x}:\n  {repr candidates}"
  match αExp?, βExp?, getProxyExpr? α  with
  | some αExp, some βExpr, some _ =>
    for candidate in candidates do
      if cfg.traceShrinkCandidates then
        slimTrace s!"Trying {var} := {repr candidate}"
      let xExpr := toExpr candidate
      let .sort u := ← inferType αExp | throwError m!"Expected a sort, got {αExp}"
      let v ←  mkFreshLevelMVar
      let instType :=  mkApp (mkConst ``SampleableExt [u, v]) αExp
      let samp ← synthInstance instType
      let xInterp ← mkAppOptM ``SampleableExt.interp #[αExp, samp, xExpr]
      let e' ← mkAppM' βExpr #[xInterp]
      let res ← OptionT.lift <| runPropExpr (β (SampleableExt.interp candidate)) cfg true e'
      if res.isFailure then
        if cfg.traceShrink then
          slimTrace s!"{var} shrunk to {repr candidate} from {repr x}"
        let currentStep := OptionT.lift <| return Sigma.mk candidate (addShrinks (n + 1) res)
        let nextStep := minimizeAux αExp βExpr cfg var candidate (n + 1)
        return ← (nextStep <|> currentStep)
  | _, _, _ =>
    for candidate in candidates do
      if cfg.traceShrinkCandidates then
        slimTrace s!"Trying {var} := {repr candidate}"
      let res ← OptionT.lift <| runPropExpr (β (SampleableExt.interp candidate)) cfg true none
      if res.isFailure then
        if cfg.traceShrink then
          slimTrace s!"{var} shrunk to {repr candidate} from {repr x}"
        let currentStep := OptionT.lift <| return Sigma.mk candidate (addShrinks (n + 1) res)
        let nextStep := minimizeAux none none cfg var candidate (n + 1)
        return ← (nextStep <|> currentStep)
  if cfg.traceShrink then
    slimTrace s!"No shrinking possible for {var} := {repr x}"
  failure

/-- Once a property fails to hold on an example, look for smaller counter-examples
to show the user. -/
def minimize [SampleableExt α]  {β : α → Prop} [∀ x, MetaTestable (β x)] (αExp βExpr: Option Expr)(cfg : Configuration)
    (var : String) (x : SampleableExt.proxy α) (r : MetaTestResult (β <| SampleableExt.interp x)) :
    MGen (Σ x, MetaTestResult (β <| SampleableExt.interp x)) := do
  if cfg.traceShrink then
     slimTrace "Shrink"
     slimTrace s!"Attempting to shrink {var} := {repr x}"
  let res ← OptionT.run <| minimizeAux αExp βExpr cfg var x 0
  return res.getD ⟨x, r⟩

open Lean Meta Elab Term Tactic in
/-- Test a universal property by creating a sample of the right type and instantiating the
bound variable with it. -/
instance varTestable [SampleableExt α] {β : α → Prop} [∀ x, MetaTestable (β x)] :
    MetaTestable (NamedBinder var <| ∀ x : α, β x) where
  runExpr := fun cfg min e? => do
  match e? with
  | none =>
    let x ← SampleableExt.sample
    if cfg.traceSuccesses || cfg.traceDiscarded then
      slimTrace s!"{var} := {repr x}"
    let r ← runPropExpr (β <| SampleableExt.interp x) cfg false none
    let ⟨finalX, finalR⟩ ←
      if isFailure r then
        if cfg.traceSuccesses then
          slimTrace s!"{var} := {repr x} is a failure"
        if min then
          minimize none none cfg var x r
        else
          pure ⟨x, r⟩
      else
        pure ⟨x, r⟩
    let h := (· <| SampleableExt.interp finalX)
    addVarInfo var finalX h none finalR
  | some e =>
    let  (some βExp, some αExp) ← forallProp? e | throwError m!"Expected a `Forall` proposition, got {← ppExpr e}"
    let x ← SampleableExt.sample
    let e'? ← match getProxyExpr? α with
    | none => pure none
    | some inst =>
      let xExpr := toExpr x
      let αExp ← instantiateMVars αExp
      let .sort u := ← inferType αExp | throwError m!"Expected a sort, got {αExp}"
      let v ←  mkFreshLevelMVar
      let instType :=  mkApp (mkConst ``SampleableExt [u, v]) αExp
      let samp ← synthInstance instType
      let xInterp ← mkAppOptM ``SampleableExt.interp #[αExp, samp, xExpr]
      let e' ← mkAppM' βExp #[xInterp]
      -- let (e', _) ← dsimp e' {}
      pure (some e')
    if cfg.traceSuccesses || cfg.traceDiscarded then
      slimTrace s!"{var} := {repr x}"
    let r ← runPropExpr (β <| SampleableExt.interp x) cfg false e'?
    let ⟨finalX, finalR⟩ ←
      if isFailure r then
        if cfg.traceSuccesses then
          slimTrace s!"{var} := {repr x} is a failure"
        if min then
          minimize αExp βExp cfg var x r
        else
          pure ⟨x, r⟩
      else
        pure ⟨x, r⟩
    let hExpr? ← match getProxyExpr? α with
    | none => pure none
    | some inst =>
      let xExpr := toExpr finalX
      let .sort u ← inferType αExp | throwError m!"Expected a sort, got {αExp}"
      let v ←  mkFreshLevelMVar
      let instType :=  mkApp (mkConst ``SampleableExt [u, v]) αExp
      let samp ← synthInstance instType
      let xInterp ← mkAppOptM ``SampleableExt.interp #[αExp, samp, xExpr]
      let hExpr ← withLocalDeclD `x e fun x => do
        mkLambdaFVars #[x] (mkApp x xInterp)
      pure (some hExpr)
    let h := (· <| SampleableExt.interp finalX)
    addVarInfo var finalX h hExpr? finalR




theorem bool_to_prop_fmly (β : Prop → Prop): NamedBinder var (∀ (p : Prop), β p) → ∀ (b : Bool), β (b = true) := fun h b => h (b = true)

/-- Test a universal property about propositions -/
instance propVarTestable {β : Prop → Prop} [h: ∀ b : Bool, MetaTestable (β b)] :
  MetaTestable (NamedBinder var <| ∀ p : Prop, β p)
where
  runExpr := fun cfg min e? => do
    let p ←  runPropExpr (NamedBinder var <| ∀ b : Bool, β b) cfg min e?
    let e' ←
      match e? with
      | none => pure none
      | some e => do
        let (some βExpr, _) ← forallProp? e | throwError m!"Expected a `Forall` proposition, got {← ppExpr e}"
        let res ← mkAppM ``bool_to_prop_fmly #[βExpr]
        pure (some res)
    imp (bool_to_prop_fmly β) e' p

instance (priority := high) unusedVarTestable {β : Prop} [Nonempty α] [MetaTestable β] :
  MetaTestable (NamedBinder var (α → β))
where
  runExpr := fun cfg min e? => do
    if cfg.traceDiscarded || cfg.traceSuccesses then
      slimTrace s!"{var} is unused"
    match e? with
    | none =>
      let r ← runPropExpr β cfg min none
      let finalR ←  addInfo s!"{var} is irrelevant (unused)" id none r
      let h := (· <| Classical.ofNonempty)
      imp h none finalR  (PSum.inr <| fun x _ => x)
    | some e =>
      let (some aExp, some e') ← impProp? e | throwError m!"Expected an `Imp` proposition, got {← ppExpr e}"
      let r ← runPropExpr β cfg min e'
      let hExp ← mkAppOptM ``id #[e']
      let finalR ←  addInfo s!"{var} is irrelevant (unused)" id hExp r
      let nInst ← synthInstance <| ← mkAppM ``Nonempty #[aExp]
      let hExp ← withLocalDeclD `h e fun h => do
        mkLambdaFVars #[h] <| mkApp h nInst
      let h := (· <| Classical.ofNonempty)
      imp h hExp finalR  (PSum.inr <| fun x _ => x)

theorem prop_iff_subtype (p : α → Prop) (β : α → Prop) : NamedBinder var (∀ (x : α), NamedBinder var' (p x → β x)) ↔ ∀ (x : Subtype p), β x.val := by simp [Subtype.forall, NamedBinder]

-- This is unlikely to ever be used successfully because of the instance of `SampleableExt (Subtype p)` needed. Should probably have classes for implications instead.
instance (priority := 2000) subtypeVarTestable {p : α → Prop} {β : α → Prop}
    [∀ x, PrintableProp (p x)]
    [∀ x, MetaTestable (β x)][ToExpr α]
    [SampleableExt (Subtype p)]  {var'} :
    MetaTestable (NamedBinder var <| (x : α) → NamedBinder var' <| p x → β x) where
  runExpr cfg min e? :=
  match e? with
  | none => do
    letI (x : Subtype p) : MetaTestable (β x) :=
      { runExpr := fun cfg min e => do
          let r ← runPropExpr (β x.val) cfg min none
          let idExp ← mkAppOptM ``id #[e]
          addInfo s!"guard: {printProp (p x)} (by construction)" id idExp r (PSum.inr id) }
    do
      let r ← @runExpr (∀ x : Subtype p, β x.val) (@varTestable var  _ _ _ _) cfg min none
      iff (prop_iff_subtype p β) none r
  | some e => do
    let (some pExp, some βExp, some _) ← forallPropProp? e | throwError m!"Expected a `Forall` proposition with arrow, got {← ppExpr e}"
    let subType ← mkAppM ``Subtype #[pExp]
    letI (x : Subtype p) : MetaTestable (β x) :=
      { runExpr := fun cfg min e => do
          let xExp := toExpr x.val
          let y ← mkAppM' βExp #[xExp]
          let r ← runPropExpr (β x.val) cfg min y
          let idExp ← mkAppOptM ``id #[e]
          addInfo s!"guard: {printProp (p x)} (by construction)" id idExp r (PSum.inr id) }
    do
      let e' ← withLocalDeclD `x subType fun x => do
        let x' ← mkAppM ``Subtype.val #[x]
        let y ← mkAppM' βExp #[x']
        mkForallFVars #[x] y
      let r ← @runExpr (∀ x : Subtype p, β x.val) (@varTestable var  _ _ _ _) cfg min e'
      let hExp ← mkAppM ``prop_iff_subtype #[pExp, βExp]
      iff (prop_iff_subtype p β) hExp r

instance (priority := low) decidableTestable {p : Prop} [PrintableProp p] [Decidable p] :
    MetaTestable p where
  runExpr := fun _ _ e? _ => do
    if h : p then
      return success (PSum.inr h)
    else
      let s := printProp p
      let pf' ← do
        match e? with
        | none => pure none
        | some e =>
          let inst ←  synthInstance <| ← mkAppM ``Decidable #[e]
          let falseRefl ← mkAppM ``Eq.refl #[mkConst ``false]
          mkAppOptM ``of_decide_eq_false #[e, inst, falseRefl]
      -- checkDisproof pf' e
      -- logInfo "Decidable proof checked"
      return failure h pf' [s!"issue: {s} does not hold"] 0

end MetaTestable


section Meta
open MetaTestResult

namespace MetaTestable
/-- Execute `cmd` and repeat every time the result is `gaveUp` (at most `n` times). -/
def retry (cmd : MRand (MetaTestResult p)) : Nat → MRand (MetaTestResult p)
  | 0 => return MetaTestResult.gaveUp 1
  | n+1 => do
    let r ← cmd
    match r with
    | .success hp => return success hp
    | .failure h pf xs n => return failure h pf xs n
    | .gaveUp _ => retry cmd n

/-- Count the number of times the test procedure gave up. -/
def giveUp (x : Nat) : MetaTestResult p → MetaTestResult p
  | success (PSum.inl ()) => gaveUp x
  | success (PSum.inr p) => success <| (PSum.inr p)
  | gaveUp n => gaveUp <| n + x
  | MetaTestResult.failure h pf xs n => failure h pf xs n

end MetaTestable

/-- Try `n` times to find a counter-example for `p`. -/
def MetaTestable.runSuiteAux (p : Prop) [MetaTestable p] (propExpr: Option Expr) (cfg : Configuration) :
    MetaTestResult p → Nat → MRand (MetaTestResult p)
  | r, 0 => return r
  | r, n+1 => do
    let size := (cfg.numInst - n - 1) * cfg.maxSize / cfg.numInst
    if cfg.traceSuccesses then
      slimTrace s!"New sample"
      slimTrace s!"Retrying up to {cfg.numRetries} times until guards hold"
    let x ← retry (ReaderT.run (runPropExpr p cfg true propExpr) ⟨size⟩) cfg.numRetries
    match x with
    | success (PSum.inl ()) => runSuiteAux p propExpr cfg r n
    | gaveUp g => runSuiteAux p propExpr cfg (giveUp g r) n
    | _ => return x

/-- Try to find a counter-example of `p`. -/
def MetaTestable.runSuite (p : Prop) [MetaTestable p] (propExpr: Option Expr) (cfg : Configuration := {}) : MRand (MetaTestResult p) :=
  MetaTestable.runSuiteAux p propExpr cfg (success <| PSum.inl ()) cfg.numInst

/-- Run a test suite for `p` in `MetaM` using the global RNG in `stdGenRef`. -/
def MetaTestable.seekM (p : Prop) [MetaTestable p]  (cfg : Configuration := {}) (propExpr: Option Expr) : MetaM (MetaTestResult p) :=
  match cfg.randomSeed with
  | none => runRand (MetaTestable.runSuite p propExpr cfg)
  | some seed => runRandWith seed (MetaTestable.runSuite p propExpr cfg)

end Meta

open Decorations in
/-- Run a test suite for `p` and throw an exception if `p` does not hold. -/
def MetaTestable.seek (p : Prop) (cfg : Configuration := {})
    (p' : Decorations.DecorationsOf p := by mk_decorations) [MetaTestable p'](propExpr: Expr) : Lean.MetaM (Option Expr) := do
  match ← MetaTestable.seekM p' cfg propExpr with
  | MetaTestResult.success _ =>
    if !cfg.quiet then Lean.logInfo "Unable to find a counter-example"
    return none
  | MetaTestResult.gaveUp n =>
    if !cfg.quiet then
      let msg := s!"Gave up after failing to generate values that fulfill the preconditions {n} times."
      Lean.logWarning msg
    return none
  | MetaTestResult.failure _ pf xs n =>
    let msg := "Found a counter-example!"
    if cfg.quiet then
      Lean.logInfo msg
    else
      Lean.logInfo <| Testable.formatFailure msg xs n
    return pf

def disproveM? (cfg : Configuration) (tgt: Expr) : MetaM <| Option Expr := do
  let tgt' ← Decorations.addDecorations tgt
  let inst ← try
    synthInstance (← mkAppM ``MetaTestable #[tgt'])
  catch _ =>
    throwError "Failed to create a `testable` instance for `{tgt}`."
  let e ← mkAppOptM ``MetaTestable.seek #[tgt, toExpr cfg, tgt', inst]
  let expectedType := Lean.Expr.forallE `a
    (Lean.Expr.const `Lean.Expr [])
    (Lean.Expr.app
      (Lean.Expr.const `Lean.Meta.MetaM [])
      (Lean.Expr.app
        (Lean.Expr.const ``Option [Level.zero])
        (Lean.Expr.const ``Lean.Expr [])))
    (Lean.BinderInfo.default)
  let code ← unsafe evalExpr (Expr → MetaM (Option Expr)) expectedType e
  code tgt

open Decorations in
/-- Run a test suite for `p` and throw an exception if `p` does not hold. -/
def MetaTestable.check (p : Prop) (cfg : Configuration := {})
    (p' : Decorations.DecorationsOf p := by mk_decorations) [MetaTestable p'](propExpr: Option Expr := none) : Lean.MetaM Unit := do
  match ← MetaTestable.seekM p' cfg propExpr with
  | MetaTestResult.success _ =>
    if !cfg.quiet then Lean.logInfo "Unable to find a counter-example"
  | MetaTestResult.gaveUp n =>
    if !cfg.quiet then
      let msg := s!"Gave up after failing to generate values that fulfill the preconditions {n} times."
      Lean.logWarning msg
  | MetaTestResult.failure _ _ xs n =>
    let msg := "Found a counter-example!"
    if cfg.quiet then
      throwError msg
    else
      throwError  Testable.formatFailure msg xs n



end Plausible
