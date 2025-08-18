import Lean
import Plausible.MetaTestable

open Plausible Plausible.MetaTestable
open Lean Meta Elab Term Tactic

-- Testing the pattern matching functions
open Lean Elab Term in
elab "#decompose_prop" t:term : command =>
  Command.liftTermElabM  do
    let e ← elabType t
    match ← orProp? e with
    | (some α, some β) => logInfo s!"Or: {← ppExpr α}; {← ppExpr β}"
    | _ => pure ()
    match ← andProp? e with
    | (some α, some β) => logInfo s!"And: {← ppExpr α}; {← ppExpr β}"
    | _ => pure ()
    match ← existsProp? e with
    | (some α, some β) => logInfo s!"Exists: {← ppExpr α}; domain {← ppExpr β}"
    | _ => pure ()
    match ← forallProp? e with
    | (some α, some β) => logInfo s!"Forall: {← ppExpr α}; domain {← ppExpr β}"
    | _ => pure ()
    match ← impProp? e with
    | (some α, some β) => logInfo s!"Implies: {← ppExpr α}; {← ppExpr β}"
    | _ => pure ()
    match ← eqlProp? e with
    | some (α, a, b) => logInfo s!"Eq: {← ppExpr α}; {← ppExpr a} and {← ppExpr b}"
    | _ => pure ()
    match ← iffProp? e with
    | some (α, β) => logInfo s!"Iff: {← ppExpr α}; {← ppExpr β}"
    | _ => pure ()

/-- info: Forall: fun x => x = 0 ∨ x ≠ 0; domain Nat -/
#guard_msgs in
#decompose_prop ∀ (n: Nat), n = 0 ∨ n ≠ 0

/-- info: Forall: fun x => x = 0 ∨ x ≠ 0; domain Nat -/
#guard_msgs in
#decompose_prop NamedBinder "blah" <| ∀ (n: Nat), n = 0 ∨ n ≠ 0

/-- info: Or: 1 = 0; 2 ≠ 0 -/
#guard_msgs in
#decompose_prop 1 = 0 ∨ 2 ≠ 0

/-- info: And: 1 = 0; 2 ≠ 0 -/
#guard_msgs in
#decompose_prop 1 = 0 ∧ 2 ≠ 0

/-- info: Exists: fun n => n = 0 ∨ n ≠ 0; domain Nat -/
#guard_msgs in
#decompose_prop ∃ (n: Nat), n = 0 ∨ n ≠ 0

/--
info: Forall: fun x => 2 ≠ 0; domain 1 = 0
---
info: Implies: 1 = 0; 2 ≠ 0
-/
#guard_msgs in
#decompose_prop 1 = 0 →  2 ≠ 0


/-- info: Iff: 1 = 0; 2 ≠ 0 -/
#guard_msgs in
#decompose_prop 1 = 0 ↔   2 ≠ 0

-- Elaborater to help with testing
elab "disprove%" t:term : term => do
  let tgt ← elabType t
  let cfg : Configuration := {}
  let (some code') ← disproveM? cfg tgt | throwError "disprove% failed"
  logInfo s!"disproof: {← ppExpr code'}; \ntype: {← ppExpr <| (← inferType code')}"
  return tgt

-- Testing the disproveM? function
/--
info:
===================
Found a counter-example!
a := 0
b := 0
issue: 0 < 0 does not hold
(0 shrinks)
-------------------
---
info: disproof: mt (fun x => x (SampleableExt.interp 0)) (mt (fun x => x (SampleableExt.interp 0)) (of_decide_eq_false (Eq.refl false))); ⏎
type: ¬∀ (a b : Nat), a < b
---
info: ∀ (a b : Nat), a < b : Prop
-/
#guard_msgs in
#check disprove% ∀ (a b : Nat), a < b

/--
info:
===================
Found a counter-example!
a := 0
b := 0
issue: 0 < 0 does not hold
issue: 0 < 0 does not hold
(0 shrinks)
-------------------
---
info: disproof: mt (fun x => x (SampleableExt.interp 0))
  (mt (fun x => x (SampleableExt.interp 0))
    (Or.rec (of_decide_eq_false (Eq.refl false)) (of_decide_eq_false (Eq.refl false)))); ⏎
type: ¬∀ (a b : Nat), a < b ∨ b < a
---
info: ∀ (a b : Nat), a < b ∨ b < a : Prop
-/
#guard_msgs in
#check disprove% ∀ (a b : Nat), a < b ∨ b < a

/--
info:
===================
Found a counter-example!
issue: False does not hold
(0 shrinks)
-------------------
---
info: disproof: fun h => of_decide_eq_false (Eq.refl false) h.left; ⏎
type: False ∧ False → False
---
info: False ∧ False : Prop
-/
#guard_msgs in
#check disprove% False ∧ False


elab "#expr" e:term : command =>
  Command.liftTermElabM  do
    let e ← elabTerm e none
    logInfo s!"{repr e}"
    logInfo s!"{← reduce e}"

elab "expr%" e:term : term => do
    let e ← elabTerm e none
    logInfo s!"{repr e}"
    logInfo s!"{← reduce e}"
    return e

-- Testing the MetaTestable class can be inferred
example : MetaTestable <| (1: Nat) = 0 := inferInstance

example : MetaTestable (NamedBinder "a" (∀ (a : Nat), a ≤ 1)) := inferInstance

example : MetaTestable (NamedBinder "a" (∀ (a : Nat), NamedBinder "b" (∀ (b : Nat), a ≤ b))) := inferInstance

-- Main tests: finding counterexamples
#eval MetaTestable.seek (∀ (_a : Nat), False) (propExpr := Lean.Expr.forallE `a (Lean.Expr.const `Nat []) (Lean.Expr.const `False []) (Lean.BinderInfo.default))


#eval MetaTestable.seek (∀ (a : Nat), a < 1) (propExpr := Lean.Expr.forallE `a (Lean.Expr.const `Nat []) (Lean.Expr.const `False []) (Lean.BinderInfo.default))

#eval MetaTestable.seek (∀ (a b : Nat), a < b) (propExpr := (Lean.Expr.forallE
  `a
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `b
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `LT.lt [Level.succ Level.zero])
            (Lean.Expr.const `Nat []))
          (Lean.Expr.const `instLTNat []))
        (Lean.Expr.bvar 1))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)))

#eval MetaTestable.seek (∀ (a _b : Nat), a < 0) (propExpr := (Lean.Expr.forallE
  `a
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `b
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `LT.lt [Level.succ Level.zero])
            (Lean.Expr.const `Nat []))
          (Lean.Expr.const `instLTNat []))
        (Lean.Expr.bvar 1))
      (Lean.Expr.lit (Lean.Literal.natVal 0)))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)))
