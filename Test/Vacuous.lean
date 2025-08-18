import Plausible.Vacuous
open Lean Meta Elab

elab "prove_vacuous" type:term : term => do
  let p ← Term.elabType type
  let vacuous ← proveVacuous? p
  match vacuous with
  | some pf =>
    return pf
  | none =>
    logWarning m!"No vacuous proof found"
    return mkConst ``False

/--
info:
===================
Found a counter-example!
issue: 2 < 1 does not hold
(0 shrinks)
-------------------
---
info: Vacuous Implication. Hypothesis 2 < 1 is never satisfied
---
info: fun a => False.elim (of_decide_eq_false (Eq.refl false) a) : 2 < 1 → 1 ≤ 3
-/
#guard_msgs in
#check prove_vacuous ((2 : Nat) < 1) → 1 ≤ 3

-- We cannot use `guard_msgs` here because of random search. Need to add seeds as a parameter.

#check prove_vacuous (∀ n: Nat, n < (4: Nat)) → 1 ≤ 3

example : (∀ n: Nat, n < (4: Nat)) → 4 ≤ 3 := by vacuous

example (h: ∀ n: Nat, n < (4: Nat)) : 4 ≤ 3 := by vacuous

example (m: Nat) (h: ∀ n: Nat, n < (4: Nat)) : m ≤ 3 := by vacuous
