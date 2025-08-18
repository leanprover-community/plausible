import Plausible.RandomSearch

open Plausible

/-
¬1 = 4 : Prop
-/
#check neg_neg (1 = 4)

/-
Negation of ¬1 = 4 is 1 = 4
-/
#check neg_neg ¬(1 = 4)

/-
Proof of negation is fun h =>
  induced_and id (not_not (2 < 4))
    (not_or_mp h) with type ¬(1 = 4 ∨ ¬2 < 4) → ¬1 = 4 ∧ 2 < 4, should be ¬(1 = 4 ∨ ¬2 < 4) → ¬1 = 4 ∧ 2 < 4
-/
#check neg_neg ¬(1 = 4) ∧ (2 < 4)

/-
check: true
-/
#check neg_neg (1 = 4) ∨ (¬ (2 < 4))

/-
check: true
-/
#check neg_neg ∃ x : Nat, x > 0

example : ¬ (1 = 4) := by
  /-
  Found a proof by negated counter-example!
  -/
  random_search

example : ∃ n : Nat, n > 0 ∧ n < 4 := by
  /-
  Found a proof by negated counter-example!
  -/
  random_search
