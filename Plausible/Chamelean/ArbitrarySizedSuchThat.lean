/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
import Plausible.Gen
import Plausible.Arbitrary
open Plausible

/-- Sized generators of type `α` such that `P : α -> Prop` holds for all generated values. -/
class ArbitrarySizedSuchThat (α : Type u) (P : α → Prop) where
  arbitrarySizedST : Nat → Gen α

/-- Generators of type `α` such that `P : α -> Prop` holds for all generated values. -/
class ArbitrarySuchThat (α : Type u) (P : α → Prop) where
  arbitraryST : Gen α

/-- Every `ArbitrarySizedSuchThat` instance can be automatically given a `ArbitrarySuchThat` instance -/
instance [ArbitrarySizedSuchThat α P] : ArbitrarySuchThat α P where
  arbitraryST := Gen.sized (ArbitrarySizedSuchThat.arbitrarySizedST P)

/-- `ArbitrarySizedSuchThat` instance for equality propositions
     where a variable `x` is left-equal to some value `val`.
     (Note: `val` can be the result of a fully-applied function application,
     which is typically how this typeclass is used!) -/
instance {α : Type u} {val : α} : ArbitrarySizedSuchThat α (fun x => x = val) where
  arbitrarySizedST _ := return val

/-- `ArbitrarySizedSuchThat` instance for equality propositions
     where a variable `x` is right-equal to some value `val`.
    (Note: `val` can be the result of a fully-applied function application,
     which is typically how this typeclass is used!) -/
instance {α : Type u} {val : α} : ArbitrarySizedSuchThat α (fun x => val = x) where
  arbitrarySizedST _ := return val

/-- `Arbitrary` instance for decidable predicates. It's expected that every (successfully) generated element for am `ArbitrarySuchThat α P` will satisfy  `P`.
  We therefore try to return an element of the relevant subset type.
-/
instance instArbitraryArbitrarySuchThatDec {α} {P : α → Prop} [DecidablePred P] [ArbitrarySuchThat _ P] : Arbitrary {x // P x} where
  arbitrary := do
    let x ← ArbitrarySuchThat.arbitraryST P
    if h : P x then
      return ⟨x, h⟩
    else
      throw <| .genError "Generated element did not satisfy the predicate."
