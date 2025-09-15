import Plausible.Gen
import Plausible.Chamelean.OptionTGen
open Plausible

/-- Sized generators of type `α` such that `P : α -> Prop` holds for all generated values.
    Note that these generators may fail, which is why they have type `OptionT Gen α`. -/
class ArbitrarySizedSuchThat (α : Type) (P : α → Prop) where
  arbitrarySizedST : Nat → OptionT Gen α

/-- Generators of type `α` such that `P : α -> Prop` holds for all generated values.
    Note that these generators may fail, which is why they have type `OptionT Gen α`. -/
class ArbitrarySuchThat (α : Type) (P : α → Prop) where
  arbitraryST : OptionT Gen α

/-- Every `ArbitrarySizedSuchThat` instance can be automatically given a `ArbitrarySuchThat` instance
    using the `OptionTGen.sized` combinator -/
instance [ArbitrarySizedSuchThat α P] : ArbitrarySuchThat α P where
  arbitraryST := OptionTGen.sized (ArbitrarySizedSuchThat.arbitrarySizedST P)

/-- `ArbitrarySizedSuchThat` instance for equality propositions
     where a variable `x` is left-equal to some value `val`.
     (Note: `val` can be the result of a fully-applied function application,
     which is typically how this typeclass is used!) -/
instance {α : Type} [BEq α] {val : α} : ArbitrarySizedSuchThat α (fun x => x = val) where
  arbitrarySizedST _ := return val

/-- `ArbitrarySizedSuchThat` instance for equality propositions
     where a variable `x` is right-equal to some value `val`.
    (Note: `val` can be the result of a fully-applied function application,
     which is typically how this typeclass is used!) -/
instance {α : Type} [BEq α] {val : α} : ArbitrarySizedSuchThat α (fun x => val = x) where
  arbitrarySizedST _ := return val
