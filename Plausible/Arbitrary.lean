/-
Copyright (c) 2025 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
import Plausible.Gen


/-!
# `Arbitrary` Typeclass

The `Arbitrary` typeclass represents types for which there exists a
random generator suitable for property-based testing, similar to
Haskell QuickCheck's `Arbitrary` typeclass and Rocq/Coq QuickChick's `Gen` typeclass.

(Note: the `Arbitrary` describes types which have *both* a generator & a shrinker,
whereas `Arbitrary` describes types which have a generator only.)

## Main definitions

* `Arbitrary` typeclass
* `ArbitraryFueled` typeclass

## References

* https://hackage.haskell.org/package/QuickCheck
* https://softwarefoundations.cis.upenn.edu/qc-current/QuickChickInterface.html

-/

namespace Plausible

open Gen

universe u

/-- The `Arbitrary` typeclass represents types for which there exists a
    random generator suitable for property-based testing.
    - This is the equivalent of Haskell QuickCheck's `Arbitrary` typeclass.
    - In QuickChick, this typeclass is called `Gen`, but `Gen` is already
    a reserved keyword in Plausible, so we call this typeclass `Arbitrary`
    following the Haskell QuickCheck convention). -/
class Arbitrary (α : Type u) where
  /-- A random generator for values of the given type. -/
  arbitrary : Gen α


namespace Arbitrary

/-- Samples from the generator associated with the `Arbitrary` instance for a type,
    using `size` as the size parameter for the generator.
    To invoke this function, you will need to specify what type `α` is,
    for example by doing `runArbitrary (α := Nat) 10`. -/
def runArbitrary [Arbitrary α] (size : Nat) : IO α :=
  Gen.run Arbitrary.arbitrary size

end Arbitrary

section Instances

open Arbitrary

instance Sum.Arbitrary [Arbitrary α] [Arbitrary β] : Arbitrary (Sum α β) where
  arbitrary := do
    match ← chooseAny Bool with
    | true => return .inl (← arbitrary)
    | false => return .inr (← arbitrary)

instance Unit.Arbitrary : Arbitrary Unit := ⟨return ()⟩

instance [Arbitrary α] [Arbitrary β] : Arbitrary ((_ : α) × β) where
  arbitrary := do
    let p ← prodOf arbitrary arbitrary
    return ⟨p.fst, p.snd⟩

instance Nat.Arbitrary : Arbitrary Nat := ⟨do choose Nat 0 (← getSize) (Nat.zero_le _)⟩

instance Fin.Arbitrary {n : Nat} : Arbitrary (Fin (n.succ)) :=
  ⟨do
    let m ← choose Nat 0 (min (← getSize) n) (Nat.zero_le _)
    return (Fin.ofNat _ m)⟩

instance BitVec.Arbitrary {n : Nat} : Arbitrary (BitVec n) :=
  ⟨do
    let m ← choose Nat 0 (min (← getSize) (2^n)) (Nat.zero_le _)
    return BitVec.ofNat _ m⟩

instance UInt8.Arbitrary : Arbitrary UInt8 :=
  ⟨do
    let n ← choose Nat 0 (min (← getSize) UInt8.size) (Nat.zero_le _)
    return UInt8.ofNat n⟩

instance UInt16.Arbitrary : Arbitrary UInt16 :=
  ⟨do
    let n ← choose Nat 0 (min (← getSize) UInt16.size) (Nat.zero_le _)
    return UInt16.ofNat n⟩

instance UInt32.Arbitrary : Arbitrary UInt32 :=
  ⟨do
    let n ← choose Nat 0 (min (← getSize) UInt32.size) (Nat.zero_le _)
    return UInt32.ofNat n⟩

instance UInt64.Arbitrary : Arbitrary UInt64 :=
  ⟨do
    let n ← choose Nat 0 (min (← getSize) UInt64.size) (Nat.zero_le _)
    return UInt64.ofNat n⟩

instance USize.Arbitrary : Arbitrary USize :=
  ⟨do
    let n ← choose Nat 0 (min (← getSize) USize.size) (Nat.zero_le _)
    return USize.ofNat n⟩

instance Int.Arbitrary : Arbitrary Int :=
  ⟨do
    choose Int (-(← getSize)) (← getSize) (by omega)⟩

instance Bool.Arbitrary : Arbitrary Bool :=
  ⟨chooseAny Bool⟩

/-- This can be specialized into customized `Arbitrary Char` instances.
The resulting instance has `1 / length` chances of making an unrestricted choice of characters
and it otherwise chooses a character from `chars` with uniform probabilities. -/
def Char.arbitraryFromList (length : Nat) (chars : List Char) (pos : 0 < chars.length) :
    Arbitrary Char :=
  ⟨do
    let x ← choose Nat 0 length (Nat.zero_le _)
    if x.val == 0 then
      let n ← arbitrary
      pure <| Char.ofNat n
    else
      elements chars pos⟩

instance Char.arbitraryDefaultInstance : Arbitrary Char :=
  Char.arbitraryFromList 3 " 0123abcABC:,;`\\/".toList (by decide)

instance Option.Arbitrary [Arbitrary α] : Arbitrary (Option α) where
  arbitrary := do
    match ← chooseAny Bool with
    | true => return none
    | false => return some (← arbitrary)

instance Prod.Arbitrary {α : Type u} {β : Type v} [Arbitrary α] [Arbitrary β] :
    Arbitrary (α × β) where
  arbitrary := prodOf arbitrary arbitrary

instance List.Arbitrary [Arbitrary α] : Arbitrary (List α) where
  arbitrary := Gen.listOf arbitrary

instance ULift.Arbitrary [Arbitrary α] : Arbitrary (ULift α) where
  arbitrary := do let x : α ← arbitrary; return ⟨x⟩

instance String.Arbitrary : Arbitrary String :=
  ⟨return String.mk (← Gen.listOf Char.arbitraryDefaultInstance.arbitrary)⟩

instance Array.Arbitrary [Arbitrary α] : Arbitrary (Array α) := ⟨Gen.arrayOf arbitrary⟩

end Instances

end Plausible
