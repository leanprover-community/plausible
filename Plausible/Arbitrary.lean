/-
Copyright (c) 2025 Ernest Ng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ernest Ng
-/
import Plausible.Gen
import Plausible.Gen
import Plausible.Sampleable

/-!
# `Arbitrary` Typeclass

The `Arbitrary` typeclass represents types for which there exists a
random generator suitable for property-based testing, similar to
Haskell QuickCheck's `Arbitrary` typeclass and Rocq/Coq QuickChick's `Gen` typeclass.

The `ArbitraryFueled` typeclass is a verison of `Arbitrary` in which
fuel for the generator is made explicit.
Every `ArbitraryFueled` instance automatically leads to an `Arbitrary` instance.

(Note: the `SampleableExt` describes types which have *both* a generator & a shrinker,
whereas `Arbitrary` describes types which have a generator only.)

## Main definitions

* `Arbitrary` typeclass
* `ArbitraryFueled` typeclass

## References

* https://hackage.haskell.org/package/QuickCheck
* https://softwarefoundations.cis.upenn.edu/qc-current/QuickChickInterface.html

-/

namespace Plausible

open Gen SampleableExt

/-- The `Arbitrary` typeclass represents types for which there exists a
    random generator suitable for property-based testing.
    - This is the equivalent of Haskell QuickCheck's `Arbitrary` typeclass.
    - In QuickChick, this typeclass is called `Gen`, but `Gen` is already
    a reserved keyword in Plausible, so we call this typeclass `Arbitrary`
    following the Haskell QuickCheck convention). -/
class Arbitrary (α : Type) where
  /-- A random generator for values of the given type. -/
  arbitrary : Gen α

/-- A typeclass for *fueled* random generation, i.e. a variant of
    the `Arbitrary` typeclass where the fuel for the generator is made explicit.
    - This typeclass is equivalent to Rocq QuickChick's `arbitrarySized` typeclass
      (QuickChick uses the `Nat` parameter as both fuel and the generator size,
       here we use it just for fuel, as Plausible's `Gen` type constructor
       already internalizes the size parameter.) -/
class ArbitraryFueled (α : Type) where
  /-- Takes a `Nat` and produces a random generator dependent on the `Nat` parameter
      (which indicates the size of the output) -/
  arbitraryFueled : Nat → Gen α

/-- Every `ArbitraryFueled` instance gives rise to an `Arbitrary` instance -/
instance [ArbitraryFueled α] : Arbitrary α where
  arbitrary := Gen.sized ArbitraryFueled.arbitraryFueled

/-- Any type which implements Plausible's `SampleableExt` typeclass
    can be made an instance of our `Arbitrary` typeclass -/
instance [SampleableExt α] : Arbitrary α where
  arbitrary := SampleableExt.interp <$> SampleableExt.sample

namespace Arbitrary

/-- Samples from the generator associated with the `Arbitrary` instance for a type,
    using `size` as the size parameter for the generator.
    To invoke this function, you will need to specify what type `α` is,
    for example by doing `runArbitrary (α := Nat) 10`. -/
def runArbitrary [Arbitrary α] (size : Nat) : IO α :=
  Gen.run Arbitrary.arbitrary size

end Arbitrary

end Plausible
