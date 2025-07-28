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

The `ArbitrarySized` typeclass is a verison of `Arbitrary` in which
the generator's internal size parameter is made explicit.
Every `ArbitrarySized` instance automatically leads to an `Arbitrary` instance.

(Note: the `SampleableExt` describes types which have *both* a generator & a shrinker,
whereas `Arbitrary` describes types which have a generator only.)

## Main definitions

* `Arbitrary` typeclass
* `ArbitrarySized` typeclass

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

/-- A typeclass for sized random generation, i.e. a variant of
    the `Arbitrary` typeclass where the generator's internal size
    parameter is made explicit.
    - This typeclass is equivalent to QuickChick's `arbitrarySized` typeclass. -/
class ArbitrarySized (α : Type) where
  /-- Takes a `Nat` and produces a random generator dependent on the `Nat` parameter
      (which indicates the size of the output) -/
  arbitrarySized : Nat → Gen α

/-- Every `ArbitrarySized` instance gives rise to an `Arbitrary` instance -/
instance [ArbitrarySized α] : Arbitrary α where
  arbitrary := Gen.sized ArbitrarySized.arbitrarySized

/-- If we have `Repr`, `ArbitrarySized` & `Shrinkable` instances for a type,
    then that type gets a `SampleableExt` instance
    - Note: Plausible's `SampleableExt` is analogous to QuickChick's `Arbitrary` typeclass
      (which combines QuickChick's `Gen` and `Shrink` typeclass)-/
instance [Repr α] [Shrinkable α] [ArbitrarySized α] : SampleableExt α :=
  SampleableExt.mkSelfContained (Gen.sized ArbitrarySized.arbitrarySized)

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
