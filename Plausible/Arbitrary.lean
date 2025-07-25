import Plausible.Gen
import Plausible.GeneratorCombinators
import Plausible.Sampleable

open Plausible

/-- This is the equivalent of Haskell QuickCheck's `Arbitrary` typeclass
    reprensenting types for which there exists a random generator suitable
    for property-based testing.
    (In QuickChick, this typeclass is called `Gen`, but `Gen` is already
    a reserved keyword in Plausible, so we call this typeclass `Arbitrary`
    following the Haskell QC convention). -/
class Arbitrary (α : Type) where
  arbitrary : Gen α

/-- A typeclass for sized generation.
    Equivalent to QuickChick's `arbitrarySized` typeclass -/
class ArbitrarySized (α : Type) where
  arbitrarySized : Nat → Gen α

/-- Every `ArbitrarySized` instance gives rise to an `Arbitrary` instance -/
instance [ArbitrarySized α] : Arbitrary α where
  arbitrary := GeneratorCombinators.sized ArbitrarySized.arbitrarySized

/-- If we have `Repr`, `ArbitrarySized` & `Shrinkable` instances for a type,
    then that type gets a `SampleableExt` instance
    - Note: Plausible's `SampleableExt` is analogous to QuickChick's `Arbitrary` typeclass
      (which combines QuickChick's `Gen` and `Shrink` typeclass)-/
instance [Repr α] [Shrinkable α] [ArbitrarySized α] : SampleableExt α :=
  SampleableExt.mkSelfContained (GeneratorCombinators.sized ArbitrarySized.arbitrarySized)

/-- Any type which implements Plausible's `SampleableExt` typeclass
    can be made an instance of our `Arbitrary` typeclass -/
instance [SampleableExt α] : Arbitrary α where
  arbitrary := SampleableExt.interp <$> SampleableExt.sample

/-- Samples from the generator associated with the `Arbitrary` instance for a type,
    using `size` as the size parameter for the generator.
    To invoke this function, you will need to specify what type `α` is,
    for example by doing `runArbitrary (α := Nat) 10`. -/
def runArbitrary {α} [Arbitrary α] (size : Nat) : IO α :=
  Gen.run Arbitrary.arbitrary size
