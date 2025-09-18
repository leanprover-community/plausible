/-
Copyright (c) 2025 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ernest Ng
-/
import Plausible.Gen
import Plausible.Arbitrary


namespace Plausible

open Gen

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

def Gen.outOfFuel : GenError := .genError "GenError: Out of fuel."
