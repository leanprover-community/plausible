/-
Copyright (c) 2025 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
module

public import Plausible.Arbitrary
public import Plausible.Gen

public section

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
      (which indicates the amount of fuel to be used before failing). -/
  arbitraryFueled : Nat → Gen α

/-- Every `ArbitraryFueled` instance gives rise to an `Arbitrary` instance -/
meta instance [ArbitraryFueled α] : Arbitrary α where
  arbitrary := Gen.sized ArbitraryFueled.arbitraryFueled

/-- Raised when a fueled generator fails due to insufficient fuel. -/
meta def Gen.outOfFuel : GenError :=
  .genError "out of fuel"

end Plausible
