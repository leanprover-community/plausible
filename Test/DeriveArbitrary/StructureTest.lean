import Plausible.Gen
import Plausible.Arbitrary
import Plausible.GeneratorCombinators
import Plausible.DeriveArbitrary

open Plausible GeneratorCombinators

set_option guard_msgs.diff true

/-- Dummy `structure` with named fields -/
structure Foo where
  stringField : String
  boolField : Bool
  natField : Nat
  deriving Repr, Arbitrary

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instArbitrarySizedFoo -/
#guard_msgs in
#synth ArbitrarySized Foo

/-- info: instArbitraryOfArbitrarySized -/
#guard_msgs in
#synth Arbitrary Foo

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this generator: instance : ArbitrarySized Foo where
  arbitrarySized :=
    let rec aux_arb (size : Nat) : Plausible.Gen Foo :=
      match size with
      | Nat.zero =>
        GeneratorCombinators.oneOfWithDefault
          (do
            let stringField_0 ← Arbitrary.arbitrary
            let boolField_0 ← Arbitrary.arbitrary
            let natField_0 ← Arbitrary.arbitrary
            return Foo.mk stringField_0 boolField_0 natField_0)
          [GeneratorCombinators.thunkGen
              (fun _ => do
                let stringField_0 ← Arbitrary.arbitrary
                let boolField_0 ← Arbitrary.arbitrary
                let natField_0 ← Arbitrary.arbitrary
                return Foo.mk stringField_0 boolField_0 natField_0)]
      | Nat.succ size' =>
        GeneratorCombinators.frequency
          (do
            let stringField_0 ← Arbitrary.arbitrary
            let boolField_0 ← Arbitrary.arbitrary
            let natField_0 ← Arbitrary.arbitrary
            return Foo.mk stringField_0 boolField_0 natField_0)
          [(1,
              GeneratorCombinators.thunkGen
                (fun _ => do
                  let stringField_0 ← Arbitrary.arbitrary
                  let boolField_0 ← Arbitrary.arbitrary
                  let natField_0 ← Arbitrary.arbitrary
                  return Foo.mk stringField_0 boolField_0 natField_0)),
            ]
    fun size => aux_arb size
-/
#guard_msgs(info, drop warning) in
#derive_arbitrary Foo

end CommandElaboratorTest
