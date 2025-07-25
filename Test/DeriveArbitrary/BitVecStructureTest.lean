import Plausible.Gen
import Plausible.Arbitrary
import Plausible.GeneratorCombinators
import Plausible.DeriveArbitrary

open Arbitrary GeneratorCombinators

set_option guard_msgs.diff true

/-- Dummy `inductive` where a constructor has a dependently-typed argument (`BitVec n`)
    whose index does not appear in the overall type (`DummyInductive`) -/
inductive DummyInductive where
  | FromBitVec : ∀ (n : Nat), BitVec n → String → DummyInductive
  deriving Repr, Arbitrary

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instArbitrarySizedDummyInductive -/
#guard_msgs in
#synth ArbitrarySized DummyInductive

/-- info: instArbitraryOfArbitrarySized -/
#guard_msgs in
#synth Arbitrary DummyInductive

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this generator: instance : ArbitrarySized DummyInductive where
  arbitrarySized :=
    let rec aux_arb (size : Nat) : Plausible.Gen DummyInductive :=
      match size with
      | Nat.zero =>
        GeneratorCombinators.oneOfWithDefault
          (do
            let n_0 ← Arbitrary.arbitrary
            let a_0 ← Arbitrary.arbitrary
            let a_1 ← Arbitrary.arbitrary
            return DummyInductive.FromBitVec n_0 a_0 a_1)
          [GeneratorCombinators.thunkGen
              (fun _ => do
                let n_0 ← Arbitrary.arbitrary
                let a_0 ← Arbitrary.arbitrary
                let a_1 ← Arbitrary.arbitrary
                return DummyInductive.FromBitVec n_0 a_0 a_1)]
      | Nat.succ size' =>
        GeneratorCombinators.frequency
          (do
            let n_0 ← Arbitrary.arbitrary
            let a_0 ← Arbitrary.arbitrary
            let a_1 ← Arbitrary.arbitrary
            return DummyInductive.FromBitVec n_0 a_0 a_1)
          [(1,
              GeneratorCombinators.thunkGen
                (fun _ => do
                  let n_0 ← Arbitrary.arbitrary
                  let a_0 ← Arbitrary.arbitrary
                  let a_1 ← Arbitrary.arbitrary
                  return DummyInductive.FromBitVec n_0 a_0 a_1)),
            ]
    fun size => aux_arb size
-/
#guard_msgs(info, drop warning) in
#derive_arbitrary DummyInductive

end CommandElaboratorTest
