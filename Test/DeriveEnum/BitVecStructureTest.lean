import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveEnum
import Test.DeriveArbitrary.BitVecStructureTest

set_option guard_msgs.diff true

deriving instance Enum for DummyInductive

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instEnumSizedDummyInductive -/
#guard_msgs in
#synth EnumSized DummyInductive

/-- info: instEnumOfEnumSized -/
#guard_msgs in
#synth Enum DummyInductive

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this enumerator: instance : EnumSized DummyInductive where
  enumSized :=
    let rec aux_enum (size : Nat) : Enumerator DummyInductive :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.oneOfWithDefault
          (do
            let n_0 ← Enum.enum
            let a_0 ← Enum.enum
            let a_1 ← Enum.enum
            return DummyInductive.FromBitVec n_0 a_0 a_1)
          [do
            let n_0 ← Enum.enum
            let a_0 ← Enum.enum
            let a_1 ← Enum.enum
            return DummyInductive.FromBitVec n_0 a_0 a_1]
      | Nat.succ size' =>
        EnumeratorCombinators.oneOfWithDefault
          (do
            let n_0 ← Enum.enum
            let a_0 ← Enum.enum
            let a_1 ← Enum.enum
            return DummyInductive.FromBitVec n_0 a_0 a_1)
          [do
            let n_0 ← Enum.enum
            let a_0 ← Enum.enum
            let a_1 ← Enum.enum
            return DummyInductive.FromBitVec n_0 a_0 a_1, ]
    fun size => aux_enum size
-/
#guard_msgs(info, drop warning) in
#derive_enum DummyInductive

end CommandElaboratorTest
