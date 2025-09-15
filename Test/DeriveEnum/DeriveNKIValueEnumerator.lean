import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveEnum
import Test.DeriveArbitrary.DeriveNKIValueGenerator

deriving instance Enum for NKIValue

set_option guard_msgs.diff true

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instEnumSizedNKIValue -/
#guard_msgs in
#synth EnumSized NKIValue

/-- info: instEnumOfEnumSized -/
#guard_msgs in
#synth Enum NKIValue

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this enumerator: instance : EnumSized NKIValue where
  enumSized :=
    let rec aux_enum (size : Nat) : Enumerator NKIValue :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.oneOfWithDefault (pure NKIValue.none)
          [pure NKIValue.none, do
            let value_0 ← Enum.enum
            return NKIValue.bool value_0, do
            let value_0 ← Enum.enum
            return NKIValue.int value_0, do
            let value_0 ← Enum.enum
            return NKIValue.string value_0, pure NKIValue.ellipsis, do
            let shape_0 ← Enum.enum
            let dtype_0 ← Enum.enum
            return NKIValue.tensor shape_0 dtype_0]
      | Nat.succ size' =>
        EnumeratorCombinators.oneOfWithDefault (pure NKIValue.none)
          [pure NKIValue.none, do
            let value_0 ← Enum.enum
            return NKIValue.bool value_0, do
            let value_0 ← Enum.enum
            return NKIValue.int value_0, do
            let value_0 ← Enum.enum
            return NKIValue.string value_0, pure NKIValue.ellipsis, do
            let shape_0 ← Enum.enum
            let dtype_0 ← Enum.enum
            return NKIValue.tensor shape_0 dtype_0, ]
    fun size => aux_enum size
-/
#guard_msgs(info, drop warning) in
#derive_enum NKIValue

end CommandElaboratorTest
