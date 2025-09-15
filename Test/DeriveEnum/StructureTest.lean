import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveEnum
import Test.DeriveArbitrary.StructureTest

set_option guard_msgs.diff true

deriving instance Enum for Foo

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instEnumSizedFoo -/
#guard_msgs in
#synth EnumSized Foo

/-- info: instEnumOfEnumSized -/
#guard_msgs in
#synth Enum Foo

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this enumerator: instance : EnumSized Foo where
  enumSized :=
    let rec aux_enum (size : Nat) : Enumerator Foo :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.oneOfWithDefault
          (do
            let stringField_0 ← Enum.enum
            let boolField_0 ← Enum.enum
            let natField_0 ← Enum.enum
            return Foo.mk stringField_0 boolField_0 natField_0)
          [do
            let stringField_0 ← Enum.enum
            let boolField_0 ← Enum.enum
            let natField_0 ← Enum.enum
            return Foo.mk stringField_0 boolField_0 natField_0]
      | Nat.succ size' =>
        EnumeratorCombinators.oneOfWithDefault
          (do
            let stringField_0 ← Enum.enum
            let boolField_0 ← Enum.enum
            let natField_0 ← Enum.enum
            return Foo.mk stringField_0 boolField_0 natField_0)
          [do
            let stringField_0 ← Enum.enum
            let boolField_0 ← Enum.enum
            let natField_0 ← Enum.enum
            return Foo.mk stringField_0 boolField_0 natField_0, ]
    fun size => aux_enum size
-/
#guard_msgs(info, drop warning) in
#derive_enum Foo

end CommandElaboratorTest
