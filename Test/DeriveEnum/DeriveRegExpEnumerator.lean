import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveEnum
import Test.DeriveArbitrary.DeriveRegExpGenerator

set_option guard_msgs.diff true

deriving instance Enum for RegExp

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instEnumSizedRegExp -/
#guard_msgs in
#synth EnumSized RegExp

/-- info: instEnumOfEnumSized -/
#guard_msgs in
#synth Enum RegExp

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this enumerator: instance : EnumSized RegExp where
  enumSized :=
    let rec aux_enum (size : Nat) : Enumerator RegExp :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.oneOfWithDefault (pure RegExp.EmptySet)
          [pure RegExp.EmptySet, pure RegExp.EmptyStr, do
            let a_0 ← Enum.enum
            return RegExp.Char a_0]
      | Nat.succ size' =>
        EnumeratorCombinators.oneOfWithDefault (pure RegExp.EmptySet)
          [pure RegExp.EmptySet, pure RegExp.EmptyStr, do
            let a_0 ← Enum.enum
            return RegExp.Char a_0, do
            let a_0 ← aux_enum size'
            let a_1 ← aux_enum size'
            return RegExp.App a_0 a_1, do
            let a_0 ← aux_enum size'
            let a_1 ← aux_enum size'
            return RegExp.Union a_0 a_1, do
            let a_0 ← aux_enum size'
            return RegExp.Star a_0]
    fun size => aux_enum size
-/
#guard_msgs(info, drop warning) in
#derive_enum RegExp

end CommandElaboratorTest
