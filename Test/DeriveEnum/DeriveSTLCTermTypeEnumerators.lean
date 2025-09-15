import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveEnum
import Test.CommonDefinitions.STLCDefinitions

set_option guard_msgs.diff true

-- Invoke deriving instance handler for the `Arbitrary` typeclass on `type` and `term`
deriving instance Enum for type, term

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`
-- for both `type` & `term`

/-- info: instEnumSizedType -/
#guard_msgs in
#synth EnumSized type

/-- info: instEnumSizedTerm -/
#guard_msgs in
#synth EnumSized term

/-- info: instEnumOfEnumSized -/
#guard_msgs in
#synth Enum type

/-- info: instEnumOfEnumSized -/
#guard_msgs in
#synth Enum term

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this enumerator: instance : EnumSized type where
  enumSized :=
    let rec aux_enum (size : Nat) : Enumerator type :=
      match size with
      | Nat.zero => EnumeratorCombinators.oneOfWithDefault (pure type.Nat) [pure type.Nat]
      | Nat.succ size' =>
        EnumeratorCombinators.oneOfWithDefault (pure type.Nat)
          [pure type.Nat, do
            let a_0 ← aux_enum size'
            let a_1 ← aux_enum size'
            return type.Fun a_0 a_1]
    fun size => aux_enum size
-/
#guard_msgs(info, drop warning) in
#derive_enum type

/--
info: Try this enumerator: instance : EnumSized term where
  enumSized :=
    let rec aux_enum (size : Nat) : Enumerator term :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.oneOfWithDefault
          (do
            let a_0 ← Enum.enum
            return term.Const a_0)
          [do
            let a_0 ← Enum.enum
            return term.Const a_0, do
            let a_0 ← Enum.enum
            return term.Var a_0]
      | Nat.succ size' =>
        EnumeratorCombinators.oneOfWithDefault
          (do
            let a_0 ← Enum.enum
            return term.Const a_0)
          [do
            let a_0 ← Enum.enum
            return term.Const a_0, do
            let a_0 ← Enum.enum
            return term.Var a_0, do
            let a_0 ← aux_enum size'
            let a_1 ← aux_enum size'
            return term.Add a_0 a_1, do
            let a_0 ← aux_enum size'
            let a_1 ← aux_enum size'
            return term.App a_0 a_1, do
            let a_0 ← Enum.enum
            let a_1 ← aux_enum size'
            return term.Abs a_0 a_1]
    fun size => aux_enum size
-/
#guard_msgs(info, drop warning) in
#derive_enum term

end CommandElaboratorTest
