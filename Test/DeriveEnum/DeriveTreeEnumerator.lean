import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveEnum
import Test.CommonDefinitions.BinaryTree

set_option guard_msgs.diff true

-- Invoke deriving instance handler for the `Arbitrary` typeclass on `type` and `term`
deriving instance Enum for BinaryTree

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instEnumSizedBinaryTree -/
#guard_msgs in
#synth EnumSized BinaryTree

/-- info: instEnumOfEnumSized -/
#guard_msgs in
#synth Enum BinaryTree

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this enumerator: instance : EnumSized BinaryTree where
  enumSized :=
    let rec aux_enum (size : Nat) : Enumerator BinaryTree :=
      match size with
      | Nat.zero => EnumeratorCombinators.oneOfWithDefault (pure BinaryTree.Leaf) [pure BinaryTree.Leaf]
      | Nat.succ size' =>
        EnumeratorCombinators.oneOfWithDefault (pure BinaryTree.Leaf)
          [pure BinaryTree.Leaf, do
            let a_0 ← Enum.enum
            let a_1 ← aux_enum size'
            let a_2 ← aux_enum size'
            return BinaryTree.Node a_0 a_1 a_2]
    fun size => aux_enum size
-/
#guard_msgs(info, drop warning) in
#derive_enum BinaryTree

end CommandElaboratorTest
