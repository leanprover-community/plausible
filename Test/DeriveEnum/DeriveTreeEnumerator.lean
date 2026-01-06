/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveEnum
import Test.CommonDefinitions.BinaryTree

set_option guard_msgs.diff true

-- Invoke deriving instance handler for the `Arbitrary` typeclass on `type` and `term`
deriving instance Enum for BinaryTree

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

#guard_msgs(drop info, drop warning) in
#synth EnumSized BinaryTree

#guard_msgs(drop info, drop warning) in
#synth Enum BinaryTree

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

#guard_msgs(drop info, drop warning) in
derive_enum BinaryTree

end CommandElaboratorTest
