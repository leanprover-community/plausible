/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Test.DeriveArbitrarySuchThat.DeriveBSTGenerator

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun lo hi => ∃ (x : Nat), Between lo x hi)

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun lo hi => ∃ (t : BinaryTree), BST lo hi t)
