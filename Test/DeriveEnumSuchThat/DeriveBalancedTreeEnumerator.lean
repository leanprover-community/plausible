/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Test.DeriveArbitrarySuchThat.DeriveBalancedTreeGenerator

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun n => ∃ (t : BinaryTree), balancedTree n t)
