/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveChecker
import Test.DeriveDecOpt.DeriveBSTChecker
import Test.DeriveArbitrarySuchThat.DeriveBalancedTreeGenerator

open DecOpt

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_checker (fun n t => balancedTree n t)
