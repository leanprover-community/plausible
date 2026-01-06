/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Test.DeriveArbitrarySuchThat.DeriveRegExpMatchGenerator

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun r0 => ∃ (s : List Nat), ExpMatch s r0)

-- To sample from this enumerator, we can run the following:
#guard_msgs(drop info) in
#eval runSizedEnum (EnumSizedSuchThat.enumSizedST (fun s => ExpMatch s r)) 10
