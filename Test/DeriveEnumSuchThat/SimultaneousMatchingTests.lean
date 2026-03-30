/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Test.DeriveDecOpt.SimultaneousMatchingTests

-- See `Test/CommonDefinitions/ListRelations.lean` for the definition of the inductive relations
import Test.CommonDefinitions.ListRelations

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun x => ∃ (l : List Nat), InList x l)

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun a => ∃ (l: List Nat), MinOk l a)

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun n a => ∃ (l: List Nat), MinEx n l a)
