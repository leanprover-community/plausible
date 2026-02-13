/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Test.CommonDefinitions.Permutation


#guard_msgs(drop info, drop warning) in
derive_enumerator (fun l' => ∃ (l : List Nat), Permutation l l')

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun l' => ∃ (l : List Nat), Permutation l' l)
