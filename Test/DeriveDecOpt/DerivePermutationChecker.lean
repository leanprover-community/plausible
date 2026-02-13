/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.EnumeratorCombinators
import Test.CommonDefinitions.Permutation
import Test.DeriveEnumSuchThat.DerivePermutationEnumerator


#guard_msgs(drop info, drop warning) in
derive_checker (fun l l' => Permutation l l')


-- Example: to run the derived checker, you can uncomment the following
def l := [1, 2, 3, 4]
def l' := [2, 1, 3, 4]
/--info: true-/
#guard_msgs in
#eval (DecOpt.decOpt (Permutation l l')) 0
