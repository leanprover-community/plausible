import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.EnumeratorCombinators
import Test.CommonDefinitions.Permutation
import Test.DeriveEnumSuchThat.DerivePermutationEnumerator


#guard_msgs(drop info, drop warning) in
derive_checker (fun l l' => Permutation l l')


-- Example: to run the derived checker, you can uncomment the following
-- def l := [1, 2, 3, 4]
-- def l' := [2, 1, 3, 4]
-- #eval (DecOpt.decOpt (Permutation l l')) 2
