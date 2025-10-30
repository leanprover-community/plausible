import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.EnumeratorCombinators
import Test.DeriveDecOpt.DeriveBSTChecker
import Test.DeriveEnumSuchThat.DeriveSTLCEnumerator
import Test.CommonDefinitions.STLCDefinitions

open DecOpt

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_checker (fun Γ e τ => typing Γ e τ)
