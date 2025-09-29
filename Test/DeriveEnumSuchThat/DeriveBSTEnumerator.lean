import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Test.DeriveArbitrarySuchThat.DeriveBSTGenerator

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
#derive_enumerator (fun (x : Nat) => Between lo x hi)

#guard_msgs(drop info, drop warning) in
#derive_enumerator (fun (t : BinaryTree) => BST lo hi t)
