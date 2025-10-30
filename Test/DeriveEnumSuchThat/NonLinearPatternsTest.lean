import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Test.DeriveEnumSuchThat.DeriveBSTEnumerator

-- See `Test/DeriveArbitrarySuchThat/NonLinearPatternsTest.lean` for the definition of the inductive relations
import Test.DeriveArbitrarySuchThat.NonLinearPatternsTest

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun in1 in2 => ∃ (t : BinaryTree), GoodTree in1 in2 t)
