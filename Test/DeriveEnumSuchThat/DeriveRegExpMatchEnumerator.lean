import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Test.DeriveArbitrarySuchThat.DeriveRegExpMatchGenerator

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
#derive_enumerator (fun (s : List Nat) => ExpMatch s r0)

-- To sample from this enumerator, we can run the following:
-- #eval runSizedEnum (EnumSizedSuchThat.enumSizedST (fun s => ExpMatch s r)) 1
