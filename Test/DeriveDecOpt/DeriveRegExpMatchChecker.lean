import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveEnum
import Test.DeriveArbitrary.DeriveRegExpGenerator
import Test.DeriveArbitrarySuchThat.DeriveRegExpMatchGenerator
import Test.DeriveEnum.DeriveRegExpEnumerator
import Test.DeriveEnumSuchThat.DeriveRegExpMatchEnumerator

import Plausible.Attr


open DecOpt

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_checker (fun s r0 => ExpMatch s r0)
