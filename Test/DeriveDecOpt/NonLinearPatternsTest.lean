import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveChecker
import Test.DeriveDecOpt.DeriveBSTChecker
import Test.DeriveArbitrarySuchThat.NonLinearPatternsTest

open DecOpt

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_checker (fun in1 in2 t => GoodTree in1 in2 t)
