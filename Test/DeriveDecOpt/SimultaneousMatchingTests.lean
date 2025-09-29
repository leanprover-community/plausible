import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveChecker
import Test.DeriveDecOpt.DeriveBSTChecker
import Test.CommonDefinitions.ListRelations

open DecOpt

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
#derive_checker (InList x l)

#guard_msgs(drop info, drop warning) in
#derive_checker (MinOk l a)

#guard_msgs(drop info, drop warning) in
#derive_checker (MinEx n l a)
