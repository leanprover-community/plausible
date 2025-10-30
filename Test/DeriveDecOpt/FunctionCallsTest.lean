import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.EnumeratorCombinators
import Test.CommonDefinitions.FunctionCallInConclusion

open DecOpt

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_checker (fun n m => square_of n m)
