import Plausible.Arbitrary
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Test.CommonDefinitions.FunctionCallInConclusion

open Plausible
open DecOpt

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (n : Nat) => square_of n m)
