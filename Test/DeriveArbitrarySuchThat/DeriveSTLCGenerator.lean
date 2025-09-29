import Plausible.Gen
import Plausible.Chamelean.DecOpt
import Plausible.Arbitrary
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Test.DeriveArbitrary.DeriveSTLCTermTypeGenerators
import Test.DeriveDecOpt.DeriveSTLCChecker
import Plausible.Chamelean.DeriveConstrainedProducer
import Test.CommonDefinitions.STLCDefinitions

open Plausible
open ArbitrarySizedSuchThat

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (x : Nat) => lookup Γ x τ)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (τ : type) => lookup Γ x τ)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (t : type) => typing G e t)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (e : term) => typing G e t)

-- To sample from this generator and print out 10 successful examples using the `Repr`
-- instance for `term`, we can run the following:
-- #eval Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun e => typing [] e $ .Fun .Nat .Nat) 3) 3
