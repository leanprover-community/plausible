import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Test.CommonDefinitions.Permutation

#guard_msgs(drop info, drop warning) in
derive_generator (fun l' => ∃ (l : List Nat), Permutation l l')

#guard_msgs(drop info, drop warning) in
derive_generator (fun l' => ∃ (l : List Nat), Permutation l' l)
