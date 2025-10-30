import Plausible.Gen
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.DeriveChecker
import Test.CommonDefinitions.ListRelations
import Test.DeriveDecOpt.SimultaneousMatchingTests

open Plausible
open ArbitrarySizedSuchThat

set_option guard_msgs.diff true


#guard_msgs(drop info, drop warning) in
derive_generator (fun x => ∃ (l : List Nat), InList x l)


#guard_msgs(drop info, drop warning) in
derive_generator (fun a => ∃ (l: List Nat), MinOk l a)

#guard_msgs(drop info, drop warning) in
derive_generator (fun n l' => ∃ (l : List Nat), MinEx n l l')

#guard_msgs(drop info, drop warning) in
derive_generator (fun x l' => ∃ (l : List Nat), MinEx3 x l l')

#guard_msgs(drop info, drop warning) in
derive_generator (fun x l => ∃ (l' : List Nat), MinEx2 x l l')

#guard_msgs(drop info, drop warning) in
derive_generator (fun x l' => ∃ (l : List Nat), MinEx2 x l l')
