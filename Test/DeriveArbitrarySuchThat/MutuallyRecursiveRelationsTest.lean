/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/

import Plausible.Arbitrary
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Gen

set_option guard_msgs.diff true

mutual
  inductive Even : Nat → Prop where
    | zero_is_even : Even .zero
    | succ_of_odd_is_even : ∀ n : Nat, Odd n → Even (.succ n)

  inductive Odd : Nat → Prop where
    | succ_of_even_is_odd : ∀ n : Nat, Even n → Odd (.succ n)
end

/-- To make the derived generators below compile, we need to
    manually add a dummy instance of `ArbitrarySizedSuchThat` for one of the relations, since Lean doesn't support
    mutually recursively typeclass instances currently.

    Note that the instance of `ArbitrarySizedSuchThat` for `Odd` below (produced by `derive_generator`)
    will shadow this one -- it takes precedence over this dummy instance.


    Note from Segev: This does not work, it remembers the old instance from when it was defined. -/
instance : ArbitrarySizedSuchThat Nat (fun n => Odd n) where
  arbitrarySizedST (_ : Nat) := return 1

#guard_msgs(drop info, drop warning) in
derive_generator ∃ (n : Nat), Even n

#guard_msgs(drop info, drop warning) in
derive_generator ∃ (n : Nat), Odd n
