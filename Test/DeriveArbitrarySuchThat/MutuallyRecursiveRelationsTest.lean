
import Plausible.Arbitrary
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer

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

    Note that the instance of `ArbitrarySizedSuchThat` for `Odd` below (produced by `#derive_generator`)
    will shadow this one -- it takes precedence over this dummy instance. -/
instance : ArbitrarySizedSuchThat Nat (fun n => Odd n) where
  arbitrarySizedST (_ : Nat) := return 1

/--
info: Try this generator: instance : ArbitrarySizedSuchThat Nat (fun n_1 => Even n_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) : Plausible.Gen Nat :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1, return Nat.zero),
            (1, do
              let n ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Odd n) initSize;
              return Nat.succ n)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1, return Nat.zero),
            (1, do
              let n ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Odd n) initSize;
              return Nat.succ n),
            ])
    fun size => aux_arb size size
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (n : Nat) => Even n)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat Nat (fun n_1 => Odd n_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) : Plausible.Gen Nat :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1, do
              let n ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Even n) initSize;
              return Nat.succ n)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1, do
              let n ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Even n) initSize;
              return Nat.succ n),
            ])
    fun size => aux_arb size size
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (n : Nat) => Odd n)
