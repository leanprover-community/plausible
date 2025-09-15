import Plausible.Arbitrary
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Test.CommonDefinitions.FunctionCallInConclusion

open Plausible
open DecOpt

set_option guard_msgs.diff true

/--
info: Try this generator: instance : ArbitrarySizedSuchThat Nat (fun n_1 => square_of n_1 m_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (m_1 : Nat) : OptionT Plausible.Gen Nat :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1, do
              let n_1 ← Plausible.Arbitrary.arbitrary;
              do
                let m_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun m_1 => Eq m_1 (HMul.hMul n_1 n_1)) initSize;
                return n_1)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, do
              let n_1 ← Plausible.Arbitrary.arbitrary;
              do
                let m_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun m_1 => Eq m_1 (HMul.hMul n_1 n_1)) initSize;
                return n_1),
            ]
    fun size => aux_arb size size m_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (n : Nat) => square_of n m)
