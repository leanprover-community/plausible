
import Plausible.Gen
import Plausible.Arbitrary
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Test.CommonDefinitions.BinaryTree

open Plausible
open ArbitrarySizedSuchThat

set_option guard_msgs.diff true

-- `balancedTree n t` describes whether the tree `t` of height `n` is *balancedTree*, i.e. every path through the tree has length either `n` or `n-1`. -/
inductive balancedTree : Nat → BinaryTree → Prop where
  | B0 : balancedTree .zero BinaryTree.Leaf
  | B1 : balancedTree (.succ .zero) BinaryTree.Leaf
  | BS : ∀ n x l r,
    balancedTree n l → balancedTree n r →
    balancedTree (.succ n) (BinaryTree.Node x l r)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat BinaryTree (fun t_1 => balancedTree n_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (n_1 : Nat) : Plausible.Gen BinaryTree :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match n_1 with
              | Nat.zero => return BinaryTree.Leaf
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match n_1 with
              | Nat.succ (Nat.zero) => return BinaryTree.Leaf
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match n_1 with
              | Nat.zero => return BinaryTree.Leaf
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match n_1 with
              | Nat.succ (Nat.zero) => return BinaryTree.Leaf
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size',
              match n_1 with
              | Nat.succ n => do
                let l ← aux_arb initSize size' n;
                do
                  let r ← aux_arb initSize size' n;
                  do
                    let x ← Plausible.Arbitrary.arbitrary;
                    return BinaryTree.Node x l r
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size n_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (t : BinaryTree) => balancedTree n t)
