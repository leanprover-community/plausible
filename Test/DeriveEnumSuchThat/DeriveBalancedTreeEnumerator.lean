import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Test.DeriveArbitrarySuchThat.DeriveBalancedTreeGenerator

set_option guard_msgs.diff true

/--
info: Try this enumerator: instance : EnumSizedSuchThat BinaryTree (fun t_1 => balancedTree n_1 t_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (n_1 : Nat) : ExceptT Plausible.GenError Enumerator BinaryTree :=
      (match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match n_1 with
            | Nat.zero => return BinaryTree.Leaf
            | _ => MonadExcept.throw Plausible.Gen.genericFailure,
            match n_1 with
            | Nat.succ (Nat.zero) => return BinaryTree.Leaf
            | _ => MonadExcept.throw Plausible.Gen.genericFailure]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match n_1 with
            | Nat.zero => return BinaryTree.Leaf
            | _ => MonadExcept.throw Plausible.Gen.genericFailure,
            match n_1 with
            | Nat.succ (Nat.zero) => return BinaryTree.Leaf
            | _ => MonadExcept.throw Plausible.Gen.genericFailure,
            match n_1 with
            | Nat.succ n => do
              let l ← aux_enum initSize size' n;
              do
                let r ← aux_enum initSize size' n;
                do
                  let x ← Enum.enum;
                  return BinaryTree.Node x l r
            | _ => MonadExcept.throw Plausible.Gen.genericFailure])
    fun size => aux_enum size size n_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (t : BinaryTree) => balancedTree n t)
