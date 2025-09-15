import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveChecker
import Test.DeriveDecOpt.DeriveBSTChecker
import Test.DeriveArbitrarySuchThat.DeriveBalancedTreeGenerator

open DecOpt

set_option guard_msgs.diff true

/--
info: Try this checker: instance : DecOpt (balancedTree n_1 t_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (n_1 : Nat) (t_1 : BinaryTree) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match t_1 with
            | BinaryTree.Leaf =>
              match n_1 with
              | Nat.zero => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | BinaryTree.Leaf =>
              match n_1 with
              | Nat.succ (Nat.zero) => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match t_1 with
            | BinaryTree.Leaf =>
              match n_1 with
              | Nat.zero => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | BinaryTree.Leaf =>
              match n_1 with
              | Nat.succ (Nat.zero) => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | BinaryTree.Node x l r =>
              match n_1 with
              | Nat.succ n => DecOpt.andOptList [aux_dec initSize size' n l, aux_dec initSize size' n r]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
    fun size => aux_dec size size n_1 t_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (balancedTree n t)
