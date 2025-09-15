import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveChecker
import Test.CommonDefinitions.BinaryTree

open DecOpt

set_option guard_msgs.diff true

/--
info: Try this checker: instance : DecOpt (Between lo_1 x_1 hi_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (lo_1 : Nat) (x_1 : Nat) (hi_1 : Nat) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match hi_1 with
            | Nat.succ (Nat.succ m) =>
              match x_1 with
              | Nat.succ u_3 =>
                DecOpt.andOptList [DecOpt.decOpt (BEq.beq u_3 lo_1) initSize, DecOpt.decOpt (LE.le lo_1 m) initSize]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match hi_1 with
            | Nat.succ (Nat.succ m) =>
              match x_1 with
              | Nat.succ u_3 =>
                DecOpt.andOptList [DecOpt.decOpt (BEq.beq u_3 lo_1) initSize, DecOpt.decOpt (LE.le lo_1 m) initSize]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match hi_1 with
            | Nat.succ o =>
              match x_1 with
              | Nat.succ m => aux_dec initSize size' lo_1 m o
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
    fun size => aux_dec size size lo_1 x_1 hi_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (Between lo x hi)

/--
info: Try this checker: instance : DecOpt (BST lo_1 hi_1 t_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (lo_1 : Nat) (hi_1 : Nat) (t_1 : BinaryTree) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match t_1 with
            | BinaryTree.Leaf => Option.some Bool.true
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match t_1 with
            | BinaryTree.Leaf => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | BinaryTree.Node x l r =>
              DecOpt.andOptList
                [DecOpt.decOpt (Between lo_1 x hi_1) initSize,
                  DecOpt.andOptList [aux_dec initSize size' lo_1 x l, aux_dec initSize size' x hi_1 r]]
            | _ => Option.some Bool.false]
    fun size => aux_dec size size lo_1 hi_1 t_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (BST lo hi t)
