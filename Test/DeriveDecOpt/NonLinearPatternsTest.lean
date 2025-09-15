import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveChecker
import Test.DeriveDecOpt.DeriveBSTChecker
import Test.DeriveArbitrarySuchThat.NonLinearPatternsTest

open DecOpt

set_option guard_msgs.diff true

/--
info: Try this checker: instance : DecOpt (GoodTree in1_1 in2_1 t_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (in1_1 : Nat) (in2_1 : Nat) (t_1 : BinaryTree) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match t_1 with
            | BinaryTree.Leaf => DecOpt.decOpt (BEq.beq in1_1 in2_1) initSize
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match t_1 with
            | BinaryTree.Leaf => DecOpt.decOpt (BEq.beq in1_1 in2_1) initSize
            | _ => Option.some Bool.false,
            ]
    fun size => aux_dec size size in1_1 in2_1 t_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (GoodTree in1 in2 t)
