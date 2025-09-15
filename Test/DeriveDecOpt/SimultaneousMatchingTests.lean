import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveChecker
import Test.DeriveDecOpt.DeriveBSTChecker
import Test.CommonDefinitions.ListRelations

open DecOpt

set_option guard_msgs.diff true

/--
info: Try this checker: instance : DecOpt (InList x_1 l_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (x_1 : Nat) (l_1 : List Nat) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match l_1 with
            | List.cons u_2 l => DecOpt.decOpt (BEq.beq u_2 x_1) initSize
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match l_1 with
            | List.cons u_2 l => DecOpt.decOpt (BEq.beq u_2 x_1) initSize
            | _ => Option.some Bool.false,
            fun _ =>
            match l_1 with
            | List.cons y l => aux_dec initSize size' x_1 l
            | _ => Option.some Bool.false]
    fun size => aux_dec size size x_1 l_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (InList x l)

/--
info: Try this checker: instance : DecOpt (MinOk l_1 a_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (l_1 : List Nat) (a_1 : List Nat) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match a_1 with
            | List.nil =>
              match l_1 with
              | List.nil => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match a_1 with
            | List.nil =>
              match l_1 with
              | List.nil => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match a_1 with
            | List.cons x l' => DecOpt.andOptList [aux_dec initSize size' l_1 l', DecOpt.decOpt (InList x l_1) initSize]
            | _ => Option.some Bool.false]
    fun size => aux_dec size size l_1 a_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (MinOk l a)


/--
info: Try this checker: instance : DecOpt (MinEx n_1 l_1 a_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (n_1 : Nat) (l_1 : List Nat) (a_1 : List Nat) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match a_1 with
            | List.nil =>
              match l_1 with
              | List.nil =>
                match n_1 with
                | Nat.zero => Option.some Bool.true
                | _ => Option.some Bool.false
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match a_1 with
            | List.nil =>
              match l_1 with
              | List.nil =>
                match n_1 with
                | Nat.zero => Option.some Bool.true
                | _ => Option.some Bool.false
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match a_1 with
            | List.cons x l' =>
              match n_1 with
              | Nat.succ n => DecOpt.andOptList [DecOpt.decOpt (InList x l_1) initSize, aux_dec initSize size' n l_1 l']
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
    fun size => aux_dec size size n_1 l_1 a_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (MinEx n l a)
