import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.EnumeratorCombinators
import Test.CommonDefinitions.Permutation
import Test.DeriveEnumSuchThat.DerivePermutationEnumerator


/--
info: Try this checker: instance : DecOpt (Permutation l_1 l'_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (l_1 : List Nat) (l'_1 : List Nat) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match l'_1 with
            | List.nil =>
              match l_1 with
              | List.nil => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match l'_1 with
            | List.cons u_2 (List.cons u_3 u_4) =>
              match l_1 with
              | List.cons y (List.cons x l) =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_2 x) initSize,
                    DecOpt.andOptList [DecOpt.decOpt (BEq.beq u_4 l) initSize, DecOpt.decOpt (BEq.beq u_3 y) initSize]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match l'_1 with
            | List.nil =>
              match l_1 with
              | List.nil => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match l'_1 with
            | List.cons u_2 (List.cons u_3 u_4) =>
              match l_1 with
              | List.cons y (List.cons x l) =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_2 x) initSize,
                    DecOpt.andOptList [DecOpt.decOpt (BEq.beq u_4 l) initSize, DecOpt.decOpt (BEq.beq u_3 y) initSize]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match l'_1 with
            | List.cons u_2 l' =>
              match l_1 with
              | List.cons x l => DecOpt.andOptList [DecOpt.decOpt (BEq.beq u_2 x) initSize, aux_dec initSize size' l l']
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            EnumeratorCombinators.enumeratingOpt (EnumSizedSuchThat.enumSizedST (fun l' => Permutation l_1 l') initSize)
              (fun l' => aux_dec initSize size' l' l'_1) (min 2 initSize)]
    fun size => aux_dec size size l_1 l'_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (Permutation l l')


-- Example: to run the derived checker, you can uncomment the following
-- def l := [1, 2, 3, 4]
-- def l' := [2, 1, 3, 4]
-- #eval (DecOpt.decOpt (Permutation l l')) 2
