import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.EnumeratorCombinators
import Test.DeriveDecOpt.DeriveBSTChecker
import Test.DeriveEnumSuchThat.DeriveSTLCEnumerator
import Test.CommonDefinitions.STLCDefinitions

open DecOpt

set_option guard_msgs.diff true

/--
info: Try this checker:
  instance : DecOpt (typing Γ_1 e_1 τ_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (Γ_1 : List type) (e_1 : term) (τ_1 : type) :
      Except Plausible.GenError Bool :=
      (match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match τ_1 with
            | type.Nat =>
              match e_1 with
              | term.Const n => Except.ok Bool.true
              | _ => Except.ok Bool.false
            | _ => Except.ok Bool.false,
            fun _ =>
            match e_1 with
            | term.Var x => DecOpt.decOpt (lookup Γ_1 x τ_1) initSize
            | _ => Except.ok Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match τ_1 with
            | type.Nat =>
              match e_1 with
              | term.Const n => Except.ok Bool.true
              | _ => Except.ok Bool.false
            | _ => Except.ok Bool.false,
            fun _ =>
            match e_1 with
            | term.Var x => DecOpt.decOpt (lookup Γ_1 x τ_1) initSize
            | _ => Except.ok Bool.false,
            fun _ =>
            match τ_1 with
            | type.Nat =>
              match e_1 with
              | term.Add e1 e2 =>
                DecOpt.andOptList [aux_dec initSize size' Γ_1 e1 (type.Nat), aux_dec initSize size' Γ_1 e2 (type.Nat)]
              | _ => Except.ok Bool.false
            | _ => Except.ok Bool.false,
            fun _ =>
            match τ_1 with
            | type.Fun u_3 τ2 =>
              match e_1 with
              | term.Abs τ1 e =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_3 τ1) initSize, aux_dec initSize size' (List.cons τ1 Γ_1) e τ2]
              | _ => Except.ok Bool.false
            | _ => Except.ok Bool.false,
            fun _ =>
            match e_1 with
            | term.App e1 e2 =>
              EnumeratorCombinators.enumeratingOpt (EnumSizedSuchThat.enumSizedST (fun τ1 => typing Γ_1 e2 τ1) initSize)
                (fun τ1 => aux_dec initSize size' Γ_1 e1 (type.Fun τ1 τ_1)) (min 2 initSize)
            | _ => Except.ok Bool.false])
    fun size => aux_dec size size Γ_1 e_1 τ_1
-/
#guard_msgs(info, drop warning, whitespace:=lax) in
#derive_checker (typing Γ e τ)
