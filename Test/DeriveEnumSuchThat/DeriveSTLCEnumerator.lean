import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveChecker
import Test.CommonDefinitions.STLCDefinitions
import Test.DeriveEnum.DeriveSTLCTermTypeEnumerators

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun Γ τ => ∃ (x : Nat), lookup Γ x τ)

#guard_msgs(drop info, drop warning) in
derive_checker (fun Γ x τ => lookup Γ x τ)

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun Γ x => ∃ (τ : type), lookup Γ x τ)


mutual
  /-- Enumerates types `τ` such that `typing Γ e τ` holds.
      We need to manually add an instance of the `DecOpt` typeclass since Lean doesn't support
      mutually recursively typeclass instances currently. -/
  partial def enumTyping (Γ_1 : List type) (e_1 : term) : Nat → ExceptT Plausible.GenError Enumerator type :=
    let rec aux_enum (initSize : Nat) (size : Nat) (Γ_1 : List type) (e_1 : term) : ExceptT Plausible.GenError Enumerator type :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match e_1 with
            | term.Const _ => return type.Nat
            | _ => throw Plausible.Gen.genericFailure,
            match e_1 with
            | term.Var x => do
              let τ_1 ← EnumSizedSuchThat.enumSizedST (fun τ_1 => lookup Γ_1 x τ_1) initSize;
              return τ_1
            | _ => throw Plausible.Gen.genericFailure]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match e_1 with
            | term.Const _ => return type.Nat
            | _ => throw Plausible.Gen.genericFailure,
            match e_1 with
            | term.Var x => do
              let τ_1 ← EnumSizedSuchThat.enumSizedST (fun τ_1 => lookup Γ_1 x τ_1) initSize;
              return τ_1
            | _ => throw Plausible.Gen.genericFailure,
            match e_1 with
            | term.Add e1 e2 =>
              match checkTyping Γ_1 e1 (type.Nat) size' with
              | .ok Bool.true =>
                match checkTyping Γ_1 e2 (type.Nat) size' with
                | .ok Bool.true => return type.Nat
                | _ => throw Plausible.Gen.genericFailure
              | _ => throw Plausible.Gen.genericFailure
            | _ => throw Plausible.Gen.genericFailure,
            match e_1 with
            | term.Abs τ1 e => do
              let τ2 ← aux_enum initSize size' (List.cons τ1 Γ_1) e;
              return type.Fun τ1 τ2
            | _ => throw Plausible.Gen.genericFailure,
            match e_1 with
            | term.App e1 e2 => do
              let τ1 ← aux_enum initSize size' Γ_1 e2;
              do
                let τ_1 ← Enum.enum;
                match checkTyping Γ_1 e1 (type.Fun τ1 τ_1) size' with
                  | .ok Bool.true => return τ_1
                  | _ => throw Plausible.Gen.genericFailure
            | _ => throw Plausible.Gen.genericFailure]

    fun size => aux_enum size size Γ_1 e_1

  partial def checkTyping (Γ_1 : List type) (e_1 : term) (τ_1 : type) : Nat → Except Plausible.GenError Bool :=
    let rec aux_dec (initSize : Nat) (size : Nat) (Γ_1 : List type) (e_1 : term) (τ_1 : type) : Except Plausible.GenError Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match τ_1 with
            | type.Nat =>
              match e_1 with
              | term.Const _ => .ok Bool.true
              | _ => .ok Bool.false
            | _ => .ok Bool.false,
            fun _ =>
            match e_1 with
            | term.Var x => DecOpt.decOpt (lookup Γ_1 x τ_1) initSize
            | _ => .ok Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match τ_1 with
            | type.Nat =>
              match e_1 with
              | term.Const _ => .ok Bool.true
              | _ => .ok Bool.false
            | _ => .ok Bool.false,
            fun _ =>
            match e_1 with
            | term.Var x => DecOpt.decOpt (lookup Γ_1 x τ_1) initSize
            | _ => .ok Bool.false,
            fun _ =>
            match τ_1 with
            | type.Fun u_3 τ2 =>
              match e_1 with
              | term.Abs τ1 e =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_3 τ1) initSize, aux_dec initSize size' (List.cons τ1 Γ_1) e τ2]
              | _ => .ok Bool.false
            | _ => .ok Bool.false,
            fun _ =>
            match e_1 with
            | term.App e1 e2 =>
              EnumeratorCombinators.enumeratingOpt (enumTyping Γ_1 e2 initSize)
                (fun τ1 => aux_dec initSize size' Γ_1 e1 (type.Fun τ1 τ_1)) initSize
            | _ => .ok Bool.false]

      fun size => aux_dec size size Γ_1 e_1 τ_1

end

/-- We need to manually add an instance of the `DecOpt` typeclass since Lean doesn't support
    mutually recursively typeclass instances currently.

    (The derived checker for `typing Γ e τ` relies on the derived enumerator for `fun τ => typing Γ e τ`,
    while this enumerator relies on the checker for `typing Γ e τ`.) -/
instance : DecOpt (typing Γ_1 e_1 τ_1) where
  decOpt := checkTyping Γ_1 e_1 τ_1

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun Γ x => ∃ (τ : type), lookup Γ x τ)

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun Γ e => ∃ (τ : type), typing Γ e τ)

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun Γ τ => ∃ (e : term), typing Γ e τ)
