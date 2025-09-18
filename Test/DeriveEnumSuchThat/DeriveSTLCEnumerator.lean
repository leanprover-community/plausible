import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveChecker
import Test.CommonDefinitions.STLCDefinitions
import Test.DeriveEnum.DeriveSTLCTermTypeEnumerators

set_option guard_msgs.diff true

/--
info: Try this enumerator: instance : EnumSizedSuchThat Nat (fun x_1 => lookup Γ_1 x_1 τ_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (Γ_1 : List type) (τ_1 : type) :
      ExceptT Plausible.GenError Enumerator Nat :=
      (match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match Γ_1 with
            | List.cons τ Γ =>
              match DecOpt.decOpt (BEq.beq τ τ_1) initSize with
              | Except.ok Bool.true => return Nat.zero
              | _ => MonadExcept.throw Plausible.Gen.genericFailure
            | _ => MonadExcept.throw Plausible.Gen.genericFailure]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match Γ_1 with
            | List.cons τ Γ =>
              match DecOpt.decOpt (BEq.beq τ τ_1) initSize with
              | Except.ok Bool.true => return Nat.zero
              | _ => MonadExcept.throw Plausible.Gen.genericFailure
            | _ => MonadExcept.throw Plausible.Gen.genericFailure,
            match Γ_1 with
            | List.cons τ' Γ => do
              let n ← aux_enum initSize size' Γ τ_1;
              return Nat.succ n
            | _ => MonadExcept.throw Plausible.Gen.genericFailure])
    fun size => aux_enum size size Γ_1 τ_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (x : Nat) => lookup Γ x τ)

/--
info: Try this checker:
  instance : DecOpt (lookup Γ_1 x_1 τ_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (Γ_1 : List type) (x_1 : Nat) (τ_1 : type) :
      Except Plausible.GenError Bool :=
      (match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match x_1 with
            | Nat.zero =>
              match Γ_1 with
              | List.cons τ Γ => DecOpt.decOpt (BEq.beq τ τ_1) initSize
              | _ => Except.ok Bool.false
            | _ => Except.ok Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match x_1 with
            | Nat.zero =>
              match Γ_1 with
              | List.cons τ Γ => DecOpt.decOpt (BEq.beq τ τ_1) initSize
              | _ => Except.ok Bool.false
            | _ => Except.ok Bool.false,
            fun _ =>
            match x_1 with
            | Nat.succ n =>
              match Γ_1 with
              | List.cons τ' Γ => aux_dec initSize size' Γ n τ_1
              | _ => Except.ok Bool.false
            | _ => Except.ok Bool.false])
    fun size => aux_dec size size Γ_1 x_1 τ_1
-/
#guard_msgs(info, drop warning, whitespace:=lax) in
#derive_checker (lookup Γ x τ)


/--
info: Try this enumerator: instance : EnumSizedSuchThat type (fun τ_1 => lookup Γ_1 x_1 τ_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (Γ_1 : List type) (x_1 : Nat) :
      ExceptT Plausible.GenError Enumerator type :=
      (match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match x_1 with
            | Nat.zero =>
              match Γ_1 with
              | List.cons τ Γ => return τ
              | _ => MonadExcept.throw Plausible.Gen.genericFailure
            | _ => MonadExcept.throw Plausible.Gen.genericFailure]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match x_1 with
            | Nat.zero =>
              match Γ_1 with
              | List.cons τ Γ => return τ
              | _ => MonadExcept.throw Plausible.Gen.genericFailure
            | _ => MonadExcept.throw Plausible.Gen.genericFailure,
            match x_1 with
            | Nat.succ n =>
              match Γ_1 with
              | List.cons τ' Γ => do
                let τ_1 ← aux_enum initSize size' Γ n;
                return τ_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure
            | _ => MonadExcept.throw Plausible.Gen.genericFailure])
    fun size => aux_enum size size Γ_1 x_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (τ : type) => lookup Γ x τ)


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

/--
info: Try this enumerator: instance : EnumSizedSuchThat type (fun τ_1 => lookup Γ_1 x_1 τ_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (Γ_1 : List type) (x_1 : Nat) :
      ExceptT Plausible.GenError Enumerator type :=
      (match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match x_1 with
            | Nat.zero =>
              match Γ_1 with
              | List.cons τ Γ => return τ
              | _ => MonadExcept.throw Plausible.Gen.genericFailure
            | _ => MonadExcept.throw Plausible.Gen.genericFailure]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match x_1 with
            | Nat.zero =>
              match Γ_1 with
              | List.cons τ Γ => return τ
              | _ => MonadExcept.throw Plausible.Gen.genericFailure
            | _ => MonadExcept.throw Plausible.Gen.genericFailure,
            match x_1 with
            | Nat.succ n =>
              match Γ_1 with
              | List.cons τ' Γ => do
                let τ_1 ← aux_enum initSize size' Γ n;
                return τ_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure
            | _ => MonadExcept.throw Plausible.Gen.genericFailure])
    fun size => aux_enum size size Γ_1 x_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (τ : type) => lookup Γ x τ)

/--
info: Try this enumerator: instance : EnumSizedSuchThat type (fun τ_1 => typing Γ_1 e_1 τ_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (Γ_1 : List type) (e_1 : term) :
      ExceptT Plausible.GenError Enumerator type :=
      (match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match e_1 with
            | term.Const n => return type.Nat
            | _ => MonadExcept.throw Plausible.Gen.genericFailure,
            match e_1 with
            | term.Var x => do
              let τ_1 ← EnumSizedSuchThat.enumSizedST (fun τ_1 => lookup Γ_1 x τ_1) initSize;
              return τ_1
            | _ => MonadExcept.throw Plausible.Gen.genericFailure]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match e_1 with
            | term.Const n => return type.Nat
            | _ => MonadExcept.throw Plausible.Gen.genericFailure,
            match e_1 with
            | term.Var x => do
              let τ_1 ← EnumSizedSuchThat.enumSizedST (fun τ_1 => lookup Γ_1 x τ_1) initSize;
              return τ_1
            | _ => MonadExcept.throw Plausible.Gen.genericFailure,
            match e_1 with
            | term.Add e1 e2 =>
              match DecOpt.decOpt (typing Γ_1 e1 (type.Nat)) initSize with
              | Except.ok Bool.true =>
                match DecOpt.decOpt (typing Γ_1 e2 (type.Nat)) initSize with
                | Except.ok Bool.true => return type.Nat
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure
            | _ => MonadExcept.throw Plausible.Gen.genericFailure,
            match e_1 with
            | term.Abs τ1 e => do
              let τ2 ← aux_enum initSize size' (List.cons τ1 Γ_1) e;
              return type.Fun τ1 τ2
            | _ => MonadExcept.throw Plausible.Gen.genericFailure,
            match e_1 with
            | term.App e1 e2 => do
              let τ1 ← aux_enum initSize size' Γ_1 e2;
              do
                let τ_1 ← Enum.enum;
                match DecOpt.decOpt (typing Γ_1 e1 (type.Fun τ1 τ_1)) initSize with
                  | Except.ok Bool.true => return τ_1
                  | _ => MonadExcept.throw Plausible.Gen.genericFailure
            | _ => MonadExcept.throw Plausible.Gen.genericFailure])
    fun size => aux_enum size size Γ_1 e_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (τ : type) => typing Γ e τ)

/--
info: Try this enumerator: instance : EnumSizedSuchThat term (fun e_1 => typing Γ_1 e_1 τ_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (Γ_1 : List type) (τ_1 : type) :
      ExceptT Plausible.GenError Enumerator term :=
      (match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match τ_1 with
            | type.Nat => do
              let n ← Enum.enum;
              return term.Const n
            | _ => MonadExcept.throw Plausible.Gen.genericFailure,
            do
            let x ← EnumSizedSuchThat.enumSizedST (fun x => lookup Γ_1 x τ_1) initSize;
            return term.Var x]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match τ_1 with
            | type.Nat => do
              let n ← Enum.enum;
              return term.Const n
            | _ => MonadExcept.throw Plausible.Gen.genericFailure,
            do
            let x ← EnumSizedSuchThat.enumSizedST (fun x => lookup Γ_1 x τ_1) initSize;
            return term.Var x,
            match τ_1 with
            | type.Nat => do
              let e1 ← aux_enum initSize size' Γ_1 (type.Nat);
              do
                let e2 ← aux_enum initSize size' Γ_1 (type.Nat);
                return term.Add e1 e2
            | _ => MonadExcept.throw Plausible.Gen.genericFailure,
            match τ_1 with
            | type.Fun τ1 τ2 => do
              let e ← aux_enum initSize size' (List.cons τ1 Γ_1) τ2;
              return term.Abs τ1 e
            | _ => MonadExcept.throw Plausible.Gen.genericFailure,
            do
            let e2 ← Enum.enum;
            do
              let τ1 ← EnumSizedSuchThat.enumSizedST (fun τ1 => typing Γ_1 e2 τ1) initSize;
              do
                let e1 ← aux_enum initSize size' Γ_1 (type.Fun τ1 τ_1);
                return term.App e1 e2])
    fun size => aux_enum size size Γ_1 τ_1
-/
#guard_msgs(info, drop warning, whitespace:=lax) in
#derive_enumerator (fun (e : term) => typing Γ e τ)
