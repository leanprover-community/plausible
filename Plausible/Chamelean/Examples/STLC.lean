import Plausible.Chamelean.Examples.ExampleInductiveRelations
import Plausible.Chamelean.OptionTGen
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.GeneratorCombinators
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.DeriveArbitrary
import Plausible.Arbitrary
import Plausible.Chamelean.DeriveEnum

import Plausible.Gen
import Plausible.Sampleable

open Plausible
open OptionTGen
open GeneratorCombinators

-------------------------------------------------------------------------
-- Unconstrained generators
--------------------------------------------------------------------------

deriving instance Arbitrary, Enum for type, term

-------------------------------------------------------------------------
-- Some example `DecOpt` checkers
--------------------------------------------------------------------------

/-- A handwritten checker which checks `lookup Γ x τ`
  (modelled after the automatically derived checker produced by QuickChick). -/
def checkLookup (Γ : List type) (x : Nat) (τ : type) : Nat → Option Bool :=
  let rec aux_arb (initSize : Nat) (size : Nat) (Γ : List type) (x : Nat) (τ : type) : Option Bool :=
    match size with
    | .zero =>
      DecOpt.checkerBacktrack [
        (fun _ =>
          match x with
          | .zero =>
            match Γ with
            | [] => some false
            | t :: _ => DecOpt.andOptList [DecOpt.decOpt (τ = t) initSize]
          | .succ _ => some false),
        fun _ => none
      ]
    | .succ size' =>
      DecOpt.checkerBacktrack [
        (fun _ =>
          match Γ with
          | [] => some false
          | t :: _ => DecOpt.andOptList [DecOpt.decOpt (τ = t) initSize]),
        (fun _ =>
          match x with
          | .zero => some false
          | .succ x' =>
            match Γ with
            | [] => some false
            | _τ' :: Γ' => DecOpt.andOptList [aux_arb initSize size' Γ' x' τ])
      ]
  fun size => aux_arb size size Γ x τ

/-- `lookup Γ x τ` is an instance of the `DecOpt` typeclass which describes
     partially decidable propositions -/
instance : DecOpt (lookup Γ x τ) where
  decOpt := checkLookup Γ x τ

/-- `EnumSizedSuchThat` instance for enumerating types that satisfy `lookup` -/
instance : EnumSizedSuchThat type (fun τ_1 => lookup Γ_1 x_1 τ_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (Γ_1 : List type) (x_1 : Nat) : OptionT Enumerator type :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match x_1 with
            | Nat.zero =>
              match Γ_1 with
              | List.cons τ _ => return τ
              | _ => OptionT.fail
            | _ => OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match x_1 with
            | Nat.zero =>
              match Γ_1 with
              | List.cons τ _ => return τ
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match x_1 with
            | Nat.succ n =>
              match Γ_1 with
              | List.cons _ Γ => do
                let τ_1 ← aux_enum initSize size' Γ n;
                return τ_1
              | _ => OptionT.fail
            | _ => OptionT.fail]
    fun size => aux_enum size size Γ_1 x_1

mutual
  /-- Enumerates types `τ` such that `typing Γ e τ` holds -/
  partial def enumTyping (Γ_1 : List type) (e_1 : term) : Nat → OptionT Enumerator type :=
    let rec aux_enum (initSize : Nat) (size : Nat) (Γ_1 : List type) (e_1 : term) : OptionT Enumerator type :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match e_1 with
            | term.Const _ => return type.Nat
            | _ => OptionT.fail,
            match e_1 with
            | term.Var x => do
              let τ_1 ← EnumSizedSuchThat.enumSizedST (fun τ_1 => lookup Γ_1 x τ_1) initSize;
              return τ_1
            | _ => OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match e_1 with
            | term.Const _ => return type.Nat
            | _ => OptionT.fail,
            match e_1 with
            | term.Var x => do
              let τ_1 ← EnumSizedSuchThat.enumSizedST (fun τ_1 => lookup Γ_1 x τ_1) initSize;
              return τ_1
            | _ => OptionT.fail,
            match e_1 with
            | term.Add e1 e2 =>
              match checkTyping Γ_1 e1 (type.Nat) size' with
              | Option.some Bool.true =>
                match checkTyping Γ_1 e2 (type.Nat) size' with
                | Option.some Bool.true => return type.Nat
                | _ => OptionT.fail
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match e_1 with
            | term.Abs τ1 e => do
              let τ2 ← aux_enum initSize size' (List.cons τ1 Γ_1) e;
              return type.Fun τ1 τ2
            | _ => OptionT.fail,
            match e_1 with
            | term.App e1 e2 => do
              let τ1 ← aux_enum initSize size' Γ_1 e2;
              do
                let τ_1 ← Enum.enum;
                match checkTyping Γ_1 e1 (type.Fun τ1 τ_1) size' with
                  | Option.some Bool.true => return τ_1
                  | _ => OptionT.fail
            | _ => OptionT.fail]

    fun size => aux_enum size size Γ_1 e_1

  /-- A handwritten checker which checks `typing Γ e τ`, ignoring the case for `App`
      (based on the derived checker produced by QuickChick) -/
  partial def checkTyping (Γ_1 : List type) (e_1 : term) (τ_1 : type) : Nat → Option Bool :=
    let rec aux_dec (initSize : Nat) (size : Nat) (Γ_1 : List type) (e_1 : term) (τ_1 : type) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match τ_1 with
            | type.Nat =>
              match e_1 with
              | term.Const _ => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match e_1 with
            | term.Var x => DecOpt.decOpt (lookup Γ_1 x τ_1) initSize
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match τ_1 with
            | type.Nat =>
              match e_1 with
              | term.Const _ => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match e_1 with
            | term.Var x => DecOpt.decOpt (lookup Γ_1 x τ_1) initSize
            | _ => Option.some Bool.false,
            fun _ =>
            match τ_1 with
            | type.Fun u_3 τ2 =>
              match e_1 with
              | term.Abs τ1 e =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_3 τ1) initSize, aux_dec initSize size' (List.cons τ1 Γ_1) e τ2]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match e_1 with
            | term.App e1 e2 =>
              EnumeratorCombinators.enumeratingOpt (enumTyping Γ_1 e2 initSize)
                (fun τ1 => aux_dec initSize size' Γ_1 e1 (type.Fun τ1 τ_1)) initSize
            | _ => Option.some Bool.false]

      fun size => aux_dec size size Γ_1 e_1 τ_1
end


-------------------------------------------------------------------------
-- Constrained generators
--------------------------------------------------------------------------

/-- Generator which produces `x : Nat` such that `lookup Γ x τ` holds -/
def genLookup (Γ : List type) (τ : type) : Nat → OptionT Plausible.Gen Nat :=
  let rec aux_arb (initSize : Nat) (size : Nat) (Γ_0 : List type) (τ_0 : type) : OptionT Plausible.Gen Nat :=
    match size with
    | Nat.zero =>
      OptionTGen.backtrack
        [(1,
            OptionTGen.thunkGen
              (fun _ =>
                match Γ_0 with
                | [] => OptionT.fail
                | τ :: _ =>
                  match DecOpt.decOpt (τ_0 = τ) initSize with
                  | some true => pure 0
                  | _ => OptionT.fail)),
          (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
    | Nat.succ size' =>
      OptionTGen.backtrack
        [(1,
            OptionTGen.thunkGen
              (fun _ =>
                match Γ_0 with
                | [] => OptionT.fail
                | τ :: _ =>
                  match DecOpt.decOpt (τ_0 = τ) initSize with
                  | some true => pure 0
                  | _ => OptionT.fail)),
          (Nat.succ size',
            OptionTGen.thunkGen
              (fun _ =>
                match Γ_0 with
                | [] => OptionT.fail
                | _ :: Γ => do
                  let x ← aux_arb initSize size' Γ τ_0
                  return Nat.succ x))]
  fun size => aux_arb size size Γ τ

/-- `lookup Γ x τ` is an instance of the `ArbitrarySizedSuchThat` typeclass,
    which describes generators for values that satisfy a proposition -/
instance : ArbitrarySizedSuchThat Nat (fun x => lookup Γ x τ) where
  arbitrarySizedST := genLookup Γ τ

/-- Generator which produces well-typed terms `e` such that `typing Γ e τ` holds -/
def genTyping (G_ : List type) (t_ : type) : Nat → OptionT Plausible.Gen term :=
  let rec aux_arb (initSize : Nat) (size : Nat) (G_0 : List type) (t_0 : type) : OptionT Plausible.Gen term :=
    match size with
    | Nat.zero =>
      OptionTGen.backtrack
        [(1,
            OptionTGen.thunkGen
              (fun _ =>
                match t_0 with
                | .Nat => do
                  let n ← SampleableExt.interpSample Nat
                  return term.Const n
                | .Fun _ _ => OptionT.fail)),
          (1,
            OptionTGen.thunkGen
              (fun _ => do
                let x ← ArbitrarySuchThat.arbitraryST (fun x => lookup G_0 x t_0)
                return term.Var x)),
          (1, OptionTGen.thunkGen (fun _ => OptionT.fail))]
    | Nat.succ size' =>
      OptionTGen.backtrack
        [(1,
            OptionTGen.thunkGen
              (fun _ =>
                match t_0 with
                | type.Nat => do
                  let n ← SampleableExt.interpSample Nat
                  return term.Const n
                | _ => OptionT.fail)),
          (Nat.succ size',
            OptionTGen.thunkGen
              (fun _ =>
                match t_0 with
                | type.Nat => do
                  let e1 ← aux_arb initSize size' G_0 type.Nat
                  let e2 ← aux_arb initSize size' G_0 type.Nat
                  return term.Add e1 e2
                | _ => OptionT.fail)),
          (Nat.succ size',
            OptionTGen.thunkGen
              (fun _ =>
                match t_0 with
                | type.Fun t1 t2 => do
                  let e ← aux_arb initSize size' (t1 :: G_0) t2
                  return term.Abs t1 e
                | _ => OptionT.fail)),
          (1,
            OptionTGen.thunkGen
              (fun _ => do
                let x ← ArbitrarySuchThat.arbitraryST (fun x => lookup G_0 x t_0)
                return term.Var x)),
          (Nat.succ size',
            OptionTGen.thunkGen
              (fun _ => do
                let t1 ← Arbitrary.arbitrary
                let e2 ← aux_arb initSize size' G_0 t1
                let e1 ← aux_arb initSize size' G_0 (type.Fun t1 t_0)
                return term.App (.Abs .Nat e1) e2))]
  fun size => aux_arb size size G_ t_

/- `typing Γ e τ` is an instance of the `ArbitrarySizedSuchThat` typeclass,
    which describes generators for values that satisfy a proposition -/
instance : ArbitrarySizedSuchThat term (fun e => typing Γ e τ) where
  arbitrarySizedST := genTyping Γ τ
