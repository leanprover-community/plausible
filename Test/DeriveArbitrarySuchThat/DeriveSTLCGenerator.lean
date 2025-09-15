import Plausible.Gen
import Plausible.Chamelean.OptionTGen
import Plausible.Chamelean.DecOpt
import Plausible.Arbitrary
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Test.DeriveArbitrary.DeriveSTLCTermTypeGenerators
import Test.DeriveDecOpt.DeriveSTLCChecker
import Plausible.Chamelean.DeriveConstrainedProducer
import Test.CommonDefinitions.STLCDefinitions

open Plausible
open ArbitrarySizedSuchThat OptionTGen

set_option guard_msgs.diff true

/--
info: Try this generator: instance : ArbitrarySizedSuchThat Nat (fun x_1 => lookup Γ_1 x_1 τ_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (Γ_1 : List type) (τ_1 : type) : OptionT Plausible.Gen Nat :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match Γ_1 with
              | List.cons τ Γ =>
                match DecOpt.decOpt (BEq.beq τ τ_1) initSize with
                | Option.some Bool.true => return Nat.zero
                | _ => OptionT.fail
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match Γ_1 with
              | List.cons τ Γ =>
                match DecOpt.decOpt (BEq.beq τ τ_1) initSize with
                | Option.some Bool.true => return Nat.zero
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match Γ_1 with
              | List.cons τ' Γ => do
                let n ← aux_arb initSize size' Γ τ_1;
                return Nat.succ n
              | _ => OptionT.fail)]
    fun size => aux_arb size size Γ_1 τ_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (x : Nat) => lookup Γ x τ)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat type (fun τ_1 => lookup Γ_1 x_1 τ_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (Γ_1 : List type) (x_1 : Nat) : OptionT Plausible.Gen type :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match x_1 with
              | Nat.zero =>
                match Γ_1 with
                | List.cons τ Γ => return τ
                | _ => OptionT.fail
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match x_1 with
              | Nat.zero =>
                match Γ_1 with
                | List.cons τ Γ => return τ
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match x_1 with
              | Nat.succ n =>
                match Γ_1 with
                | List.cons τ' Γ => do
                  let τ_1 ← aux_arb initSize size' Γ n;
                  return τ_1
                | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size Γ_1 x_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (τ : type) => lookup Γ x τ)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat type (fun t_1 => typing G_1 e_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (G_1 : List type) (e_1 : term) : OptionT Plausible.Gen type :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match e_1 with
              | term.Const n => return type.Nat
              | _ => OptionT.fail),
            (1,
              match e_1 with
              | term.Var x => do
                let t_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun t_1 => lookup G_1 x t_1) initSize;
                return t_1
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match e_1 with
              | term.Const n => return type.Nat
              | _ => OptionT.fail),
            (1,
              match e_1 with
              | term.Var x => do
                let t_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun t_1 => lookup G_1 x t_1) initSize;
                return t_1
              | _ => OptionT.fail),
            (Nat.succ size',
              match e_1 with
              | term.Add e1 e2 =>
                match DecOpt.decOpt (typing G_1 e1 (type.Nat)) initSize with
                | Option.some Bool.true =>
                  match DecOpt.decOpt (typing G_1 e2 (type.Nat)) initSize with
                  | Option.some Bool.true => return type.Nat
                  | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match e_1 with
              | term.Abs τ1 e => do
                let τ2 ← aux_arb initSize size' (List.cons τ1 G_1) e;
                return type.Fun τ1 τ2
              | _ => OptionT.fail),
            (Nat.succ size',
              match e_1 with
              | term.App e1 e2 => do
                let τ1 ← aux_arb initSize size' G_1 e2;
                do
                  let t_1 ← Plausible.Arbitrary.arbitrary;
                  match DecOpt.decOpt (typing G_1 e1 (type.Fun τ1 t_1)) initSize with
                    | Option.some Bool.true => return t_1
                    | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size G_1 e_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (t : type) => typing G e t)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat term (fun e_1 => typing G_1 e_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (G_1 : List type) (t_1 : type) : OptionT Plausible.Gen term :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match t_1 with
              | type.Nat => do
                let n ← Plausible.Arbitrary.arbitrary;
                return term.Const n
              | _ => OptionT.fail),
            (1, do
              let x ← ArbitrarySizedSuchThat.arbitrarySizedST (fun x => lookup G_1 x t_1) initSize;
              return term.Var x)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match t_1 with
              | type.Nat => do
                let n ← Plausible.Arbitrary.arbitrary;
                return term.Const n
              | _ => OptionT.fail),
            (1, do
              let x ← ArbitrarySizedSuchThat.arbitrarySizedST (fun x => lookup G_1 x t_1) initSize;
              return term.Var x),
            (Nat.succ size',
              match t_1 with
              | type.Nat => do
                let e1 ← aux_arb initSize size' G_1 (type.Nat);
                do
                  let e2 ← aux_arb initSize size' G_1 (type.Nat);
                  return term.Add e1 e2
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | type.Fun τ1 τ2 => do
                let e ← aux_arb initSize size' (List.cons τ1 G_1) τ2;
                return term.Abs τ1 e
              | _ => OptionT.fail),
            (Nat.succ size', do
              let e2 ← Plausible.Arbitrary.arbitrary;
              do
                let τ1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun τ1 => typing G_1 e2 τ1) initSize;
                do
                  let e1 ← aux_arb initSize size' G_1 (type.Fun τ1 t_1);
                  return term.App e1 e2)]
    fun size => aux_arb size size G_1 t_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (e : term) => typing G e t)

-- To sample from this generator and print out 10 successful examples using the `Repr`
-- instance for `term`, we can run the following:
-- #eval runSizedGenPrintOutput (ArbitrarySizedSuchThat.arbitrarySizedST (fun e => typing [] e $ .Fun .Nat .Nat)) 3
