import Test.CedarExample.Cedar
import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Chamelean.GeneratorCombinators
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.DeriveConstrainedProducer

open Plausible

/-!
This file contains snapshot tests for checkers & generators that
are derived by Chamelean for the inductive relations defined in `Test/CedarExample.Cedar.lean`.

Note: the structure of this file closely follows Mike Hicks's Coq formalization of Cedar (not publicly available),
in particular the order in which he derives checkers/generators using QuickChick.
-/

-- Suppress warnings for unused variables in derived generators/checkers
set_option linter.unusedVariables false

-- Suppress warnings for redundant pattern-match cases in derived generators/checkers
set_option match.ignoreUnusedAlts true

/-- We override the default `Arbitrary` instance for `String`s with our custom generator -/
instance : Arbitrary String where
  arbitrary := GeneratorCombinators.elementsWithDefault
    "Aaron" ["Aaron", "John", "Mike", "Kesha", "Hicks", "A", "B", "C", "D"]

-- Derive `Arbitrary` instances for Cedar data/types/expressions/schemas
deriving instance Arbitrary for
  EntityName, EntityUID, Prim, Var, PatElem, UnaryOp, BinaryOp, CedarExpr,
  Request, BoolType, CedarType, EntitySchemaEntry, ActionSchemaEntry, Schema,
  RequestType, Environment, PathSet

--------------------------------------------------
-- Checker & Generator for `RecordExpr` relation
--------------------------------------------------

/--
info: Try this checker: instance : DecOpt (RecordExpr ce_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ce_1 : CedarExpr) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ce_1 with
            | CedarExpr.recExprNil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ce_1 with
            | CedarExpr.recExprCons fn e r => Option.some Bool.true
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ce_1 with
            | CedarExpr.recExprNil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ce_1 with
            | CedarExpr.recExprCons fn e r => Option.some Bool.true
            | _ => Option.some Bool.false,
            ]
    fun size => aux_dec size size ce_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (RecordExpr ce)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat CedarExpr (fun ce_1 => RecordExpr ce_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) : OptionT Plausible.Gen CedarExpr :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1, return CedarExpr.recExprNil),
            (1, do
              let e ← Plausible.Arbitrary.arbitrary;
              do
                let fn ← Plausible.Arbitrary.arbitrary;
                do
                  let r ← Plausible.Arbitrary.arbitrary;
                  return CedarExpr.recExprCons fn e r)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, return CedarExpr.recExprNil),
            (1, do
              let e ← Plausible.Arbitrary.arbitrary;
              do
                let fn ← Plausible.Arbitrary.arbitrary;
                do
                  let r ← Plausible.Arbitrary.arbitrary;
                  return CedarExpr.recExprCons fn e r),
            ]
    fun size => aux_arb size size
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (ce : CedarExpr) => RecordExpr ce)

-----------------------------------------------
-- Checker & Generator for `SetExpr` relation
-----------------------------------------------


/--
info: Try this checker: instance : DecOpt (SetExpr ce_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ce_1 : CedarExpr) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ce_1 with
            | CedarExpr.setExprNil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ce_1 with
            | CedarExpr.setExprCons e r => Option.some Bool.true
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ce_1 with
            | CedarExpr.setExprNil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ce_1 with
            | CedarExpr.setExprCons e r => Option.some Bool.true
            | _ => Option.some Bool.false,
            ]
    fun size => aux_dec size size ce_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (SetExpr ce)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat CedarExpr (fun ce_1 => SetExpr ce_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) : OptionT Plausible.Gen CedarExpr :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1, return CedarExpr.setExprNil),
            (1, do
              let e ← Plausible.Arbitrary.arbitrary;
              do
                let r ← Plausible.Arbitrary.arbitrary;
                return CedarExpr.setExprCons e r)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, return CedarExpr.setExprNil),
            (1, do
              let e ← Plausible.Arbitrary.arbitrary;
              do
                let r ← Plausible.Arbitrary.arbitrary;
                return CedarExpr.setExprCons e r),
            ]
    fun size => aux_arb size size
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (ce : CedarExpr) => SetExpr ce)

--------------------------------------------------
-- Checker & Generator for `SetEntityValues` relation
--------------------------------------------------

/--
info: Try this checker: instance : DecOpt (SetEntityValues ce_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ce_1 : CedarExpr) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ce_1 with
            | CedarExpr.setExprNil => Option.some Bool.true
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ce_1 with
            | CedarExpr.setExprNil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ce_1 with
            | CedarExpr.setExprCons (CedarExpr.lit (Prim.entityUID uid)) r => aux_dec initSize size' r
            | _ => Option.some Bool.false]
    fun size => aux_dec size size ce_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (SetEntityValues ce)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat CedarExpr (fun ce_1 => SetEntityValues ce_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) : OptionT Plausible.Gen CedarExpr :=
      match size with
      | Nat.zero => OptionTGen.backtrack [(1, return CedarExpr.setExprNil)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, return CedarExpr.setExprNil),
            (Nat.succ size', do
              let r ← aux_arb initSize size';
              do
                let uid ← Plausible.Arbitrary.arbitrary;
                return CedarExpr.setExprCons (CedarExpr.lit (Prim.entityUID uid)) r)]
    fun size => aux_arb size size
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (ce : CedarExpr) => SetEntityValues ce)

--------------------------------------------------
-- Checker & Generator for `DefinedName` relation
--------------------------------------------------

/--
info: Try this checker: instance : DecOpt (DefinedName ns_1 n_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ns_1 : List EntityName) (n_1 : EntityName) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ns_1 with
            | List.cons A L => DecOpt.decOpt (Eq A n_1) initSize
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ns_1 with
            | List.cons A L => DecOpt.decOpt (Eq A n_1) initSize
            | _ => Option.some Bool.false,
            fun _ =>
            match ns_1 with
            | List.cons B L =>
              DecOpt.andOptList [DecOpt.decOpt (Eq (bne n_1 B) (Bool.true)) initSize, aux_dec initSize size' L n_1]
            | _ => Option.some Bool.false]
    fun size => aux_dec size size ns_1 n_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (DefinedName ns n)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat EntityName (fun n_1 => DefinedName ns_1 n_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ns_1 : List EntityName) : OptionT Plausible.Gen EntityName :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match ns_1 with
              | List.cons A L => do
                let n_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n_1 => Eq A n_1) initSize;
                return n_1
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match ns_1 with
              | List.cons A L => do
                let n_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n_1 => Eq A n_1) initSize;
                return n_1
              | _ => OptionT.fail),
            (Nat.succ size',
              match ns_1 with
              | List.cons B L => do
                let n_1 ← aux_arb initSize size' L;
                match DecOpt.decOpt (Eq (bne n_1 B) (Bool.true)) initSize with
                  | Option.some Bool.true => return n_1
                  | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size ns_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (n : EntityName) => DefinedName ns n)

--------------------------------------------------
-- Checker & Generator for `DefinedNames` relation
--------------------------------------------------

/--
info: Try this checker: instance : DecOpt (DefinedNames ns_1 ns0_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ns_1 : List EntityName) (ns0_1 : List EntityName) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ns0_1 with
            | List.nil => Option.some Bool.true
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ns0_1 with
            | List.nil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ns0_1 with
            | List.cons n ns0 =>
              DecOpt.andOptList [DecOpt.decOpt (DefinedName ns_1 n) initSize, aux_dec initSize size' ns_1 ns0]
            | _ => Option.some Bool.false]
    fun size => aux_dec size size ns_1 ns0_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (DefinedNames ns ns0)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List EntityName) (fun ns0_1 => DefinedNames ns_1 ns0_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ns_1 : List EntityName) : OptionT Plausible.Gen (List EntityName) :=
      match size with
      | Nat.zero => OptionTGen.backtrack [(1, return List.nil)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, return List.nil),
            (Nat.succ size', do
              let n ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n => DefinedName ns_1 n) initSize;
              do
                let ns0 ← aux_arb initSize size' ns_1;
                return List.cons n ns0)]
    fun size => aux_arb size size ns_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (ns0 : List EntityName) => DefinedNames ns ns0)

--------------------------------------------------
-- Checker & Generator for well-formed Cedar types
--------------------------------------------------

/--
info: Try this checker: instance : DecOpt (WfCedarType ns_1 ct_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ns_1 : List EntityName) (ct_1 : CedarType) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ct_1 with
            | CedarType.boolType B => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ct_1 with
            | CedarType.intType => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ct_1 with
            | CedarType.stringType => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ct_1 with
            | CedarType.entityType n => DecOpt.decOpt (DefinedName ns_1 n) initSize
            | _ => Option.some Bool.false,
            fun _ =>
            match ct_1 with
            | CedarType.recordTypeNil => Option.some Bool.true
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ct_1 with
            | CedarType.boolType B => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ct_1 with
            | CedarType.intType => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ct_1 with
            | CedarType.stringType => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ct_1 with
            | CedarType.entityType n => DecOpt.decOpt (DefinedName ns_1 n) initSize
            | _ => Option.some Bool.false,
            fun _ =>
            match ct_1 with
            | CedarType.recordTypeNil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ct_1 with
            | CedarType.setType T => aux_dec initSize size' ns_1 T
            | _ => Option.some Bool.false,
            fun _ =>
            match ct_1 with
            | CedarType.recordTypeCons fn o T1 (CedarType.recordTypeNil) => aux_dec initSize size' ns_1 T1
            | _ => Option.some Bool.false,
            fun _ =>
            match ct_1 with
            | CedarType.recordTypeCons fn o T1 (CedarType.recordTypeCons fn1 o1 T2 r) =>
              DecOpt.andOptList
                [aux_dec initSize size' ns_1 T1, aux_dec initSize size' ns_1 (CedarType.recordTypeCons fn1 o1 T2 r)]
            | _ => Option.some Bool.false]
    fun size => aux_dec size size ns_1 ct_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (WfCedarType ns ct)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat CedarType (fun ct_1 => WfCedarType ns_1 ct_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ns_1 : List EntityName) : OptionT Plausible.Gen CedarType :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1, do
              let B ← Plausible.Arbitrary.arbitrary;
              return CedarType.boolType B),
            (1, return CedarType.intType), (1, return CedarType.stringType),
            (1, do
              let n ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n => DefinedName ns_1 n) initSize;
              return CedarType.entityType n),
            (1, return CedarType.recordTypeNil)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, do
              let B ← Plausible.Arbitrary.arbitrary;
              return CedarType.boolType B),
            (1, return CedarType.intType), (1, return CedarType.stringType),
            (1, do
              let n ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n => DefinedName ns_1 n) initSize;
              return CedarType.entityType n),
            (1, return CedarType.recordTypeNil),
            (Nat.succ size', do
              let T ← aux_arb initSize size' ns_1;
              return CedarType.setType T),
            (Nat.succ size', do
              let T1 ← aux_arb initSize size' ns_1;
              do
                let fn ← Plausible.Arbitrary.arbitrary;
                do
                  let o ← Plausible.Arbitrary.arbitrary;
                  return CedarType.recordTypeCons fn o T1 (CedarType.recordTypeNil)),
            (Nat.succ size', do
              let T1 ← aux_arb initSize size' ns_1;
              do
                let vfn1_o1_T2_r ← aux_arb initSize size' ns_1;
                match vfn1_o1_T2_r with
                  | CedarType.recordTypeCons fn1 o1 T2 r => do
                    let fn ← Plausible.Arbitrary.arbitrary;
                    do
                      let o ← Plausible.Arbitrary.arbitrary;
                      return CedarType.recordTypeCons fn o T1 (CedarType.recordTypeCons fn1 o1 T2 r)
                  | _ => OptionT.fail)]
    fun size => aux_arb size size ns_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (ct : CedarType) => WfCedarType ns ct)

----------------------------------------------------
-- Checker & Generator for well-formed record types
----------------------------------------------------

/--
info: Try this checker: instance : DecOpt (WfRecordType ns_1 rt_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ns_1 : List EntityName) (rt_1 : CedarType) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match rt_1 with
            | CedarType.recordTypeCons fn' o' T1' (CedarType.recordTypeCons fn1 o1 T2 r) =>
              DecOpt.andOptList
                [DecOpt.decOpt (WfCedarType ns_1 T1') initSize,
                  DecOpt.decOpt (WfCedarType ns_1 (CedarType.recordTypeCons fn1 o1 T2 r)) initSize]
            | _ => Option.some Bool.false,
            fun _ =>
            match rt_1 with
            | CedarType.recordTypeCons fn' o' T1' (CedarType.recordTypeNil) =>
              DecOpt.decOpt (WfCedarType ns_1 T1') initSize
            | _ => Option.some Bool.false,
            fun _ =>
            match rt_1 with
            | CedarType.recordTypeNil => Option.some Bool.true
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match rt_1 with
            | CedarType.recordTypeCons fn' o' T1' (CedarType.recordTypeCons fn1 o1 T2 r) =>
              DecOpt.andOptList
                [DecOpt.decOpt (WfCedarType ns_1 T1') initSize,
                  DecOpt.decOpt (WfCedarType ns_1 (CedarType.recordTypeCons fn1 o1 T2 r)) initSize]
            | _ => Option.some Bool.false,
            fun _ =>
            match rt_1 with
            | CedarType.recordTypeCons fn' o' T1' (CedarType.recordTypeNil) =>
              DecOpt.decOpt (WfCedarType ns_1 T1') initSize
            | _ => Option.some Bool.false,
            fun _ =>
            match rt_1 with
            | CedarType.recordTypeNil => Option.some Bool.true
            | _ => Option.some Bool.false,
            ]
    fun size => aux_dec size size ns_1 rt_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (WfRecordType ns rt)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat CedarType (fun rt_1 => WfRecordType ns_1 rt_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ns_1 : List EntityName) : OptionT Plausible.Gen CedarType :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1, do
              let T1' ← ArbitrarySizedSuchThat.arbitrarySizedST (fun T1' => WfCedarType ns_1 T1') initSize;
              do
                let vfn1_o1_T2_r ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun vfn1_o1_T2_r => WfCedarType ns_1 vfn1_o1_T2_r) initSize;
                match vfn1_o1_T2_r with
                  | CedarType.recordTypeCons fn1 o1 T2 r => do
                    let fn' ← Plausible.Arbitrary.arbitrary;
                    do
                      let o' ← Plausible.Arbitrary.arbitrary;
                      return CedarType.recordTypeCons fn' o' T1' (CedarType.recordTypeCons fn1 o1 T2 r)
                  | _ => OptionT.fail),
            (1, do
              let T1' ← ArbitrarySizedSuchThat.arbitrarySizedST (fun T1' => WfCedarType ns_1 T1') initSize;
              do
                let fn' ← Plausible.Arbitrary.arbitrary;
                do
                  let o' ← Plausible.Arbitrary.arbitrary;
                  return CedarType.recordTypeCons fn' o' T1' (CedarType.recordTypeNil)),
            (1, return CedarType.recordTypeNil)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, do
              let T1' ← ArbitrarySizedSuchThat.arbitrarySizedST (fun T1' => WfCedarType ns_1 T1') initSize;
              do
                let vfn1_o1_T2_r ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun vfn1_o1_T2_r => WfCedarType ns_1 vfn1_o1_T2_r) initSize;
                match vfn1_o1_T2_r with
                  | CedarType.recordTypeCons fn1 o1 T2 r => do
                    let fn' ← Plausible.Arbitrary.arbitrary;
                    do
                      let o' ← Plausible.Arbitrary.arbitrary;
                      return CedarType.recordTypeCons fn' o' T1' (CedarType.recordTypeCons fn1 o1 T2 r)
                  | _ => OptionT.fail),
            (1, do
              let T1' ← ArbitrarySizedSuchThat.arbitrarySizedST (fun T1' => WfCedarType ns_1 T1') initSize;
              do
                let fn' ← Plausible.Arbitrary.arbitrary;
                do
                  let o' ← Plausible.Arbitrary.arbitrary;
                  return CedarType.recordTypeCons fn' o' T1' (CedarType.recordTypeNil)),
            (1, return CedarType.recordTypeNil), ]
    fun size => aux_arb size size ns_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (rt : CedarType) => WfRecordType ns rt)

----------------------------------------------------
-- Checker & Generator for well-formed attributes
----------------------------------------------------

/--
info: Try this checker: instance : DecOpt (WfAttrs ns_1 attrs_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ns_1 : List EntityName)
      (attrs_1 : List (String × Bool × CedarType)) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match attrs_1 with
            | List.nil => Option.some Bool.true
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match attrs_1 with
            | List.nil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match attrs_1 with
            | List.cons (Prod.mk s (Prod.mk b T)) attrs =>
              DecOpt.andOptList [DecOpt.decOpt (WfCedarType ns_1 T) initSize, aux_dec initSize size' ns_1 attrs]
            | _ => Option.some Bool.false]
    fun size => aux_dec size size ns_1 attrs_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (WfAttrs ns attrs)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List (String × Bool × CedarType)) (fun attrs_1 => WfAttrs ns_1 attrs_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ns_1 : List EntityName) :
      OptionT Plausible.Gen (List (String × Bool × CedarType)) :=
      match size with
      | Nat.zero => OptionTGen.backtrack [(1, return List.nil)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, return List.nil),
            (Nat.succ size', do
              let T ← ArbitrarySizedSuchThat.arbitrarySizedST (fun T => WfCedarType ns_1 T) initSize;
              do
                let attrs ← aux_arb initSize size' ns_1;
                do
                  let b ← Plausible.Arbitrary.arbitrary;
                  do
                    let s ← Plausible.Arbitrary.arbitrary;
                    return List.cons (Prod.mk s (Prod.mk b T)) attrs)]
    fun size => aux_arb size size ns_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (attrs : List (String × Bool × CedarType)) => WfAttrs ns attrs)

---------------------------------------------------------------------
-- Checker & Generator for well-formed `EntitySchemaEntry`(ies)
---------------------------------------------------------------------
/--
info: Try this checker: instance : DecOpt (WfET ns_1 et_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ns_1 : List EntityName) (et_1 : EntitySchemaEntry) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match et_1 with
            | EntitySchemaEntry.MkEntitySchemaEntry ancs attrs =>
              DecOpt.andOptList
                [DecOpt.decOpt (DefinedNames ns_1 ancs) initSize, DecOpt.decOpt (WfAttrs ns_1 attrs) initSize]
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match et_1 with
            | EntitySchemaEntry.MkEntitySchemaEntry ancs attrs =>
              DecOpt.andOptList
                [DecOpt.decOpt (DefinedNames ns_1 ancs) initSize, DecOpt.decOpt (WfAttrs ns_1 attrs) initSize]
            | _ => Option.some Bool.false,
            ]
    fun size => aux_dec size size ns_1 et_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (WfET ns et)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat EntitySchemaEntry (fun et_1 => WfET ns_1 et_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ns_1 : List EntityName) : OptionT Plausible.Gen EntitySchemaEntry :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1, do
              let ancs ← ArbitrarySizedSuchThat.arbitrarySizedST (fun ancs => DefinedNames ns_1 ancs) initSize;
              do
                let attrs ← ArbitrarySizedSuchThat.arbitrarySizedST (fun attrs => WfAttrs ns_1 attrs) initSize;
                return EntitySchemaEntry.MkEntitySchemaEntry ancs attrs)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, do
              let ancs ← ArbitrarySizedSuchThat.arbitrarySizedST (fun ancs => DefinedNames ns_1 ancs) initSize;
              do
                let attrs ← ArbitrarySizedSuchThat.arbitrarySizedST (fun attrs => WfAttrs ns_1 attrs) initSize;
                return EntitySchemaEntry.MkEntitySchemaEntry ancs attrs),
            ]
    fun size => aux_arb size size ns_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (et : EntitySchemaEntry) => WfET ns et)

/--
info: Try this checker: instance : DecOpt (WfETS ns_1 ns0_1 ets_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ns_1 : List EntityName) (ns0_1 : List EntityName)
      (ets_1 : List (EntityName × EntitySchemaEntry)) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ets_1 with
            | List.cons (Prod.mk u_3 et) (List.nil) =>
              match ns0_1 with
              | List.cons n (List.nil) =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_3 n) initSize,
                    DecOpt.andOptList
                      [DecOpt.decOpt (DefinedName ns_1 n) initSize, DecOpt.decOpt (WfET ns_1 et) initSize]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ets_1 with
            | List.cons (Prod.mk u_3 et) (List.nil) =>
              match ns0_1 with
              | List.cons n (List.nil) =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_3 n) initSize,
                    DecOpt.andOptList
                      [DecOpt.decOpt (DefinedName ns_1 n) initSize, DecOpt.decOpt (WfET ns_1 et) initSize]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match ets_1 with
            | List.cons (Prod.mk u_3 et) ets =>
              match ns0_1 with
              | List.cons n ns0 =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_3 n) initSize,
                    DecOpt.andOptList
                      [DecOpt.decOpt (DefinedName ns_1 n) initSize,
                        DecOpt.andOptList [DecOpt.decOpt (WfET ns_1 et) initSize, aux_dec initSize size' ns_1 ns0 ets]]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
    fun size => aux_dec size size ns_1 ns0_1 ets_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (WfETS ns ns0 ets)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List (EntityName × EntitySchemaEntry)) (fun ets_1 => WfETS ns_1 ns0_1 ets_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ns_1 : List EntityName) (ns0_1 : List EntityName) :
      OptionT Plausible.Gen (List (EntityName × EntitySchemaEntry)) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match ns0_1 with
              | List.cons n (List.nil) =>
                match DecOpt.decOpt (DefinedName ns_1 n) initSize with
                | Option.some Bool.true => do
                  let et ← ArbitrarySizedSuchThat.arbitrarySizedST (fun et => WfET ns_1 et) initSize;
                  return List.cons (Prod.mk n et) (List.nil)
                | _ => OptionT.fail
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match ns0_1 with
              | List.cons n (List.nil) =>
                match DecOpt.decOpt (DefinedName ns_1 n) initSize with
                | Option.some Bool.true => do
                  let et ← ArbitrarySizedSuchThat.arbitrarySizedST (fun et => WfET ns_1 et) initSize;
                  return List.cons (Prod.mk n et) (List.nil)
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match ns0_1 with
              | List.cons n ns0 =>
                match DecOpt.decOpt (DefinedName ns_1 n) initSize with
                | Option.some Bool.true => do
                  let et ← ArbitrarySizedSuchThat.arbitrarySizedST (fun et => WfET ns_1 et) initSize;
                  do
                    let ets ← aux_arb initSize size' ns_1 ns0;
                    return List.cons (Prod.mk n et) ets
                | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size ns_1 ns0_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (ets : List (EntityName × EntitySchemaEntry)) => WfETS ns ns0 ets)

---------------------------------------------------------------------
-- Checker & Generator for well-formed `ActionSchemaEntry`(ies)
---------------------------------------------------------------------

/--
info: Try this checker: instance : DecOpt (WfACT ns_1 act_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ns_1 : List EntityName) (act_1 : EntityUID × ActionSchemaEntry) :
      Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match act_1 with
            |
            Prod.mk (EntityUID.MkEntityUID n s)
                (ActionSchemaEntry.MkActionSchemaEntry (List.cons p (List.nil)) (List.cons r (List.nil)) attrs) =>
              DecOpt.andOptList
                [DecOpt.decOpt (DefinedName ns_1 n) initSize,
                  DecOpt.andOptList
                    [DecOpt.decOpt (DefinedName ns_1 p) initSize,
                      DecOpt.andOptList
                        [DecOpt.decOpt (DefinedName ns_1 r) initSize, DecOpt.decOpt (WfAttrs ns_1 attrs) initSize]]]
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match act_1 with
            |
            Prod.mk (EntityUID.MkEntityUID n s)
                (ActionSchemaEntry.MkActionSchemaEntry (List.cons p (List.nil)) (List.cons r (List.nil)) attrs) =>
              DecOpt.andOptList
                [DecOpt.decOpt (DefinedName ns_1 n) initSize,
                  DecOpt.andOptList
                    [DecOpt.decOpt (DefinedName ns_1 p) initSize,
                      DecOpt.andOptList
                        [DecOpt.decOpt (DefinedName ns_1 r) initSize, DecOpt.decOpt (WfAttrs ns_1 attrs) initSize]]]
            | _ => Option.some Bool.false,
            ]
    fun size => aux_dec size size ns_1 act_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (WfACT ns act)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (EntityUID × ActionSchemaEntry) (fun act_1 => WfACT ns_1 act_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ns_1 : List EntityName) :
      OptionT Plausible.Gen (EntityUID × ActionSchemaEntry) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1, do
              let n ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n => DefinedName ns_1 n) initSize;
              do
                let p ← ArbitrarySizedSuchThat.arbitrarySizedST (fun p => DefinedName ns_1 p) initSize;
                do
                  let r ← ArbitrarySizedSuchThat.arbitrarySizedST (fun r => DefinedName ns_1 r) initSize;
                  do
                    let attrs ← ArbitrarySizedSuchThat.arbitrarySizedST (fun attrs => WfAttrs ns_1 attrs) initSize;
                    do
                      let s ← Plausible.Arbitrary.arbitrary;
                      return
                          Prod.mk (EntityUID.MkEntityUID n s)
                            (ActionSchemaEntry.MkActionSchemaEntry (List.cons p (List.nil)) (List.cons r (List.nil))
                              attrs))]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, do
              let n ← ArbitrarySizedSuchThat.arbitrarySizedST (fun n => DefinedName ns_1 n) initSize;
              do
                let p ← ArbitrarySizedSuchThat.arbitrarySizedST (fun p => DefinedName ns_1 p) initSize;
                do
                  let r ← ArbitrarySizedSuchThat.arbitrarySizedST (fun r => DefinedName ns_1 r) initSize;
                  do
                    let attrs ← ArbitrarySizedSuchThat.arbitrarySizedST (fun attrs => WfAttrs ns_1 attrs) initSize;
                    do
                      let s ← Plausible.Arbitrary.arbitrary;
                      return
                          Prod.mk (EntityUID.MkEntityUID n s)
                            (ActionSchemaEntry.MkActionSchemaEntry (List.cons p (List.nil)) (List.cons r (List.nil))
                              attrs)),
            ]
    fun size => aux_arb size size ns_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (act : EntityUID × ActionSchemaEntry) => WfACT ns act)

/--
info: Try this checker: instance : DecOpt (WfACTS ns_1 act_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ns_1 : List EntityName)
      (act_1 : List (EntityUID × ActionSchemaEntry)) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match act_1 with
            | List.cons act (List.nil) => DecOpt.decOpt (WfACT ns_1 act) initSize
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match act_1 with
            | List.cons act (List.nil) => DecOpt.decOpt (WfACT ns_1 act) initSize
            | _ => Option.some Bool.false,
            fun _ =>
            match act_1 with
            | List.cons act acts =>
              DecOpt.andOptList [DecOpt.decOpt (WfACT ns_1 act) initSize, aux_dec initSize size' ns_1 acts]
            | _ => Option.some Bool.false]
    fun size => aux_dec size size ns_1 act_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (WfACTS ns act)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List (EntityUID × ActionSchemaEntry)) (fun act_1 => WfACTS ns_1 act_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ns_1 : List EntityName) :
      OptionT Plausible.Gen (List (EntityUID × ActionSchemaEntry)) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1, do
              let act ← ArbitrarySizedSuchThat.arbitrarySizedST (fun act => WfACT ns_1 act) initSize;
              return List.cons act (List.nil))]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, do
              let act ← ArbitrarySizedSuchThat.arbitrarySizedST (fun act => WfACT ns_1 act) initSize;
              return List.cons act (List.nil)),
            (Nat.succ size', do
              let act ← ArbitrarySizedSuchThat.arbitrarySizedST (fun act => WfACT ns_1 act) initSize;
              do
                let acts ← aux_arb initSize size' ns_1;
                return List.cons act acts)]
    fun size => aux_arb size size ns_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (act : List (EntityUID × ActionSchemaEntry)) => WfACTS ns act)

------------------------------------------------------------
-- Checker & Generator for well-formed schemas
------------------------------------------------------------
/--
info: Try this checker: instance : DecOpt (WfSchema ns_1 s_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ns_1 : List EntityName) (s_1 : Schema) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match s_1 with
            | Schema.MkSchema ets acts =>
              DecOpt.andOptList
                [DecOpt.decOpt (WfACTS ns_1 acts) initSize, DecOpt.decOpt (WfETS ns_1 ns_1 ets) initSize]
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match s_1 with
            | Schema.MkSchema ets acts =>
              DecOpt.andOptList
                [DecOpt.decOpt (WfACTS ns_1 acts) initSize, DecOpt.decOpt (WfETS ns_1 ns_1 ets) initSize]
            | _ => Option.some Bool.false,
            ]
    fun size => aux_dec size size ns_1 s_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (WfSchema ns s)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat Schema (fun s_1 => WfSchema ns_1 s_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ns_1 : List EntityName) : OptionT Plausible.Gen Schema :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1, do
              let acts ← ArbitrarySizedSuchThat.arbitrarySizedST (fun acts => WfACTS ns_1 acts) initSize;
              do
                let ets ← ArbitrarySizedSuchThat.arbitrarySizedST (fun ets => WfETS ns_1 ns_1 ets) initSize;
                return Schema.MkSchema ets acts)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, do
              let acts ← ArbitrarySizedSuchThat.arbitrarySizedST (fun acts => WfACTS ns_1 acts) initSize;
              do
                let ets ← ArbitrarySizedSuchThat.arbitrarySizedST (fun ets => WfETS ns_1 ns_1 ets) initSize;
                return Schema.MkSchema ets acts),
            ]
    fun size => aux_arb size size ns_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (s : Schema) => WfSchema ns s)

------------------------------------------------------------
-- Checker & Generator for defined entities
------------------------------------------------------------
/--
info: Try this checker: instance : DecOpt (DefinedEntity ets_1 n_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ets_1 : List (EntityName × EntitySchemaEntry)) (n_1 : EntityName) :
      Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ets_1 with
            | List.cons (Prod.mk n E) R => DecOpt.decOpt (BEq.beq n n_1) initSize
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ets_1 with
            | List.cons (Prod.mk n E) R => DecOpt.decOpt (BEq.beq n n_1) initSize
            | _ => Option.some Bool.false,
            fun _ =>
            match ets_1 with
            | List.cons (Prod.mk n1 E) R =>
              DecOpt.andOptList [DecOpt.decOpt (Eq (bne n_1 n1) (Bool.true)) initSize, aux_dec initSize size' R n_1]
            | _ => Option.some Bool.false]
    fun size => aux_dec size size ets_1 n_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (DefinedEntity ets n)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat EntityName (fun n_1 => DefinedEntity ets_1 n_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ets_1 : List (EntityName × EntitySchemaEntry)) :
      OptionT Plausible.Gen EntityName :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match ets_1 with
              | List.cons (Prod.mk n E) R => return n
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match ets_1 with
              | List.cons (Prod.mk n E) R => return n
              | _ => OptionT.fail),
            (Nat.succ size',
              match ets_1 with
              | List.cons (Prod.mk n1 E) R => do
                let n_1 ← aux_arb initSize size' R;
                match DecOpt.decOpt (Eq (bne n_1 n1) (Bool.true)) initSize with
                  | Option.some Bool.true => return n_1
                  | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size ets_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (n : EntityName) => DefinedEntity ets n)

/--
info: Try this checker: instance : DecOpt (DefinedEntities ets_1 n_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ets_1 : List (EntityName × EntitySchemaEntry))
      (n_1 : List EntityName) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match n_1 with
            | List.nil =>
              match ets_1 with
              | List.nil => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match n_1 with
            | List.nil =>
              match ets_1 with
              | List.nil => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match n_1 with
            | List.cons u_2 ns =>
              match ets_1 with
              | List.cons (Prod.mk n et) ets =>
                DecOpt.andOptList [DecOpt.decOpt (BEq.beq u_2 n) initSize, aux_dec initSize size' ets ns]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
    fun size => aux_dec size size ets_1 n_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (DefinedEntities ets n)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List EntityName) (fun n_1 => DefinedEntities ets_1 n_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ets_1 : List (EntityName × EntitySchemaEntry)) :
      OptionT Plausible.Gen (List EntityName) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match ets_1 with
              | List.nil => return List.nil
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match ets_1 with
              | List.nil => return List.nil
              | _ => OptionT.fail),
            (Nat.succ size',
              match ets_1 with
              | List.cons (Prod.mk n et) ets => do
                let ns ← aux_arb initSize size' ets;
                return List.cons n ns
              | _ => OptionT.fail)]
    fun size => aux_arb size size ets_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (n : List EntityName) => DefinedEntities ets n)

---------------------------------------------
-- Schema: LookupEntityAttr / GetEntityAttr
---------------------------------------------

/--
info: Try this checker: instance : DecOpt (LookupEntityAttr l_1 fnb_1 t_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (l_1 : List (String × Bool × CedarType)) (fnb_1 : String × Bool)
      (t_1 : CedarType) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match fnb_1 with
            | Prod.mk u_3 u_4 =>
              match l_1 with
              | List.cons (Prod.mk F (Prod.mk B TF)) FS =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_3 F) initSize,
                    DecOpt.andOptList [DecOpt.decOpt (BEq.beq TF t_1) initSize, DecOpt.decOpt (BEq.beq u_4 B) initSize]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match fnb_1 with
            | Prod.mk u_3 u_4 =>
              match l_1 with
              | List.cons (Prod.mk F (Prod.mk B TF)) FS =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_3 F) initSize,
                    DecOpt.andOptList [DecOpt.decOpt (BEq.beq TF t_1) initSize, DecOpt.decOpt (BEq.beq u_4 B) initSize]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match fnb_1 with
            | Prod.mk F1 B1 =>
              match l_1 with
              | List.cons (Prod.mk F2 (Prod.mk B TF)) FS =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq TF t_1) initSize,
                    DecOpt.andOptList
                      [DecOpt.decOpt (Eq (bne F1 F2) (Bool.true)) initSize,
                        aux_dec initSize size' FS (Prod.mk F1 B1) t_1]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
    fun size => aux_dec size size l_1 fnb_1 t_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (LookupEntityAttr l fnb t)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (String × Bool) (fun fnb_1 => LookupEntityAttr l_1 fnb_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (l_1 : List (String × Bool × CedarType)) (t_1 : CedarType) :
      OptionT Plausible.Gen (String × Bool) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match l_1 with
              | List.cons (Prod.mk F (Prod.mk B TF)) FS =>
                match DecOpt.decOpt (BEq.beq TF t_1) initSize with
                | Option.some Bool.true => return Prod.mk F B
                | _ => OptionT.fail
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match l_1 with
              | List.cons (Prod.mk F (Prod.mk B TF)) FS =>
                match DecOpt.decOpt (BEq.beq TF t_1) initSize with
                | Option.some Bool.true => return Prod.mk F B
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match l_1 with
              | List.cons (Prod.mk F2 (Prod.mk B TF)) FS =>
                match DecOpt.decOpt (BEq.beq TF t_1) initSize with
                | Option.some Bool.true => do
                  let vF1_B1 ← aux_arb initSize size' FS t_1;
                  match vF1_B1 with
                    | Prod.mk F1 B1 =>
                      match DecOpt.decOpt (Eq (bne F1 F2) (Bool.true)) initSize with
                      | Option.some Bool.true => return Prod.mk F1 B1
                      | _ => OptionT.fail
                    | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size l_1 t_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (fnb : (String × Bool)) => LookupEntityAttr l fnb t)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (EntityName × String × Bool) (fun nfn_1 => GetEntityAttr ets_1 nfn_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ets_1 : List (EntityName × EntitySchemaEntry)) (t_1 : CedarType) :
      OptionT Plausible.Gen (EntityName × String × Bool) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match ets_1 with
              | List.cons (Prod.mk n (EntitySchemaEntry.MkEntitySchemaEntry A E)) R => do
                let vfn_b ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun vfn_b => LookupEntityAttr E vfn_b t_1) initSize;
                match vfn_b with
                  | Prod.mk fn b => return Prod.mk n (Prod.mk fn b)
                  | _ => OptionT.fail
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match ets_1 with
              | List.cons (Prod.mk n (EntitySchemaEntry.MkEntitySchemaEntry A E)) R => do
                let vfn_b ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun vfn_b => LookupEntityAttr E vfn_b t_1) initSize;
                match vfn_b with
                  | Prod.mk fn b => return Prod.mk n (Prod.mk fn b)
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match ets_1 with
              | List.cons (Prod.mk n1 E) R => do
                let vn_fn_b ← aux_arb initSize size' R t_1;
                match vn_fn_b with
                  | Prod.mk n (Prod.mk fn b) =>
                    match DecOpt.decOpt (Eq (bne n n1) (Bool.true)) initSize with
                    | Option.some Bool.true => return Prod.mk n (Prod.mk fn b)
                    | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size ets_1 t_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (nfn : (EntityName × String × Bool)) => GetEntityAttr ets nfn t)

/--
info: Try this checker: instance : DecOpt (ReqContextToCedarType c_1 t_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (c_1 : List (String × Bool × CedarType)) (t_1 : CedarType) :
      Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match t_1 with
            | CedarType.recordTypeNil =>
              match c_1 with
              | List.nil => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match t_1 with
            | CedarType.recordTypeNil =>
              match c_1 with
              | List.nil => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.recordTypeCons u_2 u_3 u_4 TR =>
              match c_1 with
              | List.cons (Prod.mk i (Prod.mk B T)) R =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_3 B) initSize,
                    DecOpt.andOptList
                      [DecOpt.decOpt (BEq.beq u_4 T) initSize,
                        DecOpt.andOptList [DecOpt.decOpt (BEq.beq u_2 i) initSize, aux_dec initSize size' R TR]]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
    fun size => aux_dec size size c_1 t_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (ReqContextToCedarType c t)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat CedarType (fun t_1 => ReqContextToCedarType c_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (c_1 : List (String × Bool × CedarType)) :
      OptionT Plausible.Gen CedarType :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match c_1 with
              | List.nil => return CedarType.recordTypeNil
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match c_1 with
              | List.nil => return CedarType.recordTypeNil
              | _ => OptionT.fail),
            (Nat.succ size',
              match c_1 with
              | List.cons (Prod.mk i (Prod.mk B T)) R => do
                let TR ← aux_arb initSize size' R;
                return CedarType.recordTypeCons i B T TR
              | _ => OptionT.fail)]
    fun size => aux_arb size size c_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (t : CedarType) => ReqContextToCedarType c t)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List RequestType) (fun reqs_1 => ActionToRequestTypes e_1 n_1 ns_1 l_1 rs_1 reqs_1)
    where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (e_1 : EntityUID) (n_1 : EntityName) (ns_1 : List EntityName)
      (l_1 : List (String × Bool × CedarType)) (rs_1 : List RequestType) : OptionT Plausible.Gen (List RequestType) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match ns_1 with
              | List.cons r (List.nil) => return List.cons (RequestType.MkRequest n_1 e_1 r l_1) rs_1
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match ns_1 with
              | List.cons r (List.nil) => return List.cons (RequestType.MkRequest n_1 e_1 r l_1) rs_1
              | _ => OptionT.fail),
            (Nat.succ size',
              match ns_1 with
              | List.cons r rs => do
                let reqs ← aux_arb initSize size' e_1 n_1 rs l_1 rs_1;
                return List.cons (RequestType.MkRequest n_1 e_1 r l_1) reqs
              | _ => OptionT.fail)]
    fun size => aux_arb size size e_1 n_1 ns_1 l_1 rs_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (reqs : List RequestType) => ActionToRequestTypes e n ns l rs reqs)

/--
info: Try this generator: instance :
    ArbitrarySizedSuchThat (List RequestType) (fun reqs_1 => ActionSchemaEntryToRequestTypes e_1 ae_1 ls_1 reqs_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (e_1 : EntityUID) (ae_1 : ActionSchemaEntry)
      (ls_1 : List RequestType) : OptionT Plausible.Gen (List RequestType) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match ae_1 with
              | ActionSchemaEntry.MkActionSchemaEntry (List.cons p (List.nil)) rs c => do
                let reqs_1 ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun reqs_1 => ActionToRequestTypes e_1 p rs c ls_1 reqs_1)
                      initSize;
                return reqs_1
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match ae_1 with
              | ActionSchemaEntry.MkActionSchemaEntry (List.cons p (List.nil)) rs c => do
                let reqs_1 ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun reqs_1 => ActionToRequestTypes e_1 p rs c ls_1 reqs_1)
                      initSize;
                return reqs_1
              | _ => OptionT.fail),
            (Nat.succ size',
              match ae_1 with
              | ActionSchemaEntry.MkActionSchemaEntry (List.cons p ps) rs c => do
                let reqs' ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun reqs' => ActionToRequestTypes e_1 p rs c ls_1 reqs')
                      initSize;
                do
                  let reqs_1 ← aux_arb initSize size' e_1 (ActionSchemaEntry.MkActionSchemaEntry ps rs c) reqs';
                  return reqs_1
              | _ => OptionT.fail)]
    fun size => aux_arb size size e_1 ae_1 ls_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (reqs : List RequestType) => ActionSchemaEntryToRequestTypes e ae ls reqs)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List RequestType) (fun reqs_1 => ActionSchemaToRequestTypes acts_1 ls_1 reqs_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (acts_1 : List (EntityUID × ActionSchemaEntry))
      (ls_1 : List RequestType) : OptionT Plausible.Gen (List RequestType) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match acts_1 with
              | List.cons (Prod.mk uid a) (List.nil) => do
                let reqs_1 ←
                  ArbitrarySizedSuchThat.arbitrarySizedST
                      (fun reqs_1 => ActionSchemaEntryToRequestTypes uid a ls_1 reqs_1) initSize;
                return reqs_1
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match acts_1 with
              | List.cons (Prod.mk uid a) (List.nil) => do
                let reqs_1 ←
                  ArbitrarySizedSuchThat.arbitrarySizedST
                      (fun reqs_1 => ActionSchemaEntryToRequestTypes uid a ls_1 reqs_1) initSize;
                return reqs_1
              | _ => OptionT.fail),
            (Nat.succ size',
              match acts_1 with
              | List.cons (Prod.mk uid a) ass => do
                let reqs' ←
                  ArbitrarySizedSuchThat.arbitrarySizedST
                      (fun reqs' => ActionSchemaEntryToRequestTypes uid a ls_1 reqs') initSize;
                do
                  let reqs_1 ← aux_arb initSize size' ass reqs';
                  return reqs_1
              | _ => OptionT.fail)]
    fun size => aux_arb size size acts_1 ls_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (reqs : List RequestType) => ActionSchemaToRequestTypes acts ls reqs)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List Environment) (fun es_1 => SchemaToEnvironments s_1 l_1 es_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (s_1 : Schema) (l_1 : List RequestType) :
      OptionT Plausible.Gen (List Environment) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match l_1 with
              | List.cons r (List.nil) => return List.cons (Environment.MkEnvironment s_1 r) (List.nil)
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match l_1 with
              | List.cons r (List.nil) => return List.cons (Environment.MkEnvironment s_1 r) (List.nil)
              | _ => OptionT.fail),
            (Nat.succ size',
              match l_1 with
              | List.cons r rs => do
                let envs ← aux_arb initSize size' s_1 rs;
                return List.cons (Environment.MkEnvironment s_1 r) envs
              | _ => OptionT.fail)]
    fun size => aux_arb size size s_1 l_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (es : List Environment) => SchemaToEnvironments s l es)

---------------------------------------
-- Checker & Generator for RecordTypes
---------------------------------------
/--
info: Try this checker: instance : DecOpt (RecordType ct_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ct_1 : CedarType) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ct_1 with
            | CedarType.recordTypeNil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ct_1 with
            | CedarType.recordTypeCons fn o T1 T2 => Option.some Bool.true
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match ct_1 with
            | CedarType.recordTypeNil => Option.some Bool.true
            | _ => Option.some Bool.false,
            fun _ =>
            match ct_1 with
            | CedarType.recordTypeCons fn o T1 T2 => Option.some Bool.true
            | _ => Option.some Bool.false,
            ]
    fun size => aux_dec size size ct_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (RecordType ct)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat CedarType (fun ct_1 => RecordType ct_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) : OptionT Plausible.Gen CedarType :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1, return CedarType.recordTypeNil),
            (1, do
              let T1 ← Plausible.Arbitrary.arbitrary;
              do
                let T2 ← Plausible.Arbitrary.arbitrary;
                do
                  let fn ← Plausible.Arbitrary.arbitrary;
                  do
                    let o ← Plausible.Arbitrary.arbitrary;
                    return CedarType.recordTypeCons fn o T1 T2)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, return CedarType.recordTypeNil),
            (1, do
              let T1 ← Plausible.Arbitrary.arbitrary;
              do
                let T2 ← Plausible.Arbitrary.arbitrary;
                do
                  let fn ← Plausible.Arbitrary.arbitrary;
                  do
                    let o ← Plausible.Arbitrary.arbitrary;
                    return CedarType.recordTypeCons fn o T1 T2),
            ]
    fun size => aux_arb size size
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (ct : CedarType) => RecordType ct)

--------------------
-- Subtyping & Typing
--------------------
/--
info: Try this checker: instance : DecOpt (SubType t1_1 t2_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (t1_1 : CedarType) (t2_1 : CedarType) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match t2_1 with
            | CedarType.boolType (BoolType.anyBool) =>
              match t1_1 with
              | CedarType.boolType B => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t2_1 with
            | CedarType.recordTypeNil =>
              match t1_1 with
              | CedarType.recordTypeNil => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ => DecOpt.decOpt (BEq.beq t1_1 t2_1) initSize]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match t2_1 with
            | CedarType.boolType (BoolType.anyBool) =>
              match t1_1 with
              | CedarType.boolType B => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t2_1 with
            | CedarType.recordTypeNil =>
              match t1_1 with
              | CedarType.recordTypeNil => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ => DecOpt.decOpt (BEq.beq t1_1 t2_1) initSize, fun _ =>
            match t2_1 with
            | CedarType.setType T2 =>
              match t1_1 with
              | CedarType.setType T1 => aux_dec initSize size' T1 T2
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t2_1 with
            | CedarType.recordTypeCons u_2 u_3 T2 R2 =>
              match t1_1 with
              | CedarType.recordTypeCons A o T1 R1 =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_2 A) initSize,
                    DecOpt.andOptList
                      [DecOpt.decOpt (BEq.beq u_3 o) initSize,
                        DecOpt.andOptList
                          [DecOpt.decOpt (RecordType R2) initSize,
                            DecOpt.andOptList
                              [DecOpt.decOpt (RecordType R1) initSize,
                                DecOpt.andOptList [aux_dec initSize size' T1 T2, aux_dec initSize size' R1 R2]]]]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
    fun size => aux_dec size size t1_1 t2_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (SubType t1 t2)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat CedarType (fun t1_1 => SubType t1_1 t2_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (t2_1 : CedarType) : OptionT Plausible.Gen CedarType :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match t2_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let B ← Plausible.Arbitrary.arbitrary;
                return CedarType.boolType B
              | _ => OptionT.fail),
            (1,
              match t2_1 with
              | CedarType.recordTypeNil => return CedarType.recordTypeNil
              | _ => OptionT.fail),
            (1, return t2_1)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match t2_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let B ← Plausible.Arbitrary.arbitrary;
                return CedarType.boolType B
              | _ => OptionT.fail),
            (1,
              match t2_1 with
              | CedarType.recordTypeNil => return CedarType.recordTypeNil
              | _ => OptionT.fail),
            (1, return t2_1),
            (Nat.succ size',
              match t2_1 with
              | CedarType.setType T2 => do
                let T1 ← aux_arb initSize size' T2;
                return CedarType.setType T1
              | _ => OptionT.fail),
            (Nat.succ size',
              match t2_1 with
              | CedarType.recordTypeCons A o T2 R2 =>
                match DecOpt.decOpt (RecordType R2) initSize with
                | Option.some Bool.true => do
                  let R1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun R1 => RecordType R1) initSize;
                  match DecOpt.decOpt (SubType R1 R2) initSize with
                    | Option.some Bool.true => do
                      let T1 ← aux_arb initSize size' T2;
                      return CedarType.recordTypeCons A o T1 R1
                    | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size t2_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (t1 : CedarType) => SubType t1 t2)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat Prim (fun p_1 => HasTypePrim v_1 p_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (v_1 : Environment) (t_1 : CedarType) : OptionT Plausible.Gen Prim :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match t_1 with
              | CedarType.boolType (BoolType.tt) => return Prim.boolean (Bool.true)
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.boolType (BoolType.ff) => return Prim.boolean (Bool.false)
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.intType => do
                let i ← Plausible.Arbitrary.arbitrary;
                return Prim.int i
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.stringType => do
                let s ← Plausible.Arbitrary.arbitrary;
                return Prim.stringLit s
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.entityType n =>
                match v_1 with
                | Environment.MkEnvironment (Schema.MkSchema ETS ACTS) R =>
                  match DecOpt.decOpt (DefinedEntity ETS n) initSize with
                  | Option.some Bool.true => do
                    let i ← Plausible.Arbitrary.arbitrary;
                    return Prim.entityUID (EntityUID.MkEntityUID n i)
                  | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match t_1 with
              | CedarType.boolType (BoolType.tt) => return Prim.boolean (Bool.true)
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.boolType (BoolType.ff) => return Prim.boolean (Bool.false)
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.intType => do
                let i ← Plausible.Arbitrary.arbitrary;
                return Prim.int i
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.stringType => do
                let s ← Plausible.Arbitrary.arbitrary;
                return Prim.stringLit s
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.entityType n =>
                match v_1 with
                | Environment.MkEnvironment (Schema.MkSchema ETS ACTS) R =>
                  match DecOpt.decOpt (DefinedEntity ETS n) initSize with
                  | Option.some Bool.true => do
                    let i ← Plausible.Arbitrary.arbitrary;
                    return Prim.entityUID (EntityUID.MkEntityUID n i)
                  | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail),
            ]
    fun size => aux_arb size size v_1 t_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (p : Prim) => HasTypePrim v p t)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat CedarType (fun t_1 => HasTypeVar v_1 x_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (v_1 : Environment) (x_1 : Var) : OptionT Plausible.Gen CedarType :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match x_1 with
              | Var.principal =>
                match v_1 with
                | Environment.MkEnvironment s (RequestType.MkRequest P A R C) => return CedarType.entityType P
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              | Var.action =>
                match v_1 with
                | Environment.MkEnvironment s (RequestType.MkRequest P (EntityUID.MkEntityUID n i) R C) =>
                  return CedarType.entityType n
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              | Var.resource =>
                match v_1 with
                | Environment.MkEnvironment s (RequestType.MkRequest P A R C) => return CedarType.entityType R
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              | Var.context =>
                match v_1 with
                | Environment.MkEnvironment s (RequestType.MkRequest P A R C) => do
                  let t_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun t_1 => ReqContextToCedarType C t_1) initSize;
                  return t_1
                | _ => OptionT.fail
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match x_1 with
              | Var.principal =>
                match v_1 with
                | Environment.MkEnvironment s (RequestType.MkRequest P A R C) => return CedarType.entityType P
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              | Var.action =>
                match v_1 with
                | Environment.MkEnvironment s (RequestType.MkRequest P (EntityUID.MkEntityUID n i) R C) =>
                  return CedarType.entityType n
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              | Var.resource =>
                match v_1 with
                | Environment.MkEnvironment s (RequestType.MkRequest P A R C) => return CedarType.entityType R
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match x_1 with
              | Var.context =>
                match v_1 with
                | Environment.MkEnvironment s (RequestType.MkRequest P A R C) => do
                  let t_1 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun t_1 => ReqContextToCedarType C t_1) initSize;
                  return t_1
                | _ => OptionT.fail
              | _ => OptionT.fail),
            ]
    fun size => aux_arb size size v_1 x_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (t : CedarType) => HasTypeVar v x t)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat Var (fun x_1 => HasTypeVar v_1 x_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (v_1 : Environment) (t_1 : CedarType) : OptionT Plausible.Gen Var :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match t_1 with
              | CedarType.entityType u_3 =>
                match v_1 with
                | Environment.MkEnvironment s (RequestType.MkRequest P A R C) =>
                  match DecOpt.decOpt (BEq.beq u_3 P) initSize with
                  | Option.some Bool.true => return Var.principal
                  | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.entityType u_3 =>
                match v_1 with
                | Environment.MkEnvironment s (RequestType.MkRequest P (EntityUID.MkEntityUID n i) R C) =>
                  match DecOpt.decOpt (BEq.beq u_3 n) initSize with
                  | Option.some Bool.true => return Var.action
                  | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.entityType u_3 =>
                match v_1 with
                | Environment.MkEnvironment s (RequestType.MkRequest P A R C) =>
                  match DecOpt.decOpt (BEq.beq u_3 R) initSize with
                  | Option.some Bool.true => return Var.resource
                  | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match v_1 with
              | Environment.MkEnvironment s (RequestType.MkRequest P A R C) =>
                match DecOpt.decOpt (ReqContextToCedarType C t_1) initSize with
                | Option.some Bool.true => return Var.context
                | _ => OptionT.fail
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match t_1 with
              | CedarType.entityType u_3 =>
                match v_1 with
                | Environment.MkEnvironment s (RequestType.MkRequest P A R C) =>
                  match DecOpt.decOpt (BEq.beq u_3 P) initSize with
                  | Option.some Bool.true => return Var.principal
                  | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.entityType u_3 =>
                match v_1 with
                | Environment.MkEnvironment s (RequestType.MkRequest P (EntityUID.MkEntityUID n i) R C) =>
                  match DecOpt.decOpt (BEq.beq u_3 n) initSize with
                  | Option.some Bool.true => return Var.action
                  | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.entityType u_3 =>
                match v_1 with
                | Environment.MkEnvironment s (RequestType.MkRequest P A R C) =>
                  match DecOpt.decOpt (BEq.beq u_3 R) initSize with
                  | Option.some Bool.true => return Var.resource
                  | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match v_1 with
              | Environment.MkEnvironment s (RequestType.MkRequest P A R C) =>
                match DecOpt.decOpt (ReqContextToCedarType C t_1) initSize with
                | Option.some Bool.true => return Var.context
                | _ => OptionT.fail
              | _ => OptionT.fail),
            ]
    fun size => aux_arb size size v_1 t_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (x : Var) => HasTypeVar v x t)

/--
info: Try this checker: instance : DecOpt (BindAttrType ns_1 tef_1 t_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (ns_1 : List EntityName) (tef_1 : CedarType × String × Bool)
      (t_1 : CedarType) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match tef_1 with
            | Prod.mk (CedarType.recordTypeCons x b t r) (Prod.mk u_3 u_4) =>
              DecOpt.andOptList
                [DecOpt.decOpt (BEq.beq u_3 x) initSize,
                  DecOpt.andOptList
                    [DecOpt.decOpt (BEq.beq t t_1) initSize,
                      DecOpt.andOptList
                        [DecOpt.decOpt (BEq.beq u_4 b) initSize, DecOpt.decOpt (WfRecordType ns_1 r) initSize]]]
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match tef_1 with
            | Prod.mk (CedarType.recordTypeCons x b t r) (Prod.mk u_3 u_4) =>
              DecOpt.andOptList
                [DecOpt.decOpt (BEq.beq u_3 x) initSize,
                  DecOpt.andOptList
                    [DecOpt.decOpt (BEq.beq t t_1) initSize,
                      DecOpt.andOptList
                        [DecOpt.decOpt (BEq.beq u_4 b) initSize, DecOpt.decOpt (WfRecordType ns_1 r) initSize]]]
            | _ => Option.some Bool.false,
            fun _ =>
            match tef_1 with
            | Prod.mk (CedarType.recordTypeCons y i t r) (Prod.mk x b) =>
              DecOpt.andOptList
                [DecOpt.decOpt (Eq (bne x y) (Bool.true)) initSize,
                  DecOpt.andOptList
                    [DecOpt.decOpt (WfRecordType ns_1 r) initSize,
                      aux_dec initSize size' ns_1 (Prod.mk r (Prod.mk x b)) t_1]]
            | _ => Option.some Bool.false]
    fun size => aux_dec size size ns_1 tef_1 t_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (BindAttrType ns tef t)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (CedarType × String × Bool) (fun tef_1 => BindAttrType ns_1 tef_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ns_1 : List EntityName) (t_1 : CedarType) :
      OptionT Plausible.Gen (CedarType × String × Bool) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1, do
              let r ← ArbitrarySizedSuchThat.arbitrarySizedST (fun r => WfRecordType ns_1 r) initSize;
              do
                let b ← Plausible.Arbitrary.arbitrary;
                do
                  let x ← Plausible.Arbitrary.arbitrary;
                  return Prod.mk (CedarType.recordTypeCons x b t_1 r) (Prod.mk x b))]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1, do
              let r ← ArbitrarySizedSuchThat.arbitrarySizedST (fun r => WfRecordType ns_1 r) initSize;
              do
                let b ← Plausible.Arbitrary.arbitrary;
                do
                  let x ← Plausible.Arbitrary.arbitrary;
                  return Prod.mk (CedarType.recordTypeCons x b t_1 r) (Prod.mk x b)),
            (Nat.succ size', do
              let vr_x_b ← aux_arb initSize size' ns_1 t_1;
              match vr_x_b with
                | Prod.mk r (Prod.mk x b) =>
                  match DecOpt.decOpt (WfRecordType ns_1 r) initSize with
                  | Option.some Bool.true => do
                    let i ← Plausible.Arbitrary.arbitrary;
                    do
                      let t ← Plausible.Arbitrary.arbitrary;
                      do
                        let y ← Plausible.Arbitrary.arbitrary;
                        match DecOpt.decOpt (Eq (bne x y) (Bool.true)) initSize with
                          | Option.some Bool.true => return Prod.mk (CedarType.recordTypeCons y i t r) (Prod.mk x b)
                          | _ => OptionT.fail
                  | _ => OptionT.fail
                | _ => OptionT.fail)]
    fun size => aux_arb size size ns_1 t_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (tef : (CedarType × String × Bool)) => BindAttrType ns tef t)


------------------------------------------------------------
-- Generator for well-typed Cedar expressions
------------------------------------------------------------

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (CedarExpr × PathSet) (fun ex_1 => HasType a_1 v_1 ex_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (a_1 : PathSet) (v_1 : Environment) (t_1 : CedarType) :
      OptionT Plausible.Gen (CedarExpr × PathSet) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match t_1 with
              | CedarType.boolType (BoolType.ff) => do
                let P ←
                  ArbitrarySizedSuchThat.arbitrarySizedST
                      (fun P => HasTypePrim v_1 P (CedarType.boolType (BoolType.ff))) initSize;
                return Prod.mk (CedarExpr.lit P) (PathSet.allpaths)
              | _ => OptionT.fail),
            (1,
              match DecOpt.decOpt (Eq (bne t_1 (CedarType.boolType (BoolType.ff))) (Bool.true)) initSize with
              | Option.some Bool.true => do
                let P ← ArbitrarySizedSuchThat.arbitrarySizedST (fun P => HasTypePrim v_1 P t_1) initSize;
                return Prod.mk (CedarExpr.lit P) (PathSet.somepaths (List.nil))
              | _ => OptionT.fail),
            (1, do
              let X ← ArbitrarySizedSuchThat.arbitrarySizedST (fun X => HasTypeVar v_1 X t_1) initSize;
              return Prod.mk (CedarExpr.var X) (PathSet.somepaths (List.nil))),
            (1,
              match t_1 with
              | CedarType.boolType (BoolType.tt) => do
                let P ← Plausible.Arbitrary.arbitrary;
                return
                    Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P) (CedarExpr.lit P))
                      (PathSet.somepaths (List.nil))
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.boolType (BoolType.ff) => do
                let P1 ← Plausible.Arbitrary.arbitrary;
                do
                  let P2 ← Plausible.Arbitrary.arbitrary;
                  match DecOpt.decOpt (Eq (bne P1 P2) (Bool.true)) initSize with
                    | Option.some Bool.true =>
                      return
                        Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P1) (CedarExpr.lit P2))
                          (PathSet.allpaths)
                    | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.recordTypeNil => return Prod.mk (CedarExpr.recExprNil) (PathSet.somepaths (List.nil))
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match t_1 with
              | CedarType.boolType (BoolType.ff) => do
                let P ←
                  ArbitrarySizedSuchThat.arbitrarySizedST
                      (fun P => HasTypePrim v_1 P (CedarType.boolType (BoolType.ff))) initSize;
                return Prod.mk (CedarExpr.lit P) (PathSet.allpaths)
              | _ => OptionT.fail),
            (1,
              match DecOpt.decOpt (Eq (bne t_1 (CedarType.boolType (BoolType.ff))) (Bool.true)) initSize with
              | Option.some Bool.true => do
                let P ← ArbitrarySizedSuchThat.arbitrarySizedST (fun P => HasTypePrim v_1 P t_1) initSize;
                return Prod.mk (CedarExpr.lit P) (PathSet.somepaths (List.nil))
              | _ => OptionT.fail),
            (1, do
              let X ← ArbitrarySizedSuchThat.arbitrarySizedST (fun X => HasTypeVar v_1 X t_1) initSize;
              return Prod.mk (CedarExpr.var X) (PathSet.somepaths (List.nil))),
            (1,
              match t_1 with
              | CedarType.boolType (BoolType.tt) => do
                let P ← Plausible.Arbitrary.arbitrary;
                return
                    Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P) (CedarExpr.lit P))
                      (PathSet.somepaths (List.nil))
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.boolType (BoolType.ff) => do
                let P1 ← Plausible.Arbitrary.arbitrary;
                do
                  let P2 ← Plausible.Arbitrary.arbitrary;
                  match DecOpt.decOpt (Eq (bne P1 P2) (Bool.true)) initSize with
                    | Option.some Bool.true =>
                      return
                        Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P1) (CedarExpr.lit P2))
                          (PathSet.allpaths)
                    | _ => OptionT.fail
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.recordTypeNil => return Prod.mk (CedarExpr.recExprNil) (PathSet.somepaths (List.nil))
              | _ => OptionT.fail),
            (Nat.succ size', do
              let vE1_x1 ← aux_arb initSize size' a_1 v_1 (CedarType.boolType (BoolType.tt));
              match vE1_x1 with
                | Prod.mk E1 x1 => do
                  let vE2_x2 ← aux_arb initSize size' (mergeExprs a_1 x1) v_1 t_1;
                  match vE2_x2 with
                    | Prod.mk E2 x2 => do
                      let E3 ← Plausible.Arbitrary.arbitrary;
                      return Prod.mk (CedarExpr.ite E1 E2 E3) (mergeExprs x1 x2)
                    | _ => OptionT.fail
                | _ => OptionT.fail),
            (Nat.succ size', do
              let vE1_x1 ← aux_arb initSize size' a_1 v_1 (CedarType.boolType (BoolType.ff));
              match vE1_x1 with
                | Prod.mk E1 x1 => do
                  let vE3_x3 ← aux_arb initSize size' a_1 v_1 t_1;
                  match vE3_x3 with
                    | Prod.mk E3 x3 => do
                      let E2 ← Plausible.Arbitrary.arbitrary;
                      return Prod.mk (CedarExpr.ite E1 E2 E3) x3
                    | _ => OptionT.fail
                | _ => OptionT.fail),
            (Nat.succ size', do
              let vE1_E2_x ← aux_arb initSize size' a_1 v_1 t_1;
              match vE1_E2_x with
                | Prod.mk (CedarExpr.ite E1 E2 (CedarExpr.lit (Prim.boolean (Bool.false)))) x =>
                  return Prod.mk (CedarExpr.andExpr E1 E2) x
                | _ => OptionT.fail),
            (Nat.succ size', do
              let vE1_E2_x ← aux_arb initSize size' a_1 v_1 t_1;
              match vE1_E2_x with
                | Prod.mk (CedarExpr.ite E1 (CedarExpr.lit (Prim.boolean (Bool.true))) E2) x =>
                  return Prod.mk (CedarExpr.orExpr E1 E2) x
                | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let ve_x ← aux_arb initSize size' a_1 v_1 (CedarType.boolType (BoolType.anyBool));
                match ve_x with
                  | Prod.mk e x => return Prod.mk (CedarExpr.unaryApp (UnaryOp.not) e) (PathSet.somepaths (List.nil))
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.ff) => do
                let ve_x ← aux_arb initSize size' a_1 v_1 (CedarType.boolType (BoolType.tt));
                match ve_x with
                  | Prod.mk e x => return Prod.mk (CedarExpr.unaryApp (UnaryOp.not) e) (PathSet.allpaths)
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.tt) => do
                let ve_x ← aux_arb initSize size' a_1 v_1 (CedarType.boolType (BoolType.ff));
                match ve_x with
                  | Prod.mk e x => return Prod.mk (CedarExpr.unaryApp (UnaryOp.not) e) (PathSet.somepaths (List.nil))
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.intType => do
                let ve_x ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                match ve_x with
                  | Prod.mk e x => return Prod.mk (CedarExpr.unaryApp (UnaryOp.neg) e) (PathSet.somepaths (List.nil))
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let ve_x ← aux_arb initSize size' a_1 v_1 (CedarType.stringType);
                match ve_x with
                  | Prod.mk e x => do
                    let P ← Plausible.Arbitrary.arbitrary;
                    return Prod.mk (CedarExpr.unaryApp (UnaryOp.like P) e) (PathSet.somepaths (List.nil))
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let vE1_x1 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                match vE1_x1 with
                  | Prod.mk E1 x1 => do
                    let vE2_x2 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                    match vE2_x2 with
                      | Prod.mk E2 x2 =>
                        return Prod.mk (CedarExpr.binaryApp (BinaryOp.less) E1 E2) (PathSet.somepaths (List.nil))
                      | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let vE1_x1 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                match vE1_x1 with
                  | Prod.mk E1 x1 => do
                    let vE2_x2 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                    match vE2_x2 with
                      | Prod.mk E2 x2 =>
                        return Prod.mk (CedarExpr.binaryApp (BinaryOp.lessEq) E1 E2) (PathSet.somepaths (List.nil))
                      | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.intType => do
                let vE1_x1 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                match vE1_x1 with
                  | Prod.mk E1 x1 => do
                    let vE2_x2 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                    match vE2_x2 with
                      | Prod.mk E2 x2 =>
                        return Prod.mk (CedarExpr.binaryApp (BinaryOp.add) E1 E2) (PathSet.somepaths (List.nil))
                      | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.intType => do
                let vE1_x1 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                match vE1_x1 with
                  | Prod.mk E1 x1 => do
                    let vE2_x2 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                    match vE2_x2 with
                      | Prod.mk E2 x2 =>
                        return Prod.mk (CedarExpr.binaryApp (BinaryOp.sub) E1 E2) (PathSet.somepaths (List.nil))
                      | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.intType => do
                let vE1_x1 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                match vE1_x1 with
                  | Prod.mk E1 x1 => do
                    let vE2_x2 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                    match vE2_x2 with
                      | Prod.mk E2 x2 =>
                        return Prod.mk (CedarExpr.binaryApp (BinaryOp.mul) E1 E2) (PathSet.somepaths (List.nil))
                      | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.recordTypeCons i b T TR =>
                match DecOpt.decOpt (RecordType TR) initSize with
                | Option.some Bool.true => do
                  let ve_x ← aux_arb initSize size' a_1 v_1 T;
                  match ve_x with
                    | Prod.mk e x => do
                      let vR_rx ← aux_arb initSize size' a_1 v_1 TR;
                      match vR_rx with
                        | Prod.mk R rx => return Prod.mk (CedarExpr.recExprCons i e R) (PathSet.somepaths (List.nil))
                        | _ => OptionT.fail
                    | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.setType T => do
                let ve_x ← aux_arb initSize size' a_1 v_1 T;
                match ve_x with
                  | Prod.mk e x =>
                    return Prod.mk (CedarExpr.setExprCons e (CedarExpr.setExprNil)) (PathSet.somepaths (List.nil))
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.setType T => do
                let ve_x ← aux_arb initSize size' a_1 v_1 T;
                match ve_x with
                  | Prod.mk e x => do
                    let vR_rx ← aux_arb initSize size' a_1 v_1 (CedarType.setType T);
                    match vR_rx with
                      | Prod.mk R rx => return Prod.mk (CedarExpr.setExprCons e R) (PathSet.somepaths (List.nil))
                      | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail)]
    fun size => aux_arb size size a_1 v_1 t_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (ex : (CedarExpr × PathSet)) => HasType a v ex t)
