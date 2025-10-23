import Test.CedarExample.Cedar
import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Chamelean.GeneratorCombinators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.DeriveEnum

open Plausible

open Cedar


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

/- We override the default `Arbitrary` instance for `String`s with our custom generator -/
instance : ArbitraryFueled String where
  arbitraryFueled _ := GeneratorCombinators.elementsWithDefault
    "Aaron" ["Aaron", "John", "Mike", "Kesha", "Hicks", "A", "B", "C", "D"]

instance : Enum String where
  enum := EnumeratorCombinators.oneOfWithDefault
    (pure "Aaron") (pure <$> ["Aaron", "John", "Mike", "Kesha", "Hicks", "A", "B", "C", "D"])

-- Derive `Arbitrary` instances for Cedar data/types/expressions/schemas
deriving instance Arbitrary for
  EntityName, EntityUID, Prim, Var, PatElem, UnaryOp, BinaryOp, CedarExpr,
  Request, BoolType, CedarType, EntitySchemaEntry, ActionSchemaEntry, Schema,
  RequestType, Environment, PathSet

instance {α} [Arbitrary α] : ArbitraryFueled α where
  arbitraryFueled _ := Arbitrary.arbitrary

deriving instance Enum for
  EntityName, EntityUID, Prim, Var, PatElem, UnaryOp, BinaryOp, CedarExpr,
  Request, BoolType, CedarType, EntitySchemaEntry, ActionSchemaEntry, Schema,
  RequestType, Environment, PathSet

deriving instance BEq for
  EntityName

instance {α : Type} {a : α} [Repr α] [ArbitraryFueled α] [DecidableEq α] : ArbitrarySizedSuchThat α (fun b => a ≠ b) where
  arbitrarySizedST s := do
    let b ← ArbitraryFueled.arbitraryFueled s
    if a = b then
      let b' ← ArbitraryFueled.arbitraryFueled s
      if a = b' then
        throw $ (.genError s!"Failed to generate term not equal to {repr a}")
      else
        return b'
    else
      return b

instance {α : Type} {a : α} [Repr α] [ArbitraryFueled α] [DecidableEq α] : ArbitrarySizedSuchThat α (fun b => b ≠ a) where
  arbitrarySizedST s := do
    let b ← ArbitraryFueled.arbitraryFueled s
    if a = b then
      let b' ← ArbitraryFueled.arbitraryFueled s
      if a = b' then
        throw $ (.genError s!"Failed to generate term not equal to {repr a}")
      else
        return b'
    else
      return b

deriving instance DecidableEq for PathSet
--------------------------------------------------
-- Checker & Generator for `RecordExpr` relation
--------------------------------------------------

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.RecordExpr ce)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (ce : CedarExpr) => Cedar.RecordExpr ce)

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.DefinedName · ·)

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.WfCedarType n r)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (ns_1_1 : List EntityName) => Cedar.DefinedName ns_1_1 n)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (ns_1 : _) => Cedar.WfCedarType ns_1 r)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (ns_1 : List EntityName) => Cedar.WfRecordType ns_1 r)

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.WfRecordType n r)

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.BindAttrType ns TE t)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (ns : _) => Cedar.BindAttrType ns TE t_1)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (E : _) => Cedar.LookupEntityAttr E (fn, b) t_1_1)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (ets : _) => Cedar.GetEntityAttr ets n t_1)

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.SetExpr ce)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (ce : CedarExpr) => Cedar.SetExpr ce)

set_option maxHeartbeats 2000000

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.SetEntityValues ce)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (ce : CedarExpr) => Cedar.SetEntityValues ce)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (rs_1_1 : _) => Cedar.ActionToRequestTypes uid_1 p rs c l_1_1 rs_1_1)

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.DefinedName ns n)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (n : EntityName) => Cedar.DefinedName ns n)

--------------------------------------------------
-- Checker & Generator for `DefinedNames` relation
--------------------------------------------------

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.DefinedNames ns ns0)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (ns0 : List EntityName) => Cedar.DefinedNames ns ns0)

--------------------------------------------------
-- Checker & Generator for well-formed Cedar types
--------------------------------------------------

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.WfCedarType ns ct)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (ct : CedarType) => Cedar.WfCedarType ns ct)

----------------------------------------------------
-- Checker & Generator for well-formed record types
----------------------------------------------------

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.WfRecordType ns rt)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (rt : CedarType) => Cedar.WfRecordType ns rt)

----------------------------------------------------
-- Checker & Generator for well-formed attributes
----------------------------------------------------

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.WfAttrs ns attrs)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (attrs : List (String × Bool × CedarType)) => Cedar.WfAttrs ns attrs)

---------------------------------------------------------------------
-- Checker & Generator for well-formed `EntitySchemaEntry`(ies)
---------------------------------------------------------------------

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.WfET ns et)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (et : EntitySchemaEntry) => Cedar.WfET ns et)

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.WfETS ns ns0 ets)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (ets : List (EntityName × EntitySchemaEntry)) => Cedar.WfETS ns ns0 ets)

---------------------------------------------------------------------
-- Checker & Generator for well-formed `ActionSchemaEntry`(ies)
---------------------------------------------------------------------

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.WfACT ns act)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (act : EntityUID × ActionSchemaEntry) => Cedar.WfACT ns act)

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.WfACTS ns act)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (act : List (EntityUID × ActionSchemaEntry)) => Cedar.WfACTS ns act)

------------------------------------------------------------
-- Checker & Generator for well-formed schemas
------------------------------------------------------------

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.WfSchema ns s)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (s : Schema) => Cedar.WfSchema ns s)

------------------------------------------------------------
-- Checker & Generator for defined entities
------------------------------------------------------------

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.DefinedEntity ets n)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (n : EntityName) => Cedar.DefinedEntity ets n)

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.DefinedEntities ets n)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (n : List EntityName) => Cedar.DefinedEntities ets n)

---------------------------------------------
-- Schema: LookupEntityAttr / GetEntityAttr
---------------------------------------------

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.LookupEntityAttr l fnb t)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (fnb : (String × Bool)) => Cedar.LookupEntityAttr l fnb t)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (nfn : (EntityName × String × Bool)) => Cedar.GetEntityAttr ets nfn t)

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.ReqContextToCedarType c t)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (t : CedarType) => Cedar.ReqContextToCedarType c t)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (reqs : List RequestType) => Cedar.ActionToRequestTypes e n ns l rs reqs)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (reqs : List RequestType) => Cedar.ActionSchemaEntryToRequestTypes e ae ls reqs)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (reqs : List RequestType) => Cedar.ActionSchemaToRequestTypes acts ls reqs)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (es : List Environment) => Cedar.SchemaToEnvironments s l es)

---------------------------------------
-- Checker & Generator for RecordTypes
---------------------------------------

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.RecordType ct)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (ct : CedarType) => Cedar.RecordType ct)

--------------------
-- Subtyping & Typing
--------------------
#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.SubType t1 t2)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (t1 : CedarType) => Cedar.SubType t1 t2)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (p : Prim) => Cedar.HasTypePrim v p t)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (t : CedarType) => Cedar.HasTypeVar v x t)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (x : Var) => Cedar.HasTypeVar v x t)

#guard_msgs(drop info, drop warning) in
#derive_checker (Cedar.BindAttrType ns tef t)

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (tef : (CedarType × String × Bool)) => Cedar.BindAttrType ns tef t)

#guard_msgs(drop info) in
#derive_generator (fun (T : _) => Cedar.BindAttrType ns (TE, F, true) T)

------------------------------------------------------------
-- Generator for well-typed Cedar expressions
------------------------------------------------------------

#guard_msgs(drop info, drop warning) in
#derive_generator (fun (ex : (CedarExpr × PathSet)) => Cedar.HasType a v ex t)
