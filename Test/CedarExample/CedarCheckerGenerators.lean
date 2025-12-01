import Test.CedarExample.Cedar
import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Chamelean.GeneratorCombinators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.DeriveEnum
import Plausible.Attr

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
derive_checker (fun ce => Cedar.RecordExpr ce)

#guard_msgs(drop info, drop warning) in
derive_generator ∃ (ce : CedarExpr), Cedar.RecordExpr ce

#guard_msgs(drop info, drop warning) in
derive_checker (Cedar.DefinedName · ·)

#guard_msgs(drop info, drop warning) in
derive_checker (fun n r => Cedar.WfCedarType n r)

#guard_msgs(drop info, drop warning) in
derive_generator fun n => ∃ (ns_1_1 : List EntityName), Cedar.DefinedName ns_1_1 n

#guard_msgs(drop info, drop warning) in
derive_generator fun r => ∃ ns_1, Cedar.WfCedarType ns_1 r

#guard_msgs(drop info, drop warning) in
derive_generator fun r => ∃ (ns_1 : List EntityName), Cedar.WfRecordType ns_1 r

#guard_msgs(drop info, drop warning) in
derive_checker (fun n r => Cedar.WfRecordType n r)

#guard_msgs(drop info, drop warning) in
derive_checker fun ns TE t => Cedar.BindAttrType ns TE t

#guard_msgs(drop info, drop warning) in
derive_generator fun TE t_1 => ∃ (ns : _), Cedar.BindAttrType ns TE t_1

#guard_msgs(drop info, drop warning) in
derive_generator (fun p t_1_1 => ∃ E, Cedar.LookupEntityAttr E p t_1_1)

#guard_msgs(drop info, drop warning) in
derive_generator (fun n t_1 => ∃ (ets : _), Cedar.GetEntityAttr ets n t_1)

#guard_msgs(drop info, drop warning) in
derive_checker (fun ce => Cedar.SetExpr ce)

#guard_msgs(drop info, drop warning) in
derive_generator ∃ (ce : CedarExpr), Cedar.SetExpr ce

set_option maxHeartbeats 2000000

#guard_msgs(drop info, drop warning) in
derive_checker (fun ce => Cedar.SetEntityValues ce)

#guard_msgs(drop info, drop warning) in
derive_generator ∃ (ce : CedarExpr), Cedar.SetEntityValues ce

#guard_msgs(drop info, drop warning) in
derive_generator (fun uid_1 p rs c l_1_1 => ∃ (rs_1_1 : _), Cedar.ActionToRequestTypes uid_1 p rs c l_1_1 rs_1_1)

#guard_msgs(drop info, drop warning) in
derive_checker (fun ns n => Cedar.DefinedName ns n)

#guard_msgs(drop info, drop warning) in
derive_generator (fun ns => ∃ (n : EntityName), Cedar.DefinedName ns n)

--------------------------------------------------
-- Checker & Generator for `DefinedNames` relation
--------------------------------------------------

#guard_msgs(drop info, drop warning) in
derive_checker (fun ns ns0 => Cedar.DefinedNames ns ns0)

#guard_msgs(drop info, drop warning) in
derive_generator (fun ns => ∃ (ns0 : List EntityName), Cedar.DefinedNames ns ns0)

--------------------------------------------------
-- Checker & Generator for well-formed Cedar types
--------------------------------------------------

#guard_msgs(drop info, drop warning) in
derive_checker (fun ns ct => Cedar.WfCedarType ns ct)

#guard_msgs(drop info, drop warning) in
derive_generator (fun ns => ∃ (ct : CedarType), Cedar.WfCedarType ns ct)

----------------------------------------------------
-- Checker & Generator for well-formed record types
----------------------------------------------------

#guard_msgs(drop info, drop warning) in
derive_checker (fun ns rt => Cedar.WfRecordType ns rt)

#guard_msgs(drop info, drop warning) in
derive_generator (fun ns => ∃ (rt : CedarType), Cedar.WfRecordType ns rt)

----------------------------------------------------
-- Checker & Generator for well-formed attributes
----------------------------------------------------

#guard_msgs(drop info, drop warning) in
derive_checker (fun ns attrs => Cedar.WfAttrs ns attrs)

#guard_msgs(drop info, drop warning) in
derive_generator (fun ns => ∃ (attrs : List (String × Bool × CedarType)), Cedar.WfAttrs ns attrs)

---------------------------------------------------------------------
-- Checker & Generator for well-formed `EntitySchemaEntry`(ies)
---------------------------------------------------------------------

#guard_msgs(drop info, drop warning) in
derive_checker (fun ns et => Cedar.WfET ns et)

#guard_msgs(drop info, drop warning) in
derive_generator (fun ns => ∃ (et : EntitySchemaEntry), Cedar.WfET ns et)

#guard_msgs(drop info, drop warning) in
derive_checker (fun ns ns0 ets => Cedar.WfETS ns ns0 ets)

#guard_msgs(drop info, drop warning) in
derive_generator (fun ns ns0 => ∃ (ets : List (EntityName × EntitySchemaEntry)), Cedar.WfETS ns ns0 ets)

---------------------------------------------------------------------
-- Checker & Generator for well-formed `ActionSchemaEntry`(ies)
---------------------------------------------------------------------

#guard_msgs(drop info, drop warning) in
derive_checker (fun ns act => Cedar.WfACT ns act)

#guard_msgs(drop info, drop warning) in
derive_generator (fun ns => ∃ (act : EntityUID × ActionSchemaEntry), Cedar.WfACT ns act)

#guard_msgs(drop info, drop warning) in
derive_checker (fun ns act => Cedar.WfACTS ns act)

#guard_msgs(drop info, drop warning) in
derive_generator (fun ns => ∃ (act : List (EntityUID × ActionSchemaEntry)), Cedar.WfACTS ns act)

------------------------------------------------------------
-- Checker & Generator for well-formed schemas
------------------------------------------------------------

#guard_msgs(drop info, drop warning) in
derive_checker (fun ns s => Cedar.WfSchema ns s)

#guard_msgs(drop info, drop warning) in
derive_generator (fun ns => ∃ (s : Schema), Cedar.WfSchema ns s)

------------------------------------------------------------
-- Checker & Generator for defined entities
------------------------------------------------------------

#guard_msgs(drop info, drop warning) in
derive_checker (fun ets n => Cedar.DefinedEntity ets n)

#guard_msgs(drop info, drop warning) in
derive_generator (fun ets => ∃ (n : EntityName), Cedar.DefinedEntity ets n)

#guard_msgs(drop info, drop warning) in
derive_checker (fun ets n => Cedar.DefinedEntities ets n)

#guard_msgs(drop info, drop warning) in
derive_generator (fun ets => ∃ (n : List EntityName), Cedar.DefinedEntities ets n)

---------------------------------------------
-- Schema: LookupEntityAttr / GetEntityAttr
---------------------------------------------

#guard_msgs(drop info, drop warning) in
derive_checker (fun l fnb t => Cedar.LookupEntityAttr l fnb t)

#guard_msgs(drop info, drop warning) in
derive_generator (fun l t => ∃ (fnb : (String × Bool)), Cedar.LookupEntityAttr l fnb t)

#guard_msgs(drop info, drop warning) in
derive_generator (fun ets t => ∃ (nfn : (EntityName × String × Bool)), Cedar.GetEntityAttr ets nfn t)

#guard_msgs(drop info, drop warning) in
derive_checker (fun c t => Cedar.ReqContextToCedarType c t)

#guard_msgs(drop info, drop warning) in
derive_generator (fun c => ∃ (t : CedarType), Cedar.ReqContextToCedarType c t)

#guard_msgs(drop info, drop warning) in
derive_generator (fun e n ns l rs => ∃ (reqs : List RequestType), Cedar.ActionToRequestTypes e n ns l rs reqs)

#guard_msgs(drop info, drop warning) in
derive_generator (fun e ae ls => ∃ (reqs : List RequestType), Cedar.ActionSchemaEntryToRequestTypes e ae ls reqs)

#guard_msgs(drop info, drop warning) in
derive_generator (fun acts ls => ∃ (reqs : List RequestType), Cedar.ActionSchemaToRequestTypes acts ls reqs)

#guard_msgs(drop info, drop warning) in
derive_generator (fun s l => ∃ (es : List Environment), Cedar.SchemaToEnvironments s l es)

---------------------------------------
-- Checker & Generator for RecordTypes
---------------------------------------

#guard_msgs(drop info, drop warning) in
derive_checker (fun ct => Cedar.RecordType ct)

#guard_msgs(drop info, drop warning) in
derive_generator ∃ (ct : CedarType), Cedar.RecordType ct

--------------------
-- Subtyping & Typing
--------------------
#guard_msgs(drop info, drop warning) in
derive_checker (fun t1 t2 => Cedar.SubType t1 t2)

#guard_msgs(drop info, drop warning) in
derive_generator (fun t2 => ∃ (t1 : CedarType), Cedar.SubType t1 t2)

#guard_msgs(drop info, drop warning) in
derive_generator (fun v t => ∃ (p : Prim), Cedar.HasTypePrim v p t)

#guard_msgs(drop info, drop warning) in
derive_generator (fun v x => ∃ (t : CedarType), Cedar.HasTypeVar v x t)

#guard_msgs(drop info, drop warning) in
derive_generator (fun v t => ∃ (x : Var), Cedar.HasTypeVar v x t)

#guard_msgs(drop info, drop warning) in
derive_checker (fun ns tef t => Cedar.BindAttrType ns tef t)



#guard_msgs(drop info, drop warning) in
derive_generator (fun ns t => ∃ (tef : (CedarType × String × Bool)), Cedar.BindAttrType ns tef t)

#guard_msgs(drop info) in
derive_generator (fun ns p => ∃ (T : _), Cedar.BindAttrType ns p T)

------------------------------------------------------------
-- Generator for well-typed Cedar expressions
------------------------------------------------------------
#guard_msgs(drop info, drop warning) in
derive_generator (fun a v t => ∃ (ex : (CedarExpr × PathSet)), Cedar.HasType a v ex t)
