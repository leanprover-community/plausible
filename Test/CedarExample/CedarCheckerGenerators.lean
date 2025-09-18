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

#derive_checker (RecordExpr ce)

#derive_generator (fun (ce : CedarExpr) => RecordExpr ce)

-----------------------------------------------
-- Checker & Generator for `SetExpr` relation
-----------------------------------------------

#derive_checker (SetExpr ce)

#derive_generator (fun (ce : CedarExpr) => SetExpr ce)

--------------------------------------------------
-- Checker & Generator for `SetEntityValues` relation
--------------------------------------------------

#derive_checker (SetEntityValues ce)

#derive_generator (fun (ce : CedarExpr) => SetEntityValues ce)

--------------------------------------------------
-- Checker & Generator for `DefinedName` relation
--------------------------------------------------

#derive_checker (DefinedName ns n)

#derive_generator (fun (n : EntityName) => DefinedName ns n)

--------------------------------------------------
-- Checker & Generator for `DefinedNames` relation
--------------------------------------------------

#derive_checker (DefinedNames ns ns0)

#derive_generator (fun (ns0 : List EntityName) => DefinedNames ns ns0)

--------------------------------------------------
-- Checker & Generator for well-formed Cedar types
--------------------------------------------------

#derive_checker (WfCedarType ns ct)

#derive_generator (fun (ct : CedarType) => WfCedarType ns ct)

----------------------------------------------------
-- Checker & Generator for well-formed record types
----------------------------------------------------

#derive_checker (WfRecordType ns rt)

#derive_generator (fun (rt : CedarType) => WfRecordType ns rt)

----------------------------------------------------
-- Checker & Generator for well-formed attributes
----------------------------------------------------

#derive_checker (WfAttrs ns attrs)

#derive_generator (fun (attrs : List (String × Bool × CedarType)) => WfAttrs ns attrs)

---------------------------------------------------------------------
-- Checker & Generator for well-formed `EntitySchemaEntry`(ies)
---------------------------------------------------------------------

#derive_checker (WfET ns et)

#derive_generator (fun (et : EntitySchemaEntry) => WfET ns et)

#derive_checker (WfETS ns ns0 ets)

#derive_generator (fun (ets : List (EntityName × EntitySchemaEntry)) => WfETS ns ns0 ets)

---------------------------------------------------------------------
-- Checker & Generator for well-formed `ActionSchemaEntry`(ies)
---------------------------------------------------------------------

#derive_checker (WfACT ns act)

#derive_generator (fun (act : EntityUID × ActionSchemaEntry) => WfACT ns act)

#derive_checker (WfACTS ns act)

#derive_generator (fun (act : List (EntityUID × ActionSchemaEntry)) => WfACTS ns act)

------------------------------------------------------------
-- Checker & Generator for well-formed schemas
------------------------------------------------------------

#derive_checker (WfSchema ns s)

#derive_generator (fun (s : Schema) => WfSchema ns s)

------------------------------------------------------------
-- Checker & Generator for defined entities
------------------------------------------------------------

#derive_checker (DefinedEntity ets n)

#derive_generator (fun (n : EntityName) => DefinedEntity ets n)

#derive_checker (DefinedEntities ets n)

#derive_generator (fun (n : List EntityName) => DefinedEntities ets n)

---------------------------------------------
-- Schema: LookupEntityAttr / GetEntityAttr
---------------------------------------------

#derive_checker (LookupEntityAttr l fnb t)

#derive_generator (fun (fnb : (String × Bool)) => LookupEntityAttr l fnb t)

#derive_generator (fun (nfn : (EntityName × String × Bool)) => GetEntityAttr ets nfn t)

#derive_checker (ReqContextToCedarType c t)

#derive_generator (fun (t : CedarType) => ReqContextToCedarType c t)

#derive_generator (fun (reqs : List RequestType) => ActionToRequestTypes e n ns l rs reqs)

#derive_generator (fun (reqs : List RequestType) => ActionSchemaEntryToRequestTypes e ae ls reqs)

#derive_generator (fun (reqs : List RequestType) => ActionSchemaToRequestTypes acts ls reqs)

#derive_generator (fun (es : List Environment) => SchemaToEnvironments s l es)

---------------------------------------
-- Checker & Generator for RecordTypes
---------------------------------------

#derive_checker (RecordType ct)

#derive_generator (fun (ct : CedarType) => RecordType ct)

--------------------
-- Subtyping & Typing
--------------------
#derive_checker (SubType t1 t2)

#derive_generator (fun (t1 : CedarType) => SubType t1 t2)

#derive_generator (fun (p : Prim) => HasTypePrim v p t)

#derive_generator (fun (t : CedarType) => HasTypeVar v x t)

#derive_generator (fun (x : Var) => HasTypeVar v x t)

#derive_checker (BindAttrType ns tef t)

#derive_generator (fun (tef : (CedarType × String × Bool)) => BindAttrType ns tef t)


------------------------------------------------------------
-- Generator for well-typed Cedar expressions
------------------------------------------------------------

#derive_generator (fun (ex : (CedarExpr × PathSet)) => HasType a v ex t)
