import Test.CedarExample.Cedar
import Test.CedarExample.CedarCheckerGenerators
import Plausible.Gen

open Plausible


/-!
This file invokes the generator for well-typed Cedar terms, defined in `Test/CedarExample.CedarCheckerGenerators.lean`.

Note: the structure of this file closely follows Mike Hicks's Coq formalization of Cedar (not publicly available).
-/

open Cedar

/-- Schema based on one of Cedar's sample apps -/
private def schema : Schema :=
  -- entity types
  let team := EntityName.MkName "Team" []
  let teamDef := EntitySchemaEntry.MkEntitySchemaEntry [team] []
  let user := EntityName.MkName "User" []
  let userDef := EntitySchemaEntry.MkEntitySchemaEntry [team] [("manager", true, CedarType.entityType user)]
  let lst := EntityName.MkName "List" []
  let lstDef := EntitySchemaEntry.MkEntitySchemaEntry [] [
    ("owner", true, CedarType.entityType user),
    ("readers", true, CedarType.entityType team),
    ("editors", true, CedarType.entityType team),
    ("age", true, CedarType.intType),
    ("description", true, CedarType.stringType)]
  let app := EntityName.MkName "Application" []
  let appDef := EntitySchemaEntry.MkEntitySchemaEntry [] []
  let action := EntityName.MkName "Action" []
  let actionDef := EntitySchemaEntry.MkEntitySchemaEntry [action] []
  let ets := [
    (user, userDef),
    (team, teamDef),
    (lst, lstDef),
    (app, appDef),
    (action, actionDef)]
  -- action defs
  let getAct := ActionSchemaEntry.MkActionSchemaEntry [user] [lst] []
  let createAct := ActionSchemaEntry.MkActionSchemaEntry [user] [app] []
  let updateAct := ActionSchemaEntry.MkActionSchemaEntry [user] [lst] []
  let acts := [
    ((EntityUID.MkEntityUID action "getList"), getAct),
    ((EntityUID.MkEntityUID action "createList"), createAct),
    ((EntityUID.MkEntityUID action "updateList"), updateAct)]
  Schema.MkSchema ets acts

/- A generator for well-typed Cedar expressions, using the derived generators for `RequestTypes`, environments and expressions -/
private def genCedarExpr (fuel : Nat) : Gen CedarExpr :=
  match schema with
  | .MkSchema ets acts => do
    -- Generates `RequestTypes` based on the schema
    let reqs ← ArbitrarySizedSuchThat.arbitrarySizedST (fun rs => ActionSchemaToRequestTypes acts [] rs) fuel
    -- Generate a list of environments `envs`
    let envs ← ArbitrarySizedSuchThat.arbitrarySizedST (fun es => SchemaToEnvironments (.MkSchema ets acts) reqs es) fuel
    match envs with
    | v :: _ => do
      -- Generate a well-typed expression from the first environment `v` in `es`
      let (expr, _) ← ArbitrarySizedSuchThat.arbitrarySizedST (fun e => HasType (.somepaths []) v e (.boolType .anyBool)) fuel
      return expr
    | [] => throw Gen.genericFailure

/- Below are some Cedar expressions that are produced by the generator above.
Note that these are *not* well-typed Cedar expressions, because we commented out 18 out of the 41 typing rules in `HasType`
as Chamelean took too long to derive the generators for those cases -- see `Test/CedarExample/Cedar.lean` for more details.

```
6 < (5 - 1)

if (if true then John::"John" == John::"John" else action) then
  Hicks like ""
else
  nil

if false then
  { Mike: action }nil
else
  Aaron like ""

if (if A::Kesha::"D" == Aaron then nil else Hicks == Hicks) then
  Mike like ""
else
  { Hicks: if {} then nil else nil }{ D: Hicks }nil

1 <= if false then
  { B: B < true }{ B: action || principal }(2).B
else
  3

(0 - 0) < (0 * 3)

if John::Kesha::Hicks::Hicks::Hicks::Hicks::A::"D" == 0 then
  { D: action }if (nil::-1)::{ Hicks: nil }context.A then
    resource
  else
    nil && action has John
else
  -1 <= -3
```

-/
deriving instance Repr for RequestType

#guard_msgs(drop info) in
#eval Gen.printSamples $ (
  let team := EntityName.MkName "Team" []
  let teamDef := EntitySchemaEntry.MkEntitySchemaEntry [team] []
  let user := EntityName.MkName "User" []
  let userDef := EntitySchemaEntry.MkEntitySchemaEntry [team] [("manager", true, CedarType.entityType user)]
  let lst := EntityName.MkName "List" []
  let lstDef := EntitySchemaEntry.MkEntitySchemaEntry [] [
    ("owner", true, CedarType.entityType user),
    ("readers", true, CedarType.entityType team),
    ("editors", true, CedarType.entityType team),
    ("age", true, CedarType.intType),
    ("description", true, CedarType.stringType)]
  let app := EntityName.MkName "Application" []
  let appDef := EntitySchemaEntry.MkEntitySchemaEntry [] []
  let action := EntityName.MkName "Action" []
  let actionDef := EntitySchemaEntry.MkEntitySchemaEntry [action] []
  let _ets := [
    (user, userDef),
    (team, teamDef),
    (lst, lstDef),
    (app, appDef),
    (action, actionDef)]
  -- action defs
  let getAct := ActionSchemaEntry.MkActionSchemaEntry [user] [lst] []
  let createAct := ActionSchemaEntry.MkActionSchemaEntry [user] [app] []
  let updateAct := ActionSchemaEntry.MkActionSchemaEntry [user] [lst] []
  let acts := [ ((EntityUID.MkEntityUID action "getList"), getAct),
    ((EntityUID.MkEntityUID action "createList"), createAct),
    ((EntityUID.MkEntityUID action "updateList"), updateAct)]
  ArbitrarySizedSuchThat.arbitrarySizedST (fun rs => ActionSchemaToRequestTypes acts [] rs) 5)

def genSchemaThenCedarExpr (fuel : Nat) : Gen (CedarExpr) := do
  let ns := [EntityName.MkName "EntityType1" [], EntityName.MkName "EntityType2" []]
  -- 1. Generate wf_Schema xs
  let xs ← ArbitrarySizedSuchThat.arbitrarySizedST (fun s => WfSchema ns s) fuel
  match xs with
  -- 2. Generate requestTypes rs from it
  | Schema.MkSchema ets acts => do
    let reqso ← ArbitrarySizedSuchThat.arbitrarySizedST (fun rs => ActionSchemaToRequestTypes acts [] rs) fuel
    -- 3. Generate environments es from rs and xs
    match reqso with
    | reqs => do
      let envso ← ArbitrarySizedSuchThat.arbitrarySizedST (fun es => SchemaToEnvironments (Schema.MkSchema ets acts) reqs es) fuel
      -- 4. Generate a well-typed expression from v, the head of es
      match envso with
      | v :: _ => do
        let eps ← ArbitrarySizedSuchThat.arbitrarySizedST (fun e => HasType (.somepaths []) v e (.boolType .anyBool)) fuel
        match eps with
        | (expr, _) => return expr
      | _ => throw Gen.genericFailure

#guard_msgs(drop info) in
#eval Gen.printSamples (genCedarExpr 2)

#guard_msgs(drop info) in
#eval Gen.printSamples (genSchemaThenCedarExpr 3)
