-- Import linter from batteries to suppress "missing documentation" linter warnings
import Batteries.Tactic.Lint

import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Chamelean.GeneratorCombinators
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.DeriveConstrainedProducer

open Plausible

/-!
This file contains a Lean formalization of the Cedar policy language (OOPSLA '24),
adapted from Mike Hicks's Coq formalization (not publicly available).
-/

namespace Cedar

------------------------------------
-- Part One: Cedar expression syntax
-------------------------------------

/-- The name of an entity -/
inductive EntityName where
| MkName : String → List String → EntityName
deriving Repr, BEq, DecidableEq

/-- Entity UIDs -/
inductive EntityUID where
| MkEntityUID : EntityName → String → EntityUID
deriving Repr, BEq, DecidableEq

/-- Primitive values -/
inductive Prim where
| boolean (b : Bool)
| int (i : Int)
| stringLit (s : String)
| entityUID (e : EntityUID)
deriving Repr, BEq, DecidableEq

/-- Variables -/
inductive Var where
| principal
| action
| resource
| context
deriving Repr, BEq, DecidableEq

/-- Pattern elements -/
inductive PatElem where
| star
| justLit (s : String)
deriving Repr, BEq, DecidableEq

/-- Unary operations -/
inductive UnaryOp where
| not
| neg
| like (p : List PatElem)
| is (ety : EntityName)
deriving Repr, BEq, DecidableEq

/-- Binary operations -/
inductive BinaryOp where
| equals
| mem
| less
| lessEq
| add
| sub
| mul
| contains
| containsAll
| containsAny
deriving Repr, BEq, DecidableEq

/-- Cedar expressions. Note:
    - We call this datatype `CedarExpr` to avoid naming conflicts with Lean's `Expr` datatype
    - We "inline" list constructors for sets and records to avoid issue with mutual recursion in a list/generic type -/
inductive CedarExpr where
| lit (p : Prim)
| var (v : Var)
| ite (cond : CedarExpr) (thenExpr : CedarExpr) (elseExpr : CedarExpr)
| andExpr (a : CedarExpr) (b : CedarExpr)
| orExpr (a : CedarExpr) (b : CedarExpr)
| unaryApp (op : UnaryOp) (expr : CedarExpr)
| binaryApp (op : BinaryOp) (a : CedarExpr) (b : CedarExpr)
| getAttr (expr : CedarExpr) (attr : String)
| hasAttr (expr : CedarExpr) (attr : String)
| setExprNil
| setExprCons (e : CedarExpr) (ls : CedarExpr)
| recExprNil
| recExprCons (s : String) (e : CedarExpr) (attrs : CedarExpr)
deriving BEq, DecidableEq

/-- Type of entity data.
    Precondition: the `Expr` argument should always be a record of values -/
inductive EntityData where
| MkEntityData : CedarExpr → List EntityUID → EntityData
deriving BEq, DecidableEq

/-- given `MkReq P A R C`, assumes that `RecordExpr C` and `Value C` hold --/
inductive Request where
| MkReq : EntityUID → EntityUID → EntityUID → CedarExpr → Request
deriving BEq, DecidableEq

-------------------------------------------------
-- Part Two: Pretty Printing Cedar Expressions
-------------------------------------------------

/-- Converts the arguments to an `EntityName` to a String -/
def stringOfEntityName (ps : List String) (t : String) : String :=
  match ps with
  | [] => t
  | p::ps' => p ++ "::" ++ stringOfEntityName ps' t

instance : ToString EntityName where
  toString := fun b =>
    match b with
    | .MkName t p => stringOfEntityName p t

/-- Converts an Entity UID to a string -/
def stringOfEntityUID (ps : List String) (t : String) (id : String) : String :=
  stringOfEntityName ps t ++ "::\"" ++ id ++ "\""

instance : ToString EntityUID where
  toString := fun b =>
    match b with
    | EntityUID.MkEntityUID (.MkName t p) id => stringOfEntityUID p t id

/-- Converts a primitive to a string -/
def stringOfPrim (p : Prim) : String :=
  match p with
  | Prim.boolean b => toString b
  | Prim.int i => toString i
  | Prim.stringLit s => toString s
  | Prim.entityUID e => toString e

instance : ToString Prim where
  toString := stringOfPrim

instance : ToString Var where
  toString := fun v => match v with
    | Var.principal => "principal"
    | Var.action => "action"
    | Var.resource => "resource"
    | Var.context => "context"

/-- Converts a `PatElem` to a string -/
def stringOfPatElem (p : PatElem) : String :=
  match p with
  | PatElem.star => "*"
  | PatElem.justLit s => s

/-- Converts a List of `PatElem`s to `String`s -/
def stringOfPats (p : List PatElem) : String :=
  match p with
  | [] => ""
  | p0::ps => stringOfPatElem p0 ++ stringOfPats ps

/-- Converts an `Expr` to a string -/
def stringOfExpr (e : CedarExpr) : String :=
  match e with
  | CedarExpr.lit p => toString p
  | CedarExpr.var v => toString v
  | CedarExpr.ite cond thenExpr elseExpr =>
      "if (" ++ stringOfExpr cond ++ ") then (" ++ stringOfExpr thenExpr ++ ") else (" ++ stringOfExpr elseExpr ++ ")"
  | CedarExpr.andExpr a b => "(" ++ stringOfExpr a ++ ") && (" ++ stringOfExpr b ++ ")"
  | CedarExpr.orExpr a b => "(" ++ stringOfExpr a ++ ") || (" ++ stringOfExpr b ++ ")"
  | CedarExpr.unaryApp op expr =>
    match op with
    | UnaryOp.not => "not (" ++ stringOfExpr expr ++ ")"
    | UnaryOp.neg => "- (" ++ stringOfExpr expr ++ ")"
    | UnaryOp.like ps => "(" ++ stringOfExpr expr ++ ") like \"" ++ stringOfPats ps ++ "\""
    | UnaryOp.is e => "is (" ++ toString e ++ ")"
  | CedarExpr.binaryApp op a b =>
    let sa := "(" ++ stringOfExpr a ++ ")"
    let sb := "(" ++ stringOfExpr b ++ ")"
    match op with
    | BinaryOp.equals => sa ++ "==" ++ sb
    | BinaryOp.mem => sa ++ "in" ++ sb
    | BinaryOp.less => sa ++ "<" ++ sb
    | BinaryOp.lessEq => sa ++ "<=" ++ sb
    | BinaryOp.add => sa ++ "+" ++ sb
    | BinaryOp.sub => sa ++ "-" ++ sb
    | BinaryOp.mul => sa ++ "*" ++ sb
    | BinaryOp.contains => sa ++ ".contains" ++ sb
    | BinaryOp.containsAll => sa ++ ".containsAll" ++ sb
    | BinaryOp.containsAny => sa ++ ".containsAny" ++ sb
  | CedarExpr.getAttr expr attr => "(" ++ stringOfExpr expr ++ ")." ++ attr
  | CedarExpr.hasAttr expr attr => "(" ++ stringOfExpr expr ++ ") has " ++ attr
  | CedarExpr.setExprNil => "nil"
  | CedarExpr.setExprCons e ls => "(" ++ stringOfExpr e ++ ")::" ++ stringOfExpr ls
  | CedarExpr.recExprNil => "{}"
  | CedarExpr.recExprCons s e attrs => "{ " ++ s ++ ": " ++ stringOfExpr e ++ " }" ++ stringOfExpr attrs

instance : ToString CedarExpr where
  toString := stringOfExpr

instance : Repr CedarExpr where
  reprPrec e _ := toString e

instance : ToString Request where
  toString := fun r => match r with
    | Request.MkReq p a res c =>
        "MkReq " ++ toString p ++ " " ++ toString a ++ " " ++ toString res ++ " " ++ toString c

/-- Computes the `depth` of an expression, useful during generation -/
def depthExpr (e : CedarExpr) : Nat :=
  match e with
  | CedarExpr.lit _ => 1
  | CedarExpr.var _ => 1
  | CedarExpr.ite cond thenExpr elseExpr =>
    1 + max (max (depthExpr cond) (depthExpr thenExpr)) (depthExpr elseExpr)
  | CedarExpr.andExpr a b => 1 + max (depthExpr a) (depthExpr b)
  | CedarExpr.orExpr a b => 1 + max (depthExpr a) (depthExpr b)
  | CedarExpr.unaryApp _op expr => 1 + depthExpr expr
  | CedarExpr.binaryApp _op a b => 1 + max (depthExpr a) (depthExpr b)
  | CedarExpr.getAttr expr _attr => 1 + depthExpr expr
  | CedarExpr.hasAttr expr _attr => 1 + depthExpr expr
  | CedarExpr.setExprNil => 1
  | CedarExpr.setExprCons e ls => 1 + max (depthExpr e) (depthExpr ls)
  | CedarExpr.recExprNil => 1
  | CedarExpr.recExprCons _s e attrs => 1 + max (depthExpr e) (depthExpr attrs)

/-- Computes the `size` of an expression, useful during generation -/
def sizeExpr (e : CedarExpr) : Nat :=
  match e with
  | CedarExpr.lit _ => 1
  | CedarExpr.var _ => 1
  | CedarExpr.ite cond thenExpr elseExpr =>
    1 + sizeExpr cond + sizeExpr thenExpr + sizeExpr elseExpr
  | CedarExpr.andExpr a b => 1 + sizeExpr a + sizeExpr b
  | CedarExpr.orExpr a b => 1 + sizeExpr a + sizeExpr b
  | CedarExpr.unaryApp _ expr => 1 + sizeExpr expr
  | CedarExpr.binaryApp _ a b => 1 + sizeExpr a + sizeExpr b
  | CedarExpr.getAttr expr _ => 1 + sizeExpr expr
  | CedarExpr.hasAttr expr _ => 1 + sizeExpr expr
  | CedarExpr.setExprNil => 1
  | CedarExpr.setExprCons e ls => 1 + sizeExpr e + sizeExpr ls
  | CedarExpr.recExprNil => 1
  | CedarExpr.recExprCons _ e attrs => 1 + sizeExpr e + sizeExpr attrs


---------------------------------------
-- Part Three: Cedar expression typing
---------------------------------------
-- Some basic predicates useful for typing

/-- predicate: When an expression is a record -/
inductive RecordExpr : CedarExpr → Prop where
| RENil : RecordExpr CedarExpr.recExprNil
| RECons : ∀ fn e r, RecordExpr (CedarExpr.recExprCons fn e r)

/-- predicate: When an expression is a set -/
inductive SetExpr : CedarExpr → Prop where
| SENil : SetExpr CedarExpr.setExprNil
| SECons : ∀ e r, SetExpr (CedarExpr.setExprCons e r)

/-- predicate: When an expression is a value -/
inductive Value : CedarExpr → Prop where
| VLit : ∀ p, Value (CedarExpr.lit p)
| VSNil : Value CedarExpr.setExprNil
| VSCons : ∀ e ls, Value e → Value ls → Value (CedarExpr.setExprCons e ls)
| VRNil : Value CedarExpr.recExprNil
| VRCons : ∀ s e rs, Value e → Value rs → Value (CedarExpr.recExprCons s e rs)

/-- predicate: When an expression is a set of entity values -/
inductive SetEntityValues : CedarExpr → Prop where
| SEVNil : SetEntityValues CedarExpr.setExprNil
| SEVCons : ∀ uid r,
    SetEntityValues r →
    SetEntityValues (CedarExpr.setExprCons (CedarExpr.lit (Prim.entityUID uid)) r)

------------------------------------------------------
-- Types
------------------------------------------------------

/-- Boolean types -/
inductive BoolType where
| anyBool
| tt
| ff
deriving Repr, BEq, DecidableEq

/-- Types in Cedar -/
inductive CedarType where
| boolType (bty : BoolType)
| intType
| stringType
| entityType (ety : EntityName)
| setType (ty : CedarType)
| recordTypeNil
| recordTypeCons (s : String) (opt : Bool) (ty : CedarType) (rest : CedarType)
deriving BEq, DecidableEq

/-- Determines whether a `CedarType` is a `RecordType` -/
inductive RecordType : CedarType → Prop where
| RTNil : RecordType CedarType.recordTypeNil
| RTCons : ∀ fn o T1 T2, RecordType (CedarType.recordTypeCons fn o T1 T2)

@[nolint docBlame]
inductive DefinedName : List EntityName → EntityName → Prop where
| DNFound : ∀ L A B,
    A = B →
    DefinedName (A::L) B
| DNRest : ∀ L A B,
    A ≠ B →
    DefinedName L A →
    DefinedName (B::L) A

@[nolint docBlame]
inductive DefinedNames : List EntityName → List EntityName → Prop where
| DNSNil : ∀ ns, DefinedNames ns []
| DNSCons : ∀ n ns0 ns,
    DefinedName ns n →
    DefinedNames ns ns0 →
    DefinedNames ns (n::ns0)

/-- Inductive relation specifying well-formedness conditions for Cedar types -/
inductive WfCedarType : List EntityName → CedarType → Prop where
| WfBoolType : ∀ ns B, WfCedarType ns (CedarType.boolType B)
| WfIntType : ∀ ns, WfCedarType ns CedarType.intType
| WfStringType : ∀ ns, WfCedarType ns CedarType.stringType
| WfEntityType : ∀ ns n,
    DefinedName ns n →
    WfCedarType ns (CedarType.entityType n)
| WfSetType : ∀ T ns,
    WfCedarType ns T →
    WfCedarType ns (CedarType.setType T)
| WfRecordTypeNil : ∀ ns, WfCedarType ns CedarType.recordTypeNil
| WfRecordTypeConsNil : ∀ fn o T1 ns,
    WfCedarType ns T1 →
    WfCedarType ns (CedarType.recordTypeCons fn o T1 CedarType.recordTypeNil)
| WfRecordTypeConsCons : ∀ fn o T1 ns fn1 o1 T2 r,
    WfCedarType ns T1 →
    WfCedarType ns (CedarType.recordTypeCons fn1 o1 T2 r) →
    WfCedarType ns (CedarType.recordTypeCons fn o T1 (CedarType.recordTypeCons fn1 o1 T2 r))

/-- Well-formed record types are types that are both well-formed and record types.
    Note: in the original Coq code, this inductive relation is produced using QuickChick's
    ability to merge inductive relations (see "Merging Inductive Relations", PLDI '23).
    Chamelean currently doesn't this ability, so this inductive relation has been
    manually ported over to Lean based on the merged relation produced by QuickChick. -/
inductive WfRecordType : List EntityName → CedarType → Prop where
| WfRecordTypeConsConsRTcons : ∀ fn' o' T1' ns fn1 o1 T2 r,
    WfCedarType ns (.recordTypeCons fn1 o1 T2 r) →
    WfCedarType ns T1' →
    WfRecordType ns (.recordTypeCons fn' o' T1' (.recordTypeCons fn1 o1 T2 r))
| WfRecordTypeConsNilRTcons : ∀ fn' o' T1' ns,
    WfCedarType ns T1' →
    WfRecordType ns (.recordTypeCons fn' o' T1' .recordTypeNil)
| WfRecordTypeNilRTnil : ∀ (ns : List EntityName), WfRecordType ns .recordTypeNil

------------------------------------------------------
-- Schemas
------------------------------------------------------

@[nolint docBlame]
inductive EntitySchemaEntry where
| MkEntitySchemaEntry (ancestors : List EntityName) (attrs : List (String × Bool × CedarType))
deriving BEq, DecidableEq

/-- Well-formed attributes -/
inductive WfAttrs : List EntityName → List (String × Bool × CedarType) → Prop where
| WfAttrsNil : ∀ ns, WfAttrs ns []
| WfAttrsCons : ∀ ns T s b attrs,
    WfCedarType ns T →
    WfAttrs ns attrs →
    WfAttrs ns ((s, b, T)::attrs)

@[nolint docBlame]
inductive WfET : List EntityName → EntitySchemaEntry → Prop where
| WfETSingle : ∀ ns ancs attrs,
    DefinedNames ns ancs →
    WfAttrs ns attrs →
    WfET ns (EntitySchemaEntry.MkEntitySchemaEntry ancs attrs)

@[nolint docBlame]
inductive WfETS : List EntityName → List EntityName → List (EntityName × EntitySchemaEntry) → Prop where
| WfETSSingle : ∀ ns n et,
    DefinedName ns n →
    WfET ns et →
    WfETS ns [n] [(n, et)]
| WfETSCons : ∀ n ns ns0 et ets,
    DefinedName ns n →
    WfET ns et →
    WfETS ns ns0 ets →
    WfETS ns (n::ns0) ((n, et)::ets)

@[nolint docBlame]
inductive ActionSchemaEntry where
| MkActionSchemaEntry (prin : List EntityName) (res : List EntityName) (contextType : List (String × Bool × CedarType))
deriving BEq, DecidableEq

/-- LATER: Allow more than one principal and resource -/
inductive WfACT : List EntityName → (EntityUID × ActionSchemaEntry) → Prop where
| WfACTSingle : ∀ n p r ns s attrs,
    DefinedName ns n →
    DefinedName ns p →
    DefinedName ns r →
    WfAttrs ns attrs →
    WfACT ns ((EntityUID.MkEntityUID n s), (ActionSchemaEntry.MkActionSchemaEntry [p] [r] attrs))

@[nolint docBlame]
inductive WfACTS : List EntityName → List (EntityUID × ActionSchemaEntry) → Prop where
| WfACTSSingle : ∀ ns act,
    WfACT ns act →
    WfACTS ns [act]
| WfACTSCons : ∀ ns act acts,
    WfACT ns act →
    WfACTS ns acts →
    WfACTS ns (act::acts)

@[nolint docBlame]
inductive Schema where
| MkSchema (ets : List (EntityName × EntitySchemaEntry)) (acts : List (EntityUID × ActionSchemaEntry))
deriving BEq, DecidableEq

@[nolint docBlame]
inductive WfSchema : List EntityName → Schema → Prop where
| WfS : ∀ ns ets acts,
    WfETS ns ns ets →
    WfACTS ns acts →
    WfSchema ns (Schema.MkSchema ets acts)

@[nolint docBlame]
inductive DefinedEntity : List (EntityName × EntitySchemaEntry) → EntityName → Prop where
| DENow : ∀ n E R, DefinedEntity ((n, E)::R) n
| DELater : ∀ n n1 E R,
     n ≠ n1 →
    DefinedEntity R n →
    DefinedEntity ((n1, E)::R) n

@[nolint docBlame]
inductive DefinedEntities : List (EntityName × EntitySchemaEntry) → List EntityName → Prop where
| DESNil : DefinedEntities [] []
| DESCons : ∀ n ns et ets,
    DefinedEntities ets ns →
    DefinedEntities ((n, et)::ets) (n::ns)

/-- NB: Ideally the string*bool parameter would be two distinct parameters.
    It's written this way due to current QuickChick/Chamelean limitations on generation. -/
inductive LookupEntityAttr : List (String × Bool × CedarType) → (String × Bool) → CedarType → Prop where
| LUNow : ∀ F B FS TF,
    LookupEntityAttr ((F, B, TF)::FS) (F, B) TF
| LULater : ∀ F1 B1 F2 FS TF B,
    F1 ≠ F2 →
    LookupEntityAttr FS (F1, B1) TF →
    LookupEntityAttr ((F2, B, TF)::FS) (F1, B1) TF

@[nolint docBlame]
inductive GetEntityAttr : List (EntityName × EntitySchemaEntry) → (EntityName × String × Bool) → CedarType → Prop where
| GENow : ∀ n fn b A E R T,
    LookupEntityAttr E (fn, b) T →
    GetEntityAttr ((n, (EntitySchemaEntry.MkEntitySchemaEntry A E))::R) (n, fn, b) T
| GELater : ∀ n n1 fn b E R T,
    n ≠ n1 →
    GetEntityAttr R (n, fn, b) T →
    GetEntityAttr ((n1, E)::R) (n, fn, b) T

------------------------------------------------------
-- Environments
------------------------------------------------------

@[nolint docBlame]
inductive RequestType where
| MkRequest (prin : EntityName) (act : EntityUID) (res : EntityName) (ctxt : List (String × Bool × CedarType))
deriving BEq, DecidableEq

/-- Converts a context description in RequestType to a Cedar record type -/
inductive ReqContextToCedarType : List (String × Bool × CedarType) → CedarType → Prop where
| RNil : ReqContextToCedarType [] CedarType.recordTypeNil
| RCons : ∀ i B T R TR,
    ReqContextToCedarType R TR →
    ReqContextToCedarType ((i, B, T)::R) (CedarType.recordTypeCons i B T TR)

@[nolint docBlame]
inductive ActionToRequestTypes : EntityUID → EntityName → List EntityName → List (String × Bool × CedarType) → List RequestType → List RequestType → Prop where
| ATRTSingle : ∀ uid p r c acc,
    ActionToRequestTypes uid p [r] c acc ((RequestType.MkRequest p uid r c)::acc)
| ATRTCons : ∀ uid p r rs c reqs acc,
    ActionToRequestTypes uid p rs c acc reqs →
    ActionToRequestTypes uid p (r::rs) c acc ((RequestType.MkRequest p uid r c)::reqs)

@[nolint docBlame]
inductive ActionSchemaEntryToRequestTypes : EntityUID → ActionSchemaEntry → List RequestType → List RequestType → Prop where
| ASTRTSingle : ∀ uid p rs c reqs acc,
    ActionToRequestTypes uid p rs c acc reqs →
    ActionSchemaEntryToRequestTypes uid (ActionSchemaEntry.MkActionSchemaEntry [p] rs c) acc reqs
| ASTRTCons : ∀ uid p ps rs c acc reqs reqs',
    ActionToRequestTypes uid p rs c acc reqs' →
    ActionSchemaEntryToRequestTypes uid (ActionSchemaEntry.MkActionSchemaEntry ps rs c) reqs' reqs →
    ActionSchemaEntryToRequestTypes uid (ActionSchemaEntry.MkActionSchemaEntry (p::ps) rs c) acc reqs

@[nolint docBlame]
inductive ActionSchemaToRequestTypes : List (EntityUID × ActionSchemaEntry) → List RequestType → List RequestType → Prop where
| ASTESingle : ∀ uid a acc reqs,
    ActionSchemaEntryToRequestTypes uid a acc reqs →
    ActionSchemaToRequestTypes [(uid, a)] acc reqs
| ASTECons : ∀ uid a ass acc reqs' reqs,
    ActionSchemaEntryToRequestTypes uid a acc reqs' →
    ActionSchemaToRequestTypes ass reqs' reqs →
    ActionSchemaToRequestTypes ((uid, a)::ass) acc reqs

@[nolint docBlame]
inductive Environment where
| MkEnvironment (schema : Schema) (reqType : RequestType)
deriving BEq, DecidableEq

@[nolint docBlame]
inductive SchemaToEnvironments : Schema → List RequestType → List Environment → Prop where
| MkEnvsSingle : ∀ r s,
    SchemaToEnvironments s [r] [(Environment.MkEnvironment s r)]
| MkEnvsCons : ∀ r rs s envs,
    SchemaToEnvironments s rs envs →
    SchemaToEnvironments s (r::rs) ((Environment.MkEnvironment s r)::envs)

------------------------------------------------------
-- Subtyping
------------------------------------------------------

/-- Note: Cedar has no width subtyping, just depth -/
inductive SubType : CedarType → CedarType → Prop where
| SBoolAny : ∀ B,
    SubType (CedarType.boolType B) (CedarType.boolType BoolType.anyBool)
| SSet : ∀ T1 T2,
    SubType T1 T2 →
    SubType (CedarType.setType T1) (CedarType.setType T2)
| SRecEmpty :
    SubType CedarType.recordTypeNil CedarType.recordTypeNil
| SRecAttr : ∀ A o T1 T2 R1 R2,
    SubType T1 T2 →
    RecordType R2 →
    SubType R1 R2 →
    RecordType R1 →
    SubType (CedarType.recordTypeCons A o T1 R1) (CedarType.recordTypeCons A o T2 R2)
| ST : ∀ T, SubType T T

------------------------------------------------------
-- Typing: Primitives and Variables
------------------------------------------------------

@[nolint docBlame]
inductive HasTypePrim : Environment → Prim → CedarType → Prop where
| TTrue : ∀ V, HasTypePrim V (Prim.boolean true) (CedarType.boolType BoolType.tt)
| TFalse : ∀ V, HasTypePrim V (Prim.boolean false) (CedarType.boolType BoolType.ff)
| TInt : ∀ V i, HasTypePrim V (Prim.int i) CedarType.intType
| TString : ∀ V s, HasTypePrim V (Prim.stringLit s) CedarType.stringType
| TEntity : ∀ ETS ACTS n i R,
    DefinedEntity ETS n →
    HasTypePrim
      (Environment.MkEnvironment (Schema.MkSchema ETS ACTS) R)
      (Prim.entityUID (EntityUID.MkEntityUID n i))
      (CedarType.entityType n)

@[nolint docBlame]
inductive HasTypeVar : Environment → Var → CedarType → Prop where
| TPrincipal : ∀ s P A R C,
    HasTypeVar (Environment.MkEnvironment s (RequestType.MkRequest P A R C)) Var.principal (CedarType.entityType P)
| TAction : ∀ s P n i R C,
    HasTypeVar (Environment.MkEnvironment s (RequestType.MkRequest P (EntityUID.MkEntityUID n i) R C)) Var.action (CedarType.entityType n)
| TResource : ∀ s P A R C,
    HasTypeVar (Environment.MkEnvironment s (RequestType.MkRequest P A R C)) Var.resource (CedarType.entityType R)
| TContext : ∀ s P A R C T,
    ReqContextToCedarType C T →
    HasTypeVar (Environment.MkEnvironment s (RequestType.MkRequest P A R C)) Var.context T

@[nolint docBlame]
inductive BindAttrType : List EntityName → (CedarType × String × Bool) → CedarType → Prop where
| BindNow : ∀ x t b r ns,
    WfRecordType ns r →
    BindAttrType ns ((CedarType.recordTypeCons x b t r), x, b) t
| BindLater : ∀ x y b i t1 t r ns,
    x ≠ y →
    WfRecordType ns r →
    BindAttrType ns (r, x, b) t1 →
    BindAttrType ns ((CedarType.recordTypeCons y i t r), x, b) t1

/-- A PathSet is a Cedar typing "capability" -- it is a set of accessible record-access expressions, or infinity (meaning all are accessible) -/
inductive PathSet where
| allpaths
| somepaths (paths : List CedarExpr)
deriving Repr, BEq

------------------------------------------------------
-- Typing: Defining "Capabilities" for record acmercess
------------------------------------------------------

/-- Membership test of `x` in `ps` -/
def validPathExpr (x : CedarExpr) (ps : PathSet) : Bool :=
  let rec aux (xs : List CedarExpr) : Bool :=
    match xs with
    | [] => false
    | y::ys =>
        if x == y then true else aux ys
  match ps with
  | PathSet.allpaths => true
  | PathSet.somepaths xs => aux xs

/-- Intersects two pathsets -/
def interExprs (ps : PathSet) (ys : PathSet) : PathSet :=
  let rec aux (xs : List CedarExpr) : List CedarExpr :=
    match xs with
    | [] => []
    | x::xs' =>
        if validPathExpr x ys then x::(aux xs')
        else aux xs'
  match ps with
  | PathSet.allpaths => ys
  | PathSet.somepaths xs => PathSet.somepaths (aux xs)

/-- returns `l` with `x` removed -/
def subExprs (x : CedarExpr) (l : List CedarExpr) : List CedarExpr :=
   match l with
   | [] => []
   | y::ys =>
      if x == y then ys
      else y::(subExprs x ys)

/-- union of `xs` and `ys` -/
def mergeExprs (xs : PathSet) (ys : PathSet) : PathSet :=
  let rec aux (xs : List CedarExpr) (ys : List CedarExpr) : List CedarExpr :=
    match xs with
    | [] => ys
    | x::xs' => x::(aux xs' (subExprs x ys))
  match xs with
  | PathSet.allpaths => PathSet.allpaths
  | PathSet.somepaths xs0 =>
    match ys with
    | PathSet.allpaths => PathSet.allpaths
    | PathSet.somepaths ys0 => PathSet.somepaths (aux xs0 ys0)

-------------------------
-- Typing: Expressions
-------------------------

/-- `HasType a v (e,x) t` is equivalent to `a,v ⊢ e : t ; x` in the paper. This is
  Written assuming we will derive a generator for (e,x) given a v and t (ideally e and x would be their own parameters).

   Note: Chamelean can only handle 23 out of the 41 typing rules --
   if we give it all 41 typing rules, it takes > 5 minutes to derive a generator. I've kept the 23 typing rules
   for which we can derive a generator quickly.

   (I've commented out the remaining 18 typing rules, all of which involve *multiple* constraints expressed via auxiliary relations,
   e.g. Subtyping, DefinedEntities, WfCedarType.) -/
inductive HasType : PathSet → Environment → (CedarExpr × PathSet) → CedarType → Prop where
| TLitFalse : ∀ a V P,
    HasTypePrim V P (CedarType.boolType BoolType.ff) →
    HasType a V ((CedarExpr.lit P), PathSet.allpaths) (CedarType.boolType BoolType.ff)
| TLitOther : ∀ a V P T,
    T ≠ (CedarType.boolType BoolType.ff) →
    HasTypePrim V P T →
    HasType a V ((CedarExpr.lit P), PathSet.somepaths []) T
| TVar : ∀ a V X T,
    HasTypeVar V X T →
    HasType a V ((CedarExpr.var X), PathSet.somepaths []) T
| TCondTrue : ∀ a V E1 E2 E3 x1 x2 T2,
    HasType a V (E1, x1) (CedarType.boolType BoolType.tt) →
    HasType (mergeExprs a x1) V (E2, x2) T2 →
    u = mergeExprs x1 x2 →
    HasType a V ((CedarExpr.ite E1 E2 E3), u) T2
| TCondFalse : ∀ a V E1 E2 E3 x1 x3 T3,
    HasType a V (E1, x1) (CedarType.boolType BoolType.ff) →
    HasType a V (E3, x3) T3 →
    HasType a V ((CedarExpr.ite E1 E2 E3), x3) T3
| TAnd : ∀ a x V E1 E2 T1,
    HasType a V ((CedarExpr.ite E1 E2 (CedarExpr.lit (Prim.boolean false))), x) T1 →
    HasType a V ((CedarExpr.andExpr E1 E2), x) T1
| TOr : ∀ a x V E1 E2 T1,
    HasType a V ((CedarExpr.ite E1 (CedarExpr.lit (Prim.boolean true)) E2), x) T1 →
    HasType a V ((CedarExpr.orExpr E1 E2), x) T1
| TNotAny : ∀ a x V e,
    HasType a V (e, x) (CedarType.boolType BoolType.anyBool) →
    HasType a V ((CedarExpr.unaryApp UnaryOp.not e), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TNotTrue : ∀ a x V e,
    HasType a V (e, x) (CedarType.boolType BoolType.tt) →
    HasType a V ((CedarExpr.unaryApp UnaryOp.not e), PathSet.allpaths) (CedarType.boolType BoolType.ff)
| TNotFalse : ∀ a x V e,
    HasType a V (e, x) (CedarType.boolType BoolType.ff) →
    HasType a V ((CedarExpr.unaryApp UnaryOp.not e), PathSet.somepaths []) (CedarType.boolType BoolType.tt)
| TNeg : ∀ a V x e,
    HasType a V (e, x) CedarType.intType →
    HasType a V ((CedarExpr.unaryApp UnaryOp.neg e), PathSet.somepaths []) CedarType.intType
| TLike : ∀ a V e x P,
    HasType a V (e, x) CedarType.stringType →
    HasType a V ((CedarExpr.unaryApp (UnaryOp.like P) e), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TEqLitTrue : ∀ a V P,
    HasType a V ((CedarExpr.binaryApp BinaryOp.equals (CedarExpr.lit P) (CedarExpr.lit P)), PathSet.somepaths []) (CedarType.boolType BoolType.tt)
| TEqLitFalse : ∀ a V P1 P2,
    P1 ≠ P2 →
    HasType a V ((CedarExpr.binaryApp BinaryOp.equals (CedarExpr.lit P1) (CedarExpr.lit P2)), PathSet.allpaths) (CedarType.boolType BoolType.ff)
| TLessThan : ∀ a x1 x2 V E1 E2,
    HasType a V (E1, x1) CedarType.intType →
    HasType a V (E2, x2) CedarType.intType →
    HasType a V ((CedarExpr.binaryApp BinaryOp.less E1 E2), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TLessEqualThan : ∀ a x1 x2 V E1 E2,
    HasType a V (E1, x1) CedarType.intType →
    HasType a V (E2, x2) CedarType.intType →
    HasType a V ((CedarExpr.binaryApp BinaryOp.lessEq E1 E2), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TAdd : ∀ a x1 x2 V E1 E2,
    HasType a V (E1, x1) CedarType.intType →
    HasType a V (E2, x2) CedarType.intType →
    HasType a V ((CedarExpr.binaryApp BinaryOp.add E1 E2), PathSet.somepaths []) CedarType.intType
| TSub : ∀ a x1 x2 V E1 E2,
    HasType a V (E1, x1) CedarType.intType →
    HasType a V (E2, x2) CedarType.intType →
    HasType a V ((CedarExpr.binaryApp BinaryOp.sub E1 E2), PathSet.somepaths []) CedarType.intType
| TMul : ∀ a x1 x2 V E1 E2,
    HasType a V (E1, x1) CedarType.intType →
    HasType a V (E2, x2) CedarType.intType →
    HasType a V ((CedarExpr.binaryApp BinaryOp.mul E1 E2), PathSet.somepaths []) CedarType.intType
| TRecNil : ∀ a V, HasType a V (CedarExpr.recExprNil, PathSet.somepaths []) CedarType.recordTypeNil
| TRecCons : ∀ a x rx V e i T R b TR,
    HasType a V (e, x) T →
    RecordType TR →
    HasType a V (R, rx) TR →
    HasType a V ((CedarExpr.recExprCons i e R), PathSet.somepaths []) (CedarType.recordTypeCons i b T TR)
| TSetSingle : ∀ a x V e T,
    HasType a V (e, x) T →
    HasType a V ((CedarExpr.setExprCons e CedarExpr.setExprNil), PathSet.somepaths []) (CedarType.setType T)
| TSetMany : ∀ a x rx V e T R,
    HasType a V (e, x) T →
    HasType a V (R, rx) (CedarType.setType T) →
    HasType a V ((CedarExpr.setExprCons e R), PathSet.somepaths []) (CedarType.setType T)
| TIsTrue : ∀ a x V e n ets acts R ns,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns (CedarType.entityType n) →
    HasType a V (e, x) (CedarType.entityType n) →
    HasType a V ((CedarExpr.unaryApp (UnaryOp.is n) e), PathSet.somepaths []) (CedarType.boolType BoolType.tt)
| TIsFalse : ∀ a x V e N1 N2 ets acts R ns,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns (CedarType.entityType N1) →
    HasType a V (e, x) (CedarType.entityType N2) →
    N1 ≠ N2 →
    HasType a V ((CedarExpr.unaryApp (UnaryOp.is N1) e), PathSet.allpaths) (CedarType.boolType BoolType.ff)
| TCondBool : ∀ a V E1 E2 E3 x1 x2 x3 T2 T3 T u,
    SubType T2 T → SubType T3 T →
    HasType a V (E1, x1) (CedarType.boolType BoolType.anyBool) →
    HasType (mergeExprs a x1) V (E2, x2) T2 →
    HasType a V (E3, x3) T3 →
    u = interExprs (mergeExprs x1 x2) x3 →
    HasType a V ((CedarExpr.ite E1 E2 E3), u) T
| TEqEntity : ∀ a x1 x2 V E1 N1 E2 N2 ns ets acts R,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns (CedarType.entityType N1) →
    WfCedarType ns (CedarType.entityType N2) →
    N1 ≠ N2 →
    HasType a V (E1, x1) (CedarType.entityType N1) →
    HasType a V (E2, x2) (CedarType.entityType N2) →
    HasType a V ((CedarExpr.binaryApp BinaryOp.equals E1 E2), PathSet.allpaths) (CedarType.boolType BoolType.ff)
| TEqAny : ∀ a x1 x2 V E1 E2 T T1 T2 ets acts R ns,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns T →
    SubType T1 T → SubType T2 T →
    HasType a V (E1, x1) T1 →
    HasType a V (E2, x2) T2 →
    HasType a V ((CedarExpr.binaryApp BinaryOp.equals E1 E2), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TInEntity : ∀ a x1 x2 V E1 E2 N1 N2 ns ets acts R,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns (CedarType.entityType N1) →
    WfCedarType ns (CedarType.entityType N2) →
    HasType a V (E1, x1) (CedarType.entityType N1) →
    HasType a V (E2, x2) (CedarType.entityType N2) →
    HasType a V ((CedarExpr.binaryApp BinaryOp.mem E1 E2), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TInEntitySet : ∀ a x1 x2 V E1 E2 N1 N2 ns ets acts R,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns (CedarType.entityType N1) →
    WfCedarType ns (CedarType.entityType N2) →
    HasType a V (E1, x1) (CedarType.entityType N1) →
    HasType a V (E2, x2) (CedarType.setType (CedarType.entityType N2)) →
    HasType a V ((CedarExpr.binaryApp BinaryOp.mem E1 E2), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TContains : ∀ a x1 x2 V E1 E2 ets acts R ns T1 T2 T,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns T →
    SubType T1 T → SubType T2 T →
    HasType a V (E1, x1) T1 →
    HasType a V (E2, x2) (CedarType.setType T2) →
    HasType a V ((CedarExpr.binaryApp BinaryOp.contains E1 E2), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TContainsAll : ∀ a x1 x2 V E1 E2 ets acts R ns T1 T2 T,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns T →
    SubType T1 T → SubType T2 T →
    HasType a V (E1, x1) (CedarType.setType T1) →
    HasType a V (E2, x2) (CedarType.setType T2) →
    HasType a V ((CedarExpr.binaryApp BinaryOp.containsAll E1 E2), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| TContainsAny : ∀ a x1 x2 V E1 E2 ets acts R ns T1 T2 T,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    WfCedarType ns T →
    SubType T1 T → SubType T2 T →
    HasType a V (E1, x1) (CedarType.setType T1) →
    HasType a V (E2, x2) (CedarType.setType T2) →
    HasType a V ((CedarExpr.binaryApp BinaryOp.containsAny E1 E2), PathSet.somepaths []) (CedarType.boolType BoolType.anyBool)
| THasAttrRecOpt : ∀ a x V e F T TE ns ets acts R,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    BindAttrType ns (TE, F, true) T →
    HasType a V (e, x) TE →
    HasType a V ((CedarExpr.hasAttr e F), (PathSet.somepaths [CedarExpr.getAttr e F])) (CedarType.boolType BoolType.anyBool)
| THasAttrRecReq : ∀ a x V e F T TE ns ets acts R,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    BindAttrType ns (TE, F, false) T →
    HasType a V (e, x) TE →
    HasType a V ((CedarExpr.hasAttr e F), (PathSet.somepaths [CedarExpr.getAttr e F])) (CedarType.boolType BoolType.tt)
| TGetAttrRecOpt : ∀ a x V e F T TE ns ets acts R,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    BindAttrType ns (TE, F, true) T →
    HasType a V (e, x) TE →
    validPathExpr (CedarExpr.getAttr e F) a = true →
    HasType a V ((CedarExpr.getAttr e F), PathSet.somepaths []) T
| TGetAttrRecReq : ∀ a x V e F T TE ns ets acts R,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    DefinedEntities ets ns →
    BindAttrType ns (TE, F, false) T →
    HasType a V (e, x) TE →
    HasType a V ((CedarExpr.getAttr e F), PathSet.somepaths []) T
| THasAttrEntityOpt : ∀ a x V ets acts R e n fn T,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    GetEntityAttr ets (n, fn, true) T →
    HasType a V (e, x) (CedarType.entityType n) →
    HasType a V ((CedarExpr.hasAttr e fn), PathSet.somepaths [CedarExpr.getAttr e fn]) (CedarType.boolType BoolType.anyBool)
| THasAttrEntityReq : ∀ a x V ets acts R e n fn T,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    GetEntityAttr ets (n, fn, false) T →
    HasType a V (e, x) (CedarType.entityType n) →
    HasType a V ((CedarExpr.hasAttr e fn), PathSet.somepaths [CedarExpr.getAttr e fn]) (CedarType.boolType BoolType.tt)
| TGetAttrEntityOpt : ∀ a x V ets acts R e n fn T,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    GetEntityAttr ets (n, fn, true) T →
    HasType a V (e, x) (CedarType.entityType n) →
    validPathExpr (CedarExpr.getAttr e fn) a = true →
    HasType a V ((CedarExpr.getAttr e fn), PathSet.somepaths []) T
| TGetAttrEntityReq : ∀ a x V ets acts R e n fn T,
    V = (Environment.MkEnvironment (Schema.MkSchema ets acts) R) →
    GetEntityAttr ets (n, fn, false) T →
    HasType a V (e, x) (CedarType.entityType n) →
    HasType a V ((CedarExpr.getAttr e fn), PathSet.somepaths []) T


------------------------------
-- Pretty printing for types
-------------------------------
def stringOfBooltype (b : BoolType) : String :=
    match b with
    | BoolType.anyBool => "Bool"
    | BoolType.tt => "True"
    | BoolType.ff => "False"

instance : ToString BoolType where
  toString := stringOfBooltype

instance : Repr BoolType where
  reprPrec boolTy _ := toString boolTy

def stringOfCedartype (t : CedarType) : String :=
  match t with
    | CedarType.boolType b => stringOfBooltype b
    | CedarType.intType => "Int"
    | CedarType.stringType => "String"
    | CedarType.entityType n => toString n
    | CedarType.setType t => "Set<" ++ stringOfCedartype t ++ ">"
    | CedarType.recordTypeNil => "{}"
    | CedarType.recordTypeCons s o t' CedarType.recordTypeNil =>
        "{" ++ s ++ ":" ++ (if o then "?" else " ") ++ stringOfCedartype t' ++ "}"
    | CedarType.recordTypeCons s o t' tr =>
        "{" ++ s ++ ":" ++ (if o then "?" else " ") ++ stringOfCedartype t' ++ ", " ++ stringOfRecordtype tr ++ "}"
where
  stringOfRecordtype (t : CedarType) : String :=
    match t with
    | CedarType.recordTypeNil => ""
    | CedarType.recordTypeCons s o t' tr =>
        s ++ ":" ++ (if o then "?" else " ") ++ stringOfCedartype t' ++ ", " ++ stringOfRecordtype tr
    | _ => ""

instance : ToString CedarType where
  toString := stringOfCedartype

instance : Repr CedarType where
  reprPrec ty _ := toString ty

def stringOfAttrs (attrs : List (String × Bool × CedarType)) : String :=
  match attrs with
  | [] => ""
  | [(s, o, t')] => s ++ ":" ++ (if o then " " else "? ") ++ stringOfCedartype t'
  | (s, o, t')::attrs' => s ++ ":" ++ (if o then " " else "? ") ++ stringOfCedartype t' ++ ", " ++ stringOfAttrs attrs'

def stringOfEse (ancs : List EntityName) (attrs : List (String × Bool × CedarType)) : String :=
  (match ancs with
  | [] => " "
  | _ => " in " ++ toString ancs) ++
  (match attrs with
  | [] => ""
  | _ => " { " ++ stringOfAttrs attrs ++ " }")

instance : ToString EntitySchemaEntry where
  toString := fun ese =>
      match ese with
      | EntitySchemaEntry.MkEntitySchemaEntry ancs attrs => stringOfEse ancs attrs

instance : Repr EntitySchemaEntry where
  reprPrec ese _ := toString ese

def stringOfAse (prin : List EntityName) (res : List EntityName) (ct : List (String × Bool × CedarType)) : String :=
    "{ principal: " ++ toString prin ++
    "; resource: " ++ toString res ++
    (match ct with | [] => "" | _ => "; context: {" ++ stringOfAttrs ct ++ " }") ++ " }"

instance : ToString ActionSchemaEntry where
  toString := fun ase =>
        match ase with
        | ActionSchemaEntry.MkActionSchemaEntry ps rs ct => stringOfAse ps rs ct

instance : Repr ActionSchemaEntry where
  reprPrec ase _ := toString ase

def stringOfSchemaEts (eses : List (EntityName × EntitySchemaEntry)) : String :=
    match eses with
    | [] => ""
    | (n, ese)::eses' => "entity " ++ toString n ++ toString ese ++ "; " ++ stringOfSchemaEts eses'

def stringOfSchemaActs (acts : List (EntityUID × ActionSchemaEntry)) : String :=
    match acts with
    | [] => ""
    | (uid, act)::acts' => "action " ++ toString uid ++ " appliesTo " ++ toString act ++ "; " ++ stringOfSchemaActs acts'

def stringOfSchema (s : Schema) : String :=
    match s with
    | Schema.MkSchema ets acts => stringOfSchemaEts ets ++ stringOfSchemaActs acts

instance : ToString Schema where
  toString := stringOfSchema

instance : Repr Schema where
  reprPrec s _ := toString s

instance : ToString PathSet where
  toString := fun ps => match ps with
    | PathSet.allpaths => "allpaths"
    | PathSet.somepaths paths => "somepaths " ++ toString paths

instance : Repr PathSet where
  reprPrec pathset _ := toString pathset

end Cedar
