/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Lean
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

import Plausible.Sampleable

open Lean Elab Meta Parser Term
open Elab.Deriving
open Elab.Command

/-!
# Deriving Handler for `Shrinkable`

This file defines a handler which automatically derives `Shrinkable` instances
for inductive types.

The derived shrinker for a value `C x₁ ... xₙ` produces:
1. **Subterm shrinks**: any `xᵢ` whose type equals the inductive type itself
   (these are strictly smaller subterms).
2. **Argument shrinks**: for each `xᵢ`, shrink it via its `Shrinkable` instance
   and reconstruct the constructor with the shrunk value, holding all other
   arguments fixed.

Example usage:
```lean
inductive Tree where
  | Leaf : Tree
  | Node : Nat → Tree → Tree → Tree
  deriving Shrinkable
```

To view the derived code, enable the trace class:
```lean
set_option trace.plausible.deriving.shrinkable true
```
-/

initialize registerTraceClass `plausible.deriving.shrinkable

namespace Plausible

open Shrinkable

/-! ## Helpers (adapted from Plausible.DeriveArbitrary) -/

/-- Returns `(argument_name, argument_type)` pairs for a constructor,
    skipping the inductive's type parameters. Freshens names to avoid macro scopes. -/
private def getCtorArgsNamesAndTypes (indVal : InductiveVal) (ctorName : Name) :
    MetaM (Array (Name × Expr)) := do
  let ctorInfo ← getConstInfoCtor ctorName
  forallTelescopeReducing ctorInfo.type fun args _ => do
    let mut result := #[]
    for i in [:args.size] do
      if i < indVal.numParams then continue
      let arg := args[i]!
      let argType ← arg.fvarId!.getType
      let argName ← Core.mkFreshUserName `a
      result := result.push (argName, argType)
    return result

open TSyntax.Compat in
/-- Builds a `Header` with only implicit + instance binders (no explicit target binder).
    Adapted from `Plausible.mkHeaderWithOnlyImplicitBinders`. -/
private def mkShrinkableHeader (indVal : InductiveVal) : TermElabM Header := do
  let argNames ← mkInductArgNames indVal
  let binders ← mkImplicitBinders argNames
  let targetType ← mkInductiveApp indVal argNames
  let binders := binders ++ (← mkInstImplicitBinders ``Plausible.Shrinkable indVal argNames)
  return { binders, argNames, targetNames := #[], targetType }

/-! ## Core shrink-expression builder -/

/-- For constructor `C x₁ ... xₙ` of inductive type `T`, builds the `List T` expression:
    - subterm shrinks: each `xᵢ : T` is yielded directly
    - argument shrinks: for each `xᵢ`, shrink it and reconstruct `C` with the shrunk value
    For recursive fields (type = T), uses `auxFn` for the recursive call instead of
    `Shrinkable.shrink`, since the instance doesn't exist yet during derivation. -/
private def mkCtorShrinkExpr (targetTypeName : Name) (ctorIdent : Ident)
    (freshIdents : Array Ident) (argTypes : Array Expr)
    (auxFn : Ident) : TermElabM Term := do
  let mut listTerms : Array Term := #[]

  -- 1) Subterm shrinks: yield recursive fields directly
  for i in [:freshIdents.size] do
    if argTypes[i]!.getAppFn.constName == targetTypeName then
      listTerms := listTerms.push (← `([$(freshIdents[i]!)]))

  -- 2) Argument shrinks: shrink each field and reconstruct
  for i in [:freshIdents.size] do
    let xi := freshIdents[i]!
    let xi' := mkIdent (← Core.mkFreshUserName `x')
    let mut reconstructArgs : Array Term := #[]
    for j in [:freshIdents.size] do
      if i == j then
        reconstructArgs := reconstructArgs.push (← `($xi'))
      else
        reconstructArgs := reconstructArgs.push (← `($(freshIdents[j]!)))
    let mapBody ← `(fun $xi' => $ctorIdent $reconstructArgs*)
    -- Use recursive call for self-referential fields, Shrinkable.shrink for others
    let shrinkCall ←
      if argTypes[i]!.getAppFn.constName == targetTypeName then
        `($auxFn $xi)
      else
        `(Shrinkable.shrink $xi)
    let shrinkExpr ← `(($shrinkCall).map $mapBody)
    listTerms := listTerms.push shrinkExpr

  match listTerms.toList with
  | [] => `(([] : List _))
  | [single] => pure single
  | first :: rest =>
    rest.foldlM (fun acc t => `($acc ++ $t)) first

/-! ## Auxiliary function and instance generation -/

/-- Creates the auxiliary shrink function definition for one inductive type. -/
private def mkAuxFunction (ctx : Deriving.Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal := ctx.typeInfos[i]!
  let header ← mkShrinkableHeader indVal

  let targetType ← mkInductiveApp indVal header.argNames
  let retType ← `(List $targetType)
  let x := mkIdent (← Core.mkFreshUserName `x)
  let auxFn := mkIdent auxFunName

  let mut matchAlts : TSyntaxArray ``Term.matchAlt := #[]

  for ctorName in indVal.ctors do
    let ctorIdent := mkIdent ctorName
    let ctorArgNamesTypes ← getCtorArgsNamesAndTypes indVal ctorName
    let argTypes := ctorArgNamesTypes.map Prod.snd
    let freshIdents := (ctorArgNamesTypes.map Prod.fst).map Lean.mkIdent

    let body ← mkCtorShrinkExpr indVal.name ctorIdent freshIdents argTypes auxFn

    if freshIdents.isEmpty then
      matchAlts := matchAlts.push (← `(Term.matchAltExpr| | $ctorIdent => $body))
    else
      matchAlts := matchAlts.push (← `(Term.matchAltExpr| | $ctorIdent $freshIdents* => $body))

  let matchExpr ← `(match $x:ident with $matchAlts:matchAlt*)
  let mut body ← `(fun ($x : $targetType) => $matchExpr)

  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx ``Plausible.Shrinkable header.argNames
    body ← mkLet letDecls body

  let binders := header.binders
  let fullType ← `($targetType → $retType)
  if ctx.usePartial then
    `(partial def $auxFn:ident $binders:bracketedBinder* : $fullType := $body)
  else
    `(def $auxFn:ident $binders:bracketedBinder* : $fullType := $body)

/-- Creates a `mutual ... end` block containing the shrink function definitions -/
private def mkMutualBlock (ctx : Deriving.Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual $auxDefs:command* end)

open TSyntax.Compat in
/-- Creates instance commands for the `Shrinkable` typeclass -/
private def mkShrinkableInstanceCmds (ctx : Deriving.Context) (typeNames : Array Name) :
    TermElabM (Array Command) := do
  let mut instances := #[]
  for i in [:ctx.typeInfos.size] do
    let indVal := ctx.typeInfos[i]!
    if typeNames.contains indVal.name then
      let auxFunName := ctx.auxFunNames[i]!
      let argNames ← mkInductArgNames indVal
      let binders ← mkImplicitBinders argNames
      let binders := binders ++ (← mkInstImplicitBinders ``Plausible.Shrinkable indVal argNames)
      let indType ← mkInductiveApp indVal argNames
      let type ← `(Shrinkable $indType)
      let instCmd ← `(instance $binders:implicitBinder* : $type := ⟨$(mkIdent auxFunName)⟩)
      instances := instances.push instCmd
  return instances

/-- Derives a `Shrinkable` instance for a single inductive type -/
private def mkShrinkableInstanceCmd (declName : Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext ``Plausible.Shrinkable "shrink" declName
  let cmds := #[← mkMutualBlock ctx] ++ (← mkShrinkableInstanceCmds ctx #[declName])
  trace[plausible.deriving.shrinkable] "\n{cmds}"
  return cmds

/-- Deriving handler for `Shrinkable` -/
def mkShrinkableInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      let cmds ← liftTermElabM $ mkShrinkableInstanceCmd declName
      cmds.forM elabCommand
    return true
  else
    throwError "Cannot derive instance of Shrinkable typeclass for non-inductive types"
    return false

initialize
  registerDerivingHandler ``Shrinkable mkShrinkableInstanceHandler

end Plausible
