/-
Copyright (c) 2025 Ernest Ng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ernest Ng
-/
import Lean.Elab
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

import Plausible.Arbitrary

open Lean Elab Meta Parser Term
open Elab.Deriving
open Elab.Command

/-!

# Deriving Handler for `Arbitrary`

This file defines a handler which automatically derives `Arbitrary` instances
for inductive types.

(Note that the deriving handler technically derives `ArbitraryFueled` instancces,
but every `ArbitraryFueled` instance automatically results in an `Arbitrary` instance,
as detailed in `Arbitrary.lean`.)

Note that the resulting `Arbitrary` and `ArbitraryFueled` instance should be considered
to be opaque, following the convention for the deriving handler for Mathlib's `Encodable` typeclass.

Example usage:

```lean
-- Datatype for binary trees
inductive Tree
  | Leaf : Tree
  | Node : Nat → Tree → Tree → Tree
  deriving Arbitrary
```

To sample from a derived generator, users can simply call `Arbitrary.runArbitrary`, specify the type
for the desired generated values and provide some Nat to act as the generator's fuel parameter (10 in the example below):

```lean
#eval Arbitrary.runArbitrary (α := Tree) 10
```

To view the code for the derived generator, users can enable trace messages using the `plausible.deriving.arbitrary` trace class as follows:

```lean
set_option trace.plausible.deriving.arbitrary true
```

## Main definitions
* Deriving handler for `ArbitraryFueled` typeclass

-/

namespace Plausible

open Arbitrary

/-- Takes the name of a constructor for an algebraic data type and returns an array
    containing `(argument_name, argument_type)` pairs.

    If the algebraic data type is defined using anonymous constructor argument syntax, i.e.
    ```
    inductive T where
      C1 : τ1 → … → τn
      …
    ```
    Lean produces macro scopes when we try to access the names for the constructor args.
    In this case, we remove the macro scopes so that the name is user-accessible.
    (This will result in constructor argument names being non-unique in the array
    that is returned -- it is the caller's responsibility to produce fresh names.)
-/
def getCtorArgsNamesAndTypes (header : Header) (indVal : InductiveVal) (ctorName : Name) : MetaM (Array (Name × Expr)) := do
  let ctorInfo ← getConstInfoCtor ctorName

  forallTelescopeReducing ctorInfo.type fun args _ => do
    let mut argNamesAndTypes := #[]

    for i in *...args.size do
      let arg := args[i]!
      let localDecl ← arg.fvarId!.getDecl
      let argType := localDecl.type

      let argName ← if i < indVal.numParams then pure header.argNames[i]! else Core.mkFreshUserName `a
      if i < indVal.numParams then
        continue
      else
        argNamesAndTypes := argNamesAndTypes.push (argName, argType)

    return argNamesAndTypes

-- Note: the following functions closely follow the implementation of the deriving handler for `Repr` / `BEq`
-- (see https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Deriving/Repr.lean).

open TSyntax.Compat in
/-- Variant of `Deriving.Util.mkHeader` where we don't add an explicit binder
    of the form `($targetName : $targetType)` to the field `binders`
    (i.e. `binders` contains only implicit binders) -/
def mkHeaderWithOnlyImplicitBinders (className : Name) (arity : Nat) (indVal : InductiveVal) : TermElabM Header := do
  let argNames ← mkInductArgNames indVal
  let binders ← mkImplicitBinders argNames
  let targetType ← mkInductiveApp indVal argNames
  let mut targetNames := #[]
  for _ in [:arity] do
    targetNames := targetNames.push (← mkFreshUserName `x)
  let binders := binders ++ (← mkInstImplicitBinders className indVal argNames)
  return {
    binders := binders
    argNames := argNames
    targetNames := targetNames
    targetType := targetType
  }

open TSyntax.Compat in
/-- Variant of `Deriving.Util.mkInstanceCmds` which is specialized to creating `ArbitraryFueled` instances
    that have `Arbitrary` inst-implicit binders.

    Note that we can't use `mkInstanceCmds` out of the box,
    since it expects the inst-implicit binders and the instance we're creating to both belong to the same typeclass. -/
def mkArbitraryFueledInstanceCmds (ctx : Deriving.Context) (typeNames : Array Name) (useAnonCtor := true) : TermElabM (Array Command) := do
  let mut instances := #[]
  for i in [:ctx.typeInfos.size] do
    let indVal       := ctx.typeInfos[i]!
    if typeNames.contains indVal.name then
      let auxFunName   := ctx.auxFunNames[i]!
      let argNames     ← mkInductArgNames indVal
      let binders      ← mkImplicitBinders argNames
      let binders      := binders ++ (← mkInstImplicitBinders ``Arbitrary indVal argNames)  -- this line is changed from
      let indType      ← mkInductiveApp indVal argNames
      let type         ← `($(mkCIdent ``ArbitraryFueled) $indType)
      let mut val      := mkIdent auxFunName
      if useAnonCtor then
        val ← `(⟨$val⟩)
      let instCmd ← `(instance $binders:implicitBinder* : $type := $val)
      instances := instances.push instCmd
  return instances

/-- Creates a `Header` for the `Arbitrary` typeclass -/
def mkArbitraryHeader (indVal : InductiveVal) : TermElabM Header :=
  mkHeaderWithOnlyImplicitBinders ``Arbitrary 1 indVal

/-- Creates the *body* of the generator that appears in the instance of the `ArbitraryFueled` typeclass -/
def mkBody (header : Header) (inductiveVal : InductiveVal) (generatorType : TSyntax `term) : TermElabM Term := do
  -- Fetch the name of the target type (the type for which we are deriving a generator)
  let targetTypeName := inductiveVal.name

  -- Produce `Ident`s for the `fuel` argument for the lambda
  -- at the end of the generator function, as well as the `aux_arb` inner helper function
  let freshFuel := Lean.mkIdent (← Core.mkFreshUserName `fuel)
  let freshFuel' := Lean.mkIdent (← Core.mkFreshUserName `fuel')
  let auxArb := mkIdent `aux_arb

  -- Maintain two arrays which will be populated with pairs
  -- where the first component is a sub-generator (non-recursive / recursive)
  -- and the 2nd component is the generator's associated weight
  let mut weightedNonRecursiveGenerators := #[]
  let mut weightedRecursiveGenerators := #[]

  -- We also need to keep track of non-recursive generators without their weights,
  -- since some of Plausible's `Gen` combinators operate on generator functions
  let mut nonRecursiveGeneratorsNoWeights := #[]

  for ctorName in inductiveVal.ctors do
    let ctorIdent := mkIdent ctorName

    let ctorArgNamesTypes ← getCtorArgsNamesAndTypes header inductiveVal ctorName
    let (ctorArgNames, ctorArgTypes) := Array.unzip ctorArgNamesTypes

    /- Produce fresh names for each of the constructor's arguments.
      Producing fresh names is necessary in order to handle
      constructors expressed using the following syntax:
      ```
      inductive Foo
        | C : T1 → ... → Tn
      ```
      in which all the arguments to the constructor `C` don't have explicit names.
    -/
    let ctorArgIdents := Lean.mkIdent <$> ctorArgNames
    let ctorArgIdentsTypes := Array.zip ctorArgIdents ctorArgTypes

    if ctorArgNamesTypes.isEmpty then
      -- Constructor is nullary, we can just use an generator of the form `pure ...` with weight 1,
      -- following the QuickChick convention.
      -- (For clarity, this generator is parenthesized in the code produced.)
      let pureGen ← `(($(Lean.mkIdent `pure) $ctorIdent))
      weightedNonRecursiveGenerators := weightedNonRecursiveGenerators.push (← `((1, $pureGen)))
      nonRecursiveGeneratorsNoWeights := nonRecursiveGeneratorsNoWeights.push pureGen
    else
      -- Add all the constructor's argument names + types to the local context,
      -- then produce the body of the sub-generator (& a flag indicating if the constructor is recursive)
      let (generatorBody, ctorIsRecursive) ←
        withLocalDeclsDND ctorArgNamesTypes (fun _ => do
          let mut doElems := #[]

          -- Flag to indicate whether the constructor is recursive (initialized to `false`)
          let mut ctorIsRecursive := false

          -- Examine each argument to see which of them require recursive calls to the generator
          for (freshIdent, argType) in ctorArgIdentsTypes do
            -- If the argument's type is the same as the target type,
            -- produce a recursive call to the generator using `aux_arb`,
            -- otherwise generate a value using `arbitrary`
            let bindExpr ←
              if argType.getAppFn.constName == targetTypeName then
                -- We've detected that the constructor has a recursive argument, so we update the flag
                ctorIsRecursive := true
                `(doElem| let $freshIdent ← $(mkIdent `aux_arb):term $(freshFuel'):term)
              else
                `(doElem| let $freshIdent ← $(mkIdent ``Arbitrary.arbitrary):term)
            doElems := doElems.push bindExpr

          -- Create an expression `return C x1 ... xn` at the end of the generator, where
          -- `C` is the constructor name and the `xi` are the generated values for the args
          let pureExpr ← `(doElem| return $ctorIdent $ctorArgIdents*)
          doElems := doElems.push pureExpr

          -- Put the body of the generator together in an explicitly-parenthesized `do`-block
          let generatorBody ← `((do $[$doElems:doElem]*))
          pure (generatorBody, ctorIsRecursive))

      if !ctorIsRecursive then
        -- Non-recursive generators have weight 1, following the QuickChick convention
        weightedNonRecursiveGenerators := weightedNonRecursiveGenerators.push (← `((1, $generatorBody)))
        nonRecursiveGeneratorsNoWeights := nonRecursiveGeneratorsNoWeights.push generatorBody
      else
        -- Recursive generaotrs have an associated weight of `fuel' + 1`, following the QuickChick convention
        weightedRecursiveGenerators := weightedRecursiveGenerators.push (← ``(($freshFuel' + 1, $generatorBody)))

  -- Use the first non-recursive generator (without its weight) as the default generator
  -- If the target type has no non-recursive constructors, we emit an error message
  -- saying that we cannot derive a generator for that type
  let defaultGenerator ← Option.getDM (nonRecursiveGeneratorsNoWeights[0]?)
    (throwError m!"derive Arbitrary failed, {targetTypeName} has no non-recursive constructors")

  -- Create the cases for the pattern-match on the fuel argument
  -- If `fuel = 0`, pick one of the non-recursive generators
  let mut caseExprs := #[]
  let zeroCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $(mkIdent ``Gen.oneOfWithDefault) $defaultGenerator [$nonRecursiveGeneratorsNoWeights,*])
  caseExprs := caseExprs.push zeroCase

  -- If `fuel = fuel' + 1`, pick a generator (it can be non-recursive or recursive)
  let mut allWeightedGenerators ← `([$weightedNonRecursiveGenerators,*, $weightedRecursiveGenerators,*])
  let succCase ← `(Term.matchAltExpr| | $freshFuel' + 1 => $(mkIdent ``Gen.frequency) $defaultGenerator $allWeightedGenerators)
  caseExprs := caseExprs.push succCase

  -- Create function argument for the generator fuel
  let fuelParam ← `(Term.letIdBinder| ($freshFuel : $(mkIdent `Nat)))
  let matchExpr ← `(match $freshFuel:ident with $caseExprs:matchAlt*)

  -- Create an instance of the `ArbitraryFueled` typeclass
  `(let rec $auxArb:ident $fuelParam : $generatorType :=
      $matchExpr
    fun $freshFuel => $auxArb $freshFuel)


/-- Creates the function definition for the derived generator -/
def mkAuxFunction (ctx : Deriving.Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal := ctx.typeInfos[i]!
  let header ← mkArbitraryHeader indVal
  let mut binders := header.binders

  -- Determine the type of the generator
  -- (the `Plausible.Gen` type constructor applied to the name of the `inductive` type, plus any type parameters)
  let targetType ← mkInductiveApp ctx.typeInfos[i]! header.argNames
  let generatorType ← `($(mkIdent ``Plausible.Gen) $targetType)

  -- Create the body of the generator function
  let mut body ← mkBody header indVal generatorType

  -- For mutually-recursive types, we need to create
  -- local `let`-definitions containing the relevant `ArbitraryFueled` instances so that
  -- the derived generator typechecks
  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx ``ArbitraryFueled header.argNames
    body ← mkLet letDecls body

  -- If we are deriving a generator for a bunch of mutually-recursive types,
  -- the derived generator needs to be marked `partial` (following the implementation
  -- of the `deriving Repr` handler)
  if ctx.usePartial then
    `(partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : $(mkIdent ``Nat) → $generatorType := $body:term)
  else
    `(def $(mkIdent auxFunName):ident $binders:bracketedBinder* : $(mkIdent ``Nat) → $generatorType := $body:term)

/-- Creates a `mutual ... end` block containing the definitions of the derived generators -/
def mkMutualBlock (ctx : Deriving.Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in *...ctx.typeInfos.size do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual
     $auxDefs:command*
    end)

/-- Creates an instance of the `ArbitraryFueled` typeclass -/
private def mkArbitraryFueledInstanceCmd (declName : Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext "arbitrary" declName
  let cmds := #[← mkMutualBlock ctx] ++ (← mkArbitraryFueledInstanceCmds ctx #[declName])
  trace[plausible.deriving.arbitrary] "\n{cmds}"
  return cmds

/-- Deriving handler which produces an instance of the `ArbitraryFueled` typeclass for
    each type specified in `declNames` -/
def mkArbitraryInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      let cmds ← liftTermElabM $ mkArbitraryFueledInstanceCmd declName
      cmds.forM elabCommand
    return true
  else
    throwError "Cannot derive instance of Arbitrary typeclass for non-inductive types"
    return false

initialize
  registerDerivingHandler ``Arbitrary mkArbitraryInstanceHandler

end Plausible
