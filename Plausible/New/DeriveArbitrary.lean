import Lean
import Plausible.IR.Prelude
import Plausible.New.Idents
import Plausible.New.TSyntaxCombinators
import Plausible.New.Arbitrary
import Plausible.New.Utils

open Lean Elab Command Meta Term Parser
open Plausible.IR Idents


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
    that is returned -- it is the caller's responsibility to produce fresh names,
    e.g. using `Idents.genFreshNames`.)
-/
def getCtorArgsNamesAndTypes (ctorName : Name) : MetaM (Array (Name × Expr)) := do
  let ctorInfo ← getConstInfoCtor ctorName

  forallTelescopeReducing ctorInfo.type fun args _ => do
    let mut argNamesAndTypes := #[]
    for arg in args.toList do
      let localDecl ← arg.fvarId!.getDecl
      let mut argName := localDecl.userName
      -- Check if the name has macro scopes
      -- If so, remove them so that we can produce a user-accessible name
      -- (where macro scopes don't appear in the name)
      if argName.hasMacroScopes then
        argName := Name.eraseMacroScopes argName
      argNamesAndTypes := Array.push argNamesAndTypes (argName, localDecl.type)

    return argNamesAndTypes

/-- Produces an instance of the `ArbitrarySized` typeclass for an inductive type
    whose name is given by `targetTypeName`.

    (Note: the main logic for determining the structure of the derived generator
    is contained in this function.) -/
def mkArbitrarySizedInstance (targetTypeName : Name) : CommandElabM (TSyntax `command) := do
  -- Obtain Lean's `InductiveVal` data structure, which contains metadata about
  -- the type corresponding to `targetTypeName`
  let inductiveVal ← getConstInfoInduct targetTypeName

  -- Fetch the ambient local context, which we need to produce user-accessible fresh names
  let localCtx ← liftTermElabM $ getLCtx

  -- Produce a fresh name for the `size` argument for the lambda
  -- at the end of the generator function, as well as the `aux_arb` inner helper function
  let freshSizeIdent := mkFreshAccessibleIdent localCtx `size
  let freshSize' := mkFreshAccessibleIdent localCtx `size'
  let auxArbIdent := mkFreshAccessibleIdent localCtx `aux_arb

  let mut nonRecursiveGenerators := #[]
  let mut recursiveGenerators := #[]
  for ctorName in inductiveVal.ctors do
    let ctorIdent := mkIdent ctorName

    let ctorArgNamesTypes ← liftTermElabM $ getCtorArgsNamesAndTypes ctorName

    if ctorArgNamesTypes.isEmpty then
      -- Constructor is nullary, we can just use a generator of the form `pure ...`
      let pureGen ← `($pureFn $ctorIdent)
      nonRecursiveGenerators := nonRecursiveGenerators.push pureGen
    else
      -- Produce a fresh name for each of the args to the constructor
      let ctorArgNames := Prod.fst <$> ctorArgNamesTypes
      let freshArgIdents := Lean.mkIdent <$> genFreshNames (existingNames := ctorArgNames) (namePrefixes := ctorArgNames)

      let mut doElems := #[]

      -- Determine whether the constructor has any recursive arguments
      let ctorIsRecursive ← liftTermElabM $ isConstructorRecursive targetTypeName ctorName
      if !ctorIsRecursive then
        -- Call `arbitrary` to generate a random value for each of the arguments
        for freshIdent in freshArgIdents do
          let bindExpr ← liftTermElabM $ mkLetBind freshIdent #[arbitraryFn]
          doElems := doElems.push bindExpr
      else
        -- For recursive constructors, we need to examine each argument to see which of them require
        -- recursive calls to the generator
        let freshArgIdentsTypes := Array.zip freshArgIdents (Prod.snd <$> ctorArgNamesTypes)
        for (freshIdent, argType) in freshArgIdentsTypes do
          -- If the argument's type is the same as the target type,
          -- produce a recursive call to the generator using `aux_arb`,
          -- otherwise generate a value using `arbitrary`
          let bindExpr ←
            liftTermElabM $
              if argType.getAppFn.constName == targetTypeName then
                mkLetBind freshIdent #[auxArbFn, freshSize']
              else
                mkLetBind freshIdent #[arbitraryFn]
          doElems := doElems.push bindExpr

      -- Create an expression `return C x1 ... xn` at the end of the generator, where
      -- `C` is the constructor name and the `xi` are the generated values for the args
      let pureExpr ← `(doElem| return $ctorIdent $freshArgIdents*)
      doElems := doElems.push pureExpr

      -- Put the body of the generator together
      let generatorBody ← liftTermElabM $ mkDoBlock doElems
      if !ctorIsRecursive then
        nonRecursiveGenerators := nonRecursiveGenerators.push generatorBody
      else
        recursiveGenerators := recursiveGenerators.push generatorBody

  -- Just use the first non-recursive generator as the default generator
  let defaultGenerator := nonRecursiveGenerators[0]!

  -- Turn each generator into a thunked function and associate each generator with its weight
  -- (1 for non-recursive generators, `.succ size'` for recursive generators)
  let thunkedNonRecursiveGenerators ←
    Array.mapM (fun generatorBody => `($generatorCombinatorsThunkGenFn (fun _ => $generatorBody))) nonRecursiveGenerators

  let mut weightedThunkedNonRecursiveGens := #[]
  for thunkedGen in thunkedNonRecursiveGenerators do
    let thunkedGen ← `((1, $thunkedGen))
    weightedThunkedNonRecursiveGens := weightedThunkedNonRecursiveGens.push thunkedGen

  let mut weightedThunkedRecursiveGens := #[]
  for recursiveGen in recursiveGenerators do
    let thunkedWeightedGen ← `(($succIdent $freshSize', $generatorCombinatorsThunkGenFn (fun _ => $recursiveGen)))
    weightedThunkedRecursiveGens := weightedThunkedRecursiveGens.push thunkedWeightedGen

  -- Create the cases for the pattern-match on the size argument
  -- If `size = 0`, pick one of the thunked non-recursive generators
  let mut caseExprs := #[]
  let zeroCase ← `(Term.matchAltExpr| | $zeroIdent => $oneOfWithDefaultGenCombinatorFn $defaultGenerator [$thunkedNonRecursiveGenerators,*])
  caseExprs := caseExprs.push zeroCase

  -- If `size = .succ size'`, pick a generator (it can be non-recursive or recursive)
  let mut allThunkedWeightedGenerators ← `([$weightedThunkedNonRecursiveGens,*, $weightedThunkedRecursiveGens,*])
  let succCase ← `(Term.matchAltExpr| | $succIdent $freshSize' => $frequencyFn $defaultGenerator $allThunkedWeightedGenerators)
  caseExprs := caseExprs.push succCase

  -- Create function argument for the generator size
  let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))
  let matchExpr ← liftTermElabM $ mkMatchExpr sizeIdent caseExprs

  -- Create an instance of the `ArbitrarySized` typeclass
  let targetTypeIdent := mkIdent targetTypeName
  let generatorType ← `($genTypeConstructor $targetTypeIdent)
  `(instance : $arbitrarySizedTypeclass $targetTypeIdent where
      $unqualifiedArbitrarySizedFn:ident :=
        let rec $auxArbIdent:ident $sizeParam : $generatorType :=
          $matchExpr
      fun $freshSizeIdent => $auxArbIdent $freshSizeIdent)

syntax (name := derive_arbitrary) "#derive_arbitrary" term : command

/-- Command elaborator which derives an instance of the `ArbitrarySized` typeclass -/
@[command_elab derive_arbitrary]
def elabDeriveArbitrary : CommandElab := fun stx => do
  match stx with
  | `(#derive_arbitrary $targetTypeTerm:term) => do

    -- TODO: figure out how to support parameterized types
    let targetTypeIdent ←
      match targetTypeTerm with
      | `($tyIdent:ident) => pure tyIdent
      | _ => throwErrorAt targetTypeTerm "Parameterized types not supported"
    let targetTypeName := targetTypeIdent.getId

    let isInductiveType ← isInductive targetTypeName
    if isInductiveType then
      let typeClassInstance ← mkArbitrarySizedInstance targetTypeName

      -- Pretty-print the derived generator
      let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeClassInstance)

      -- Display the code for the derived typeclass instance to the user
      -- & prompt the user to accept it in the VS Code side panel
      liftTermElabM $ Tactic.TryThis.addSuggestion stx
        (Format.pretty genFormat) (header := "Try this generator: ")

      -- Elaborate the typeclass instance and add it to the local context
      elabCommand typeClassInstance
    else
      throwError "Cannot derive Arbitrary instance for non-inductive types"

  | _ => throwUnsupportedSyntax

/-- Deriving handler which produces an instance of the `ArbitrarySized` typeclass for
    each type specified in `declNames` -/
def deriveArbitraryInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for targetTypeName in declNames do
      let typeClassInstance ← mkArbitrarySizedInstance targetTypeName
      elabCommand typeClassInstance
    return true
  else
    throwError "Cannot derive instance of Arbitrary typeclass for non-inductive types"
    return false

initialize
  registerDerivingHandler ``Arbitrary deriveArbitraryInstanceHandler
