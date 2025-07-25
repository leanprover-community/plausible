import Lean
import Plausible.Idents
import Plausible.TSyntaxCombinators
import Plausible.Arbitrary
import Plausible.Utils

open Lean Elab Command Meta Term Parser
open Idents


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
  let freshSizeIdent := mkIdent $ localCtx.getUnusedName `size
  let freshSize' := mkIdent $ localCtx.getUnusedName `size'

  let mut nonRecursiveGenerators := #[]
  let mut recursiveGenerators := #[]
  for ctorName in inductiveVal.ctors do
    let ctorIdent := mkIdent ctorName

    let ctorArgNamesTypes ← liftTermElabM $ getCtorArgsNamesAndTypes ctorName
    let (ctorArgNames, ctorArgTypes) := Array.unzip ctorArgNamesTypes

    /- Produce fresh names for each of the constructor's arguments.
      Producing fresh names is necessary in order to handle
      constructors expressed using the following syntax:
      ```
      inductive Foo
        | C : T1 → ... → Tn
      ```
      in which all the arguments to the constructor `C` don't have explicit names.

      (Note: we use `genFreshNames` instead of `LocalContext.getUnusedName` here
      to ensure that when there are multiple arguments,
      every single argument gets a fresh name. All of the fresh names are added
      to the `LocalContext` later in this function, ensuring that the `LocalContext`
      remains updated.)
    -/
    let freshArgNames := genFreshNames (existingNames := ctorArgNames) (namePrefixes := ctorArgNames)
    let freshArgNamesTypes := Array.zip freshArgNames ctorArgTypes
    let freshArgIdents := Lean.mkIdent <$> freshArgNames
    let freshArgIdentsTypes := Array.zip freshArgIdents ctorArgTypes

    if ctorArgNamesTypes.isEmpty then
      -- Constructor is nullary, we can just use a generator of the form `pure ...`
      let pureGen ← `($pureFn $ctorIdent)
      nonRecursiveGenerators := nonRecursiveGenerators.push pureGen
    else
      -- Add all the freshened names for the constructor to the local context,
      -- then produce the body of the sub-generator
      let (generatorBody, ctorIsRecursive) ← liftTermElabM $
        withLocalDeclsDND freshArgNamesTypes (fun _ => do
          let mut doElems := #[]

          -- Determine whether the constructor has any recursive arguments
          let ctorIsRecursive ← isConstructorRecursive targetTypeName ctorName
          if !ctorIsRecursive then
            -- Call `arbitrary` to generate a random value for each of the arguments
            for freshIdent in freshArgIdents do
              let bindExpr ← mkLetBind freshIdent #[arbitraryFn]
              doElems := doElems.push bindExpr
          else
            -- For recursive constructors, we need to examine each argument to see which of them require
            -- recursive calls to the generator
            for (freshIdent, argType) in freshArgIdentsTypes do
              -- If the argument's type is the same as the target type,
              -- produce a recursive call to the generator using `aux_arb`,
              -- otherwise generate a value using `arbitrary`
              let bindExpr ←
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
          let generatorBody ← mkDoBlock doElems
          pure (generatorBody, ctorIsRecursive))

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
        let rec $auxArbFn:ident $sizeParam : $generatorType :=
          $matchExpr
      fun $freshSizeIdent => $auxArbFn $freshSizeIdent)

syntax (name := derive_arbitrary) "#derive_arbitrary" term : command

/-- Command elaborator which derives an instance of the `ArbitrarySized` typeclass -/
@[command_elab derive_arbitrary]
def elabDeriveArbitrary : CommandElab := fun stx => do
  match stx with
  | `(#derive_arbitrary $targetTypeTerm:term) => do

    let targetTypeIdent ←
      match targetTypeTerm with
      | `($tyIdent:ident) => pure tyIdent
      | _ => throwErrorAt targetTypeTerm "Deriving Arbitrary not supported for parameterized types"
    let targetTypeName := targetTypeIdent.getId

    let isInductiveType ← isInductive targetTypeName
    if isInductiveType then
      let typeClassInstance ← mkArbitrarySizedInstance targetTypeName

      -- Pretty-print the derived generator
      let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeClassInstance)

      logInfo m!"Try this generator: {genFormat}"

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
