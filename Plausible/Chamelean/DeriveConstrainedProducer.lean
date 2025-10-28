import Lean.Expr
import Lean.LocalContext

import Plausible.Chamelean.UnificationMonad
import Plausible.Chamelean.Schedules
import Plausible.Chamelean.DeriveSchedules
import Plausible.Chamelean.MExp
import Plausible.Chamelean.MakeConstrainedProducerInstance
import Plausible.DeriveArbitrary
import Plausible.Chamelean.TSyntaxCombinators
import Plausible.Chamelean.Utils
import Plausible.Chamelean.Debug
import Plausible.Arbitrary

import Lean.Elab.Command
import Lean.Meta.Basic

open Lean Elab Command Meta Term Parser
open Idents Schedules


----------------------------------------------------------------------------------------------------------------------------------
-- Adapted from "Generating Good Generators for Inductive Relations" (POPL '18) & "Testing Theorems, Fully Automatically" (2025)
-- as well as the QuickChick source code
-- https://github.com/QuickChick/QuickChick/blob/internal-rewrite/plugin/newGenericLib.ml
-- https://github.com/QuickChick/QuickChick/blob/internal-rewrite/plugin/newUnifyQC.ml.cppo
----------------------------------------------------------------------------------------------------------------------------------

/-- Creates the initial constraint map where all inputs are `Fixed`, while the output & all universally-quantified variables are `Undef`.
    - `forAllVariables` is a list of (variable name, variable type) pairs -/
def mkInitialUnknownMap (inputNames: List Name) (outputName : Name) (outputType : Expr) (forAllVariables : List (Name × Expr)) : UnknownMap :=
  let inputConstraints := inputNames.zip (List.replicate inputNames.length .Fixed)
  let outputConstraints := [(outputName, .Undef outputType)]
  let filteredForAllVariables := forAllVariables.filter (fun (x, _) => x ∉ inputNames)
  let forAllVarsConstraints := (fun (x, ty) => (x, .Undef ty)) <$> filteredForAllVariables
  Std.HashMap.ofList $ inputConstraints ++ outputConstraints ++ forAllVarsConstraints

/-- Creates the initial `UnifyState` for a producer, with the `UnifyState` corresponding to a constructor of an inductive relation.
    The arguments to this function are:
    - `inputNames`: the names of all inputs to the producer
    - `outputName`, `outputType`: name & type of the output (variable to be produced)
  - `forAllVariables`: the names & types for universally-quantified variables in the constructor's type
    - `hypotheses`: the hypotheses for the constructor (represented as a constructor name applied to some list of arguments) -/
def mkProducerInitialUnifyState (inputNames : List Name) (outputName : Name) (outputType : Expr) (forAllVariables : List (Name × Expr))
  (hypotheses : List (Name × List ConstructorExpr)) : UnifyState :=
  let forAllVarNames := Prod.fst <$> forAllVariables
  let constraints := mkInitialUnknownMap inputNames outputName outputType forAllVariables
  let unknowns := Std.HashSet.ofList (outputName :: (inputNames ++ forAllVarNames))
  { constraints := constraints
    equalities := ∅
    patterns := []
    unknowns := unknowns
    outputName := outputName
    outputType := outputType
    inputNames := inputNames
    hypotheses := hypotheses }

/-- Creates the initial `UnifyState` for a checker, with the `UnifyState` corresponding to a constructor of an inductive relation.
    The arguments to this function are:
    - `inputNames`: the names of all inputs to the producer
    - `forAllVariables`: the names & types for universally-quantified variables in the constructor's type
    - `hypotheses`: the hypotheses for the constructor (represented as a constructor name applied to some list of arguments)

    Note that this function is the same as `mkProducerInitialUnifyState`, except it doesn't take in the name & type of the output variable,
    since checkers don't need to produce values (they just need to return an `Option Bool`). -/
def mkCheckerInitialUnifyState (inputNames : List Name) (forAllVariables : List (Name × Expr)) (hypotheses : List (Name × List ConstructorExpr)) : UnifyState :=
  let forAllVarNames := Prod.fst <$> forAllVariables
  let inputConstraints := inputNames.zip (List.replicate inputNames.length .Fixed)
  let filteredForAllVariables := forAllVariables.filter (fun (x, _) => x ∉ inputNames)
  let forAllVarsConstraints := (fun (x, ty) => (x, .Undef ty)) <$> filteredForAllVariables
  let constraints := Std.HashMap.ofList $ inputConstraints ++ forAllVarsConstraints
  let unknowns := Std.HashSet.ofList (inputNames ++ forAllVarNames)
  { emptyUnifyState with
    constraints := constraints
    unknowns := unknowns
    inputNames := inputNames
    hypotheses := hypotheses }

/-- Converts a expression `e` to a *constructor expression* `C r1 … rn`,
    where `C` is a constructor and the `ri` are arguments,
    returning `some (C, #[r1, …, rn])`
    - If `e` is not an application, this function returns `none`  -/
def convertToCtorExpr (e : Expr) : MetaM (Option (Name × Array Expr)) :=
  if e.isConst then
    -- Nullary constructors are identified by name
    return some (e.constName!, #[])
  else if e.isApp then do
    -- Constructors with arguments
    let (ctorName, args) := e.getAppFnArgs
    let mut actualArgs := #[]
    for arg in args do
      -- Figure out whether `argType` is `Type u` for some universe `u`
      let argType ← inferType arg
      -- If `argType` is `Type u` or `Sort u`, then we know `arg` itself must be a type
      -- (i.e. it is part of an explicit type application), so we can omit it from `actualArgs`
      if argType.isSort then
        continue
      else if argType.isApp then
        -- Handle case where `argType` is a typeclass instance
        -- (e.g. `LT Nat` is supplied as an argument to `<`)
        -- Typeclass instance arguments which are explicit type applications
        -- can be omitted from `actualArgs`
        let (typeCtorName, _) := argType.getAppFnArgs
        let env ← getEnv
        if Lean.isClass env typeCtorName then
          continue
        else
          actualArgs := actualArgs.push arg
      else
        actualArgs := actualArgs.push arg
    return some (ctorName, actualArgs)
  else
    return none


/-- Takes an unknown `u`, and finds the `Range` `r` that corresponds to
    `u` in the `constraints` map.

    However, there are 3 conditions in which we generate a fresh unknown `u'`
    and update the `constraints` map with the binding `u' ↦ Unknown u`:

    1. `u` isn't present in the `constraints` map (i.e. no such `r` exists)
    2. `r = .Fixed`
    3. `r = .Undef τ` for some type τ
    (We need to hand latter two conditions are )

    We need to handle conditions (2) and (3) because the top-level ranges
    passed to `UnifyM.unify` cannot be `Fixed` or `Undef`, as stipulated
    in the QuickChick codebase / the Generating Good Generators paper. -/
def processCorrespondingRange (u : Unknown) : UnifyM Range :=
  UnifyM.withConstraints $ fun k =>
    match k[u]? with
    | some .Fixed | some (.Undef _) | none => do
      let u' ← UnifyM.registerFreshUnknown
      UnifyM.update u' (.Unknown u)
      return .Unknown u'
    | some r => return r

/-- Converts an `Expr` to a `Range`, using the `LocalContext` to find the user-facing names
    corresponding to `FVarId`s -/
partial def convertExprToRangeInCurrentContext (e : Expr) : UnifyM Range := do
  match (← convertToCtorExpr e) with
  | some (f, args) => do
    let argRanges ← args.toList.mapM convertExprToRangeInCurrentContext
    return (Range.Ctor f argRanges)
  | none =>
    if e.isFVar then do
      let localCtx ← getLCtx
      match localCtx.findFVar? e with
      | some localDecl =>
        let u := localDecl.userName
        return (.Unknown u)
      | none =>
        let namesInContext := (fun e => getUserNameInContext! localCtx e.fvarId!) <$> localCtx.getFVars
        throwError m!"{e} missing from LocalContext, which only contains {namesInContext}"
    else
      match e with
      | .const u _ => return (.Unknown u)
      | .lit literal => return .Lit literal
      | _ => throwError m!"Cannot convert expression {e} to Range"

/-- Converts a hypothesis (reprented as a `TSyntax term`) to a `Range` -/
partial def convertHypothesisTermToRange (term : TSyntax `term) : UnifyM Range := do
  match term with
  | `($ctor:ident $args:term*) => do
    let argRanges ← Array.toList <$> args.mapM convertHypothesisTermToRange
    return (.Ctor ctor.getId argRanges)
  | `($ctor:ident) =>
    -- Use `getConstInfo` to determine if the identifier is a variable name or
    -- a nullary constructor of an inductive type
    let name := ctor.getId
    let constInfo ← getConstInfo name
    if constInfo.isCtor then
      return (Range.Ctor name [])
    else
      return (.Unknown name)
  | _ => throwError m!"unable to convert {term} to a Range"

/-- Converts a `Pattern` to a `TSyntax term` -/
def convertPatternToTerm (pattern : Pattern) : MetaM (TSyntax `term) :=
  match pattern with
  | .UnknownPattern name => return (mkIdent name)
  | .CtorPattern ctorName args => do
    let ctorIdent := mkIdent ctorName
    let argSyntaxes ← args.mapM convertPatternToTerm
    argSyntaxes.foldlM (fun acc arg => `($acc $arg)) ctorIdent
  | .LitPattern l => mkLiteral l


/-- Converts a `Range` to a `ConstructorExpr`
    (helper function used by `convertRangeToCtorAppForm`) -/
partial def convertRangeToConstructorExpr (r : Range) : UnifyM ConstructorExpr :=
  match r with
  | .Unknown u => return (.Unknown u)
  | .Ctor ctorName args => do
    let updatedArgs ← args.mapM convertRangeToConstructorExpr
    return (.Ctor ctorName updatedArgs)
  | .Lit l =>
    return .Lit l
  | _ => throwError m!"Unable to convert {r} to a constructor expression"

/-- Converts a `Range` that is either an `Unknown` or `Ctor` to
    a term in *constructor application form*, represented as a pair of type `(Name × List ConstructorExpr)`
    (constructor name applied to zero or more arguments which may themselves be `ConstructorExpr`s) -/
def convertRangeToCtorAppForm (r : Range) : UnifyM (Name × List ConstructorExpr) :=
  match r with
  | Range.Unknown u => return (u, [])
  | Range.Ctor c rs => do
    let args ← rs.mapM convertRangeToConstructorExpr
    return (c, args)
  | _ => throwError m!"Unable to convert {r} to a constructor expression"

/-- Given a `conclusion` to a constructor, a list of `outputVars` and a `deriveSort`,
    figures out the appropriate `ScheduleSort`.

    - The `returnOption` boolean argument is used to determine
      whether producers should return their results wrapped in an `Option` or not.

    - The `ctorNameOpt` argument is an (optional) constructor name for the produced value
      + This is `none` for checkers/theorem schedules as they don't produce constructor applications like generators/enumerators.
    - Note: callers should supply `none` as the `ctorNameOpt` argument if `deriveSort := .Theorem`  or `.Checker` -/
def getScheduleSort (conclusion : HypothesisExpr) (outputVars : List Unknown) (ctorNameOpt : Option Name) (deriveSort : DeriveSort) (returnOption : Bool) : UnifyM ScheduleSort :=
  match deriveSort with
  | .Checker => return .CheckerSchedule
  | .Theorem => return (.TheoremSchedule conclusion (typeClassUsed := true))
  | _ => do
    let outputValues ← outputVars.mapM UnifyM.evaluateUnknown
    let producerSort :=
      if let .Enumerator := deriveSort then ProducerSort.Enumerator
      else ProducerSort.Generator
    let conclusion ← do
      if returnOption then
        pure outputValues
      else
        let ctorName ← Option.getDM ctorNameOpt
          (throwError "No constructor name given for Non-theorem schedule")
        pure [ConstructorExpr.Ctor ctorName outputValues]
    return .ProducerSchedule producerSort conclusion


/-- `rewriteFunctionCallsInConclusion hypotheses conclusion inductiveRelationName` does the following:
    1. Checks if the `conclusion` contains a function call where the function is *not* the same as the `inductiveRelationName`.
       (If no, we just return the pair `(hypotheses, conclusion)` as is.)
    2. If yes, we create a fresh variable & add an extra hypothesis where the fresh var is bound to the result of the function call.
    3. We add the fresh variable to the `unknowns` set and the `constraints` map in `UnifyState`, where it maps to an `Undef` range
       (see comments in the body of this function for more details).
    4. We then rewrite the conclusion, replacing occurrences of the function call with the fresh variable.
    The updated hypotheses, conclusion, a list of the names & types of the fresh variables produced, and new `LocalContext` are subsequently returned.
    - Note: it is the caller's responsibility to check that `conclusion` does indeed contain
      a non-trivial function application (e.g. by using `containsNonTrivialFuncApp`) -/
def rewriteFunctionCallsInConclusion (hypotheses : Array Expr) (conclusion : Expr) (inductiveRelationName : Name) (localCtx : LocalContext) : UnifyM (Array Expr × Expr × List (Name × Expr) × LocalContext) := do
  -- Find all sub-terms which are non-trivial function applications
  let funcAppExprs ← conclusion.foldlM (init := []) (fun acc subExpr => do
    if (← containsNonTrivialFuncApp subExpr inductiveRelationName)
      then
      trace[plausible.deriving.arbitrary]  m!"{repr subExpr} has a function call in it"
      pure (subExpr :: acc)
    else
      pure acc)

  match funcAppExprs with
  | [] => pure (hypotheses, conclusion, [], ← getLCtx)
  | _ => withLCtx' localCtx do

    let mut freshUnknownsAndTypes := #[]
    for funcAppExpr in funcAppExprs do
      let funcAppType ← inferType funcAppExpr

      -- Create a fresh name (an `Unknown`), insert it into the set of unknowns in `UnifyState`
      -- Thie fresh unknown has the same type as the result of the function application (`funcAppType`),
      -- so we give it a `Range` of `Undef funcAppType`
      let freshUnknown := (localCtx.getUnusedName `unk)
      UnifyM.insertUnknown freshUnknown
      UnifyM.update freshUnknown (.Undef funcAppType)
      freshUnknownsAndTypes := freshUnknownsAndTypes.push (freshUnknown, funcAppType)

    -- We use `withLocalDecl` to add all the fresh variables produced to the local context
    withLocalDeclsDND freshUnknownsAndTypes (fun freshVarExprs => do
      -- Association list mapping each function call to the corresponding fresh variable
      let newEqualities := List.zip funcAppExprs freshVarExprs.toList

      let mut additionalHyps := #[]

      -- For each (fresh variable, function call result) pair,
      -- create a new hypothesis stating that `newVarExpr = funcAppExpr`,
      -- and add it to the array of all hypotheses
      for (newVarExpr, funcAppExpr) in Array.zip freshVarExprs funcAppExprs.toArray do
        let newHyp ← mkEq newVarExpr funcAppExpr
        additionalHyps := additionalHyps.push newHyp

      let updatedHypotheses := hypotheses ++ additionalHyps

      let rewrittenConclusion ← conclusion.traverseChildren (fun subExpr =>
        match List.lookup subExpr newEqualities with
        | some freshVar => pure freshVar
        | none => pure subExpr)

      -- Insert the fresh variable into the bound-variable context
      return (updatedHypotheses, rewrittenConclusion, freshUnknownsAndTypes.toList, ← getLCtx))



/-- Unifies each argument in the conclusion of an inductive relation with the top-level arguments to the relation
    (using the unification algorithm from Generating Good Generations),
    and subsequently computes a *naive* schedule for a generator/enumerator/checker (indicated by the `deriveSort`).

    Note: this function processes the entire type of the constructor within the same `LocalContext`
    (the one produced by `forallTelescopeReducing`).

    This function takes the following as arguments:
    - The name of the inductive relation `inductiveName`
    - The constructor name `ctorName`
    - The sort of function we are deriving (`deriveSort`) (either a generator, enumerator or a checker)
    - The names of inputs `inputNames` (arguments to the derived function)
    - An option `outputNameTypeOption` containing the name & type of the output (value to be produced)
      + This option should be `some` pair if `deriveSort = .Generator` or `.Enumerator`, and none otherwise
    - An array of unknowns (`unknownsArray`), which are provided to the unification algorithm
      + This array should be non-empty if `deriveSort = .Generator` or `.Enumerator`, and empty otherwise
      + Note: when `deriveSort == .Generator / .Enumerator`, it is the caller's responsibility to ensure that
        `unknowns == inputNames ∪ { outputName }`, i.e. `unknowns` contains all args to the inductive relation
        listed in order, which coincides with `inputNames ∪ { outputName }` -/
def getScheduleForInductiveRelationConstructor
  (inductiveName : Name) (ctorName : Name) (inputNames : List Name)
  (deriveSort : DeriveSort) (outputNameTypeOption : Option (Name × Expr)) (unknownsArray : Array Unknown) : UnifyM Schedule := do
  trace[plausible.deriving.arbitrary] "Schedule requested for inductive {inductiveName}'s constructor, {ctorName} with inputs: {inputNames} and outputs: {unknownsArray}"

  let ctorInfo ← getConstInfoCtor ctorName
  let ctorType := ctorInfo.type

  -- Stay within the forallTelescope scope for all processing
  forallTelescopeReducing ctorType (cleanupAnnotations := true) (fun forAllVarsAndHyps conclusion => do
    -- Collect all the universally-quantified variables + hypotheses
    -- Universally-quantified variables `x : τ` are represented using `(some x, τ)`
    -- Hypotheses are represented using `(none, hyp)` (first component is `none` since a hypothesis doesn't have a name)
    let forAllVarsAndHypsWithTypes ← forAllVarsAndHyps.mapM (fun fvar => do
      let localCtx ← getLCtx
      let localDecl := localCtx.get! fvar.fvarId!
      let userName := localDecl.userName
      if not userName.hasMacroScopes then
        return (some userName, localDecl.type)
      else
        return (none, localDecl.type))

    -- Extract the universally quantified variables
    let forAllVars := forAllVarsAndHypsWithTypes.filterMap (fun (nameOpt, ty) =>
      match nameOpt with
      | some name => some (name, ty)
      | none => none) |>.toList

    -- Extract hypotheses (which correspond to pairs in `forAllVarsAndHypsWithTypes` where the first component is `none`)
    let hypotheses := forAllVarsAndHypsWithTypes.filterMap (fun (nameOpt, tyExpr) =>
      match nameOpt with
      | none => some tyExpr
      | some _ => none)

    -- Check if the conclusion contains a non-trivial function call
    -- (i.e. one where the function is not a constructor of an inductive type)
    let conclusionNeedsRewriting ← containsNonTrivialFuncApp conclusion inductiveName

    -- For each function call in the cocnlusion, rewrite it by introducing a fresh variable
    -- equal to the result of the function call, and adding an extra hypothesis asserting equality
    -- between the function call and the variable.
    -- `freshNamesAndTypes` is a list containing the names & types of the fresh variables produced during this procedure.
    let (updatedHypotheses, updatedConclusion, freshNamesAndTypes, updatedLocalCtx) ←
      if conclusionNeedsRewriting then
        rewriteFunctionCallsInConclusion hypotheses conclusion inductiveName (← getLCtx)
      else
        pure (hypotheses, conclusion, [], ← getLCtx)

    -- Enter the updated `LocalContext` containing the fresh variable that was created when rewriting the conclusion
    withLCtx' updatedLocalCtx (do
      -- Stores the representation of hypotheses as a `HypothesisExpr`
      -- (constructor name applied to some list of arguments, which are themselves `ConstructorExpr`s)
      let mut hypothesisExprs := #[]

      for hyp in updatedHypotheses do
        let hypTerm ← withOptions setDelaboratorOptions (delabExprInLocalContext updatedLocalCtx hyp)
        -- Convert the `TSyntax` representation of the hypothesis to a `Range`
        -- If that fails, convert the `Expr` representation of the hypothesis to a `Range`
        -- (the latter is needed to handle hypotheses which use infix operators)
        let hypRange ←
          try convertHypothesisTermToRange hypTerm
          catch _ => convertExprToRangeInCurrentContext hyp

        -- Convert each hypothesis' range to a `HypothesisExpr`, which is just a constructor application
        -- (constructor name applied to some list of arguments, which are themselves `ConstructorExpr`s)
        hypothesisExprs := hypothesisExprs.push (← convertRangeToCtorAppForm hypRange)

      -- let hypothesisExprs' ← monadLift (updatedHypotheses.toList.mapM exprToHypothesisExpr)
      -- let hypothesisExprs'' ←
      --   try pure (hypothesisExprs'.map (Option.get!))
      --   catch _ => throwError m!"Could not convert {updatedHypotheses} to HypothesisExprs"

      -- Creates the initial `UnifyState` needed for the unification algorithm
      let initialUnifyState ←
        match deriveSort with
        | .Generator | .Enumerator =>
           match outputNameTypeOption with
          | none => throwError "Output name & type not specified when deriving producer"
          | some (outputName, outputType) => pure $ mkProducerInitialUnifyState inputNames outputName outputType forAllVars hypothesisExprs.toList
        | .Checker | .Theorem => pure $ mkCheckerInitialUnifyState inputNames forAllVars hypothesisExprs.toList

      -- Extend the current state with the contents of `initialUnifyState`
      UnifyM.extendState initialUnifyState

      -- Get the ranges corresponding to each of the unknowns
      -- For producers, we simply use the `unknownsArray` that this function receives as an argument
      -- For checkers, there is no notion of `unknowns` (all arguments to the inductive relation are inputs to the checker),
      -- so we can just use `inputNames`
      let unknowns:=
        if deriveSort.isProducer then
          unknownsArray
        else
          inputNames.toArray
      let unknownRanges ← unknowns.mapM processCorrespondingRange
      let unknownArgsAndRanges := unknowns.zip unknownRanges

      -- Compute the appropriate `Range` for each argument in the constructor's conclusion
      let conclusionArgs := updatedConclusion.getAppArgs
      let conclusionRanges ← conclusionArgs.mapM convertExprToRangeInCurrentContext
      let conclusionArgsAndRanges := conclusionArgs.zip conclusionRanges

      for ((_, r1), (_, r2)) in conclusionArgsAndRanges.zip unknownArgsAndRanges do
        unify r1 r2

      -- Convert the conclusion from an `Expr` to a `HypothesisExpr`
      let conclusionExpr ← exprToHypothesisExpr conclusion

      let ctorNameOpt :=
        match deriveSort with
        | .Generator | .Enumerator => some ctorName
        | .Checker | .Theorem => none

      let (outputVars, recCall) ←
        match deriveSort with
        | .Generator | .Enumerator =>
          match outputNameTypeOption with
          | none => throwError "Error: output name & type not specified when deriving producer"
          | some (outputName, _) =>
          let outputIdx := unknowns.idxOf outputName
          pure ([outputName], (inductiveName, [outputIdx]))
        | .Checker | .Theorem => pure ([], (inductiveName, []))

      -- Determine the appropriate `ScheduleSort` (right now we only produce `ScheduleSort`s for `Generator`s)
      let scheduleSort ← getScheduleSort
        conclusionExpr
        (outputVars := outputVars)
        (ctorNameOpt := ctorNameOpt)
        (deriveSort := deriveSort)
        (returnOption := true)

      -- Check which universally-quantified variables have a `Fixed` range,
      -- so that we can supply them to `possibleSchedules` as the `fixedVars` arg
      let fixedVars ← forAllVars.filterMapM (fun (v, _) => do
        if (← UnifyM.isUnknownFixed v) then
          return some v
        else
          return none)

      -- Include any fresh variables produced (when rewriting function calls in conclusions)
      -- in the list of universally-quantified variables
      let updatedForAllVars := List.map (fun (n,ty) => ⟨n,ty⟩) (forAllVars ++ freshNamesAndTypes)
      -- Compute all possible checker schedules for this constructor
      let possibleSchedules := possibleSchedules
        (vars := updatedForAllVars)
        (hypotheses := hypothesisExprs.toList)
        deriveSort
        recCall
        fixedVars

      match possibleSchedules with
      | .lnil => throwError m!"Unable to compute any possible schedules"
      | .lcons fstSchdM rest =>

      let fstSchd ← fstSchdM

      let countChecks (schd : List ScheduleStep) : Nat :=
        schd.foldl (fun acc step => match step with | .Check _ _ => acc + 1 | _ => acc) 0

      let mut minChecks := countChecks fstSchd
      let mut countSeen  := 1
      let mut minLen     := fstSchd.length
      let mut bestSchedule   := fstSchd

      let prefixSize := 100000

      trace[plausible.deriving.arbitrary] m!"First Schedule: {scheduleStepsToString bestSchedule} \nChecks & Length: {(minChecks, minLen)} \nSchedules Considered: {repr countSeen}"

      for schdM in LazyList.take prefixSize rest.get do
        let schd ← schdM
        let checkCount := countChecks schd
        countSeen := countSeen + 1
        let len := schd.length
        if checkCount < minChecks || (checkCount == minChecks && len < minLen) then
          bestSchedule := schd
          minChecks := checkCount
          minLen := len
          trace[plausible.deriving.arbitrary] m!"Better Schedule: {scheduleStepsToString bestSchedule} \nChecks & Length: {(minChecks, minLen)} \nSchedules Considered: {repr countSeen}"


      trace[plausible.deriving.arbitrary] m!"Chosen Schedule: {scheduleStepsToString bestSchedule} \nChecks & Length: {(minChecks, minLen)} \nSchedules Considered: {repr countSeen}"

      -- Update the best schedule with the result of unification
      let updatedBestSchedule ← updateScheduleSteps bestSchedule
      let finalState ← get

      -- Takes the `patterns` and `equalities` fields from `UnifyState` (created after
      -- the conclusion of a constructor has been unified with the top-level arguments to the inductive relation),
      -- convert them to the appropriate `ScheduleStep`s, and prepends them to the `naiveSchedule`
      pure $ addConclusionPatternsAndEqualitiesToSchedule finalState.patterns finalState.equalities (updatedBestSchedule, scheduleSort))
  )


/-- Unifies each argument in the conclusion of an inductive relation with the top-level arguments to the relation
    (using the unification algorithm from Generating Good Generations),
    and subsequently computes a *naive* generator schedule for a sub-generator corresponding to the constructor
    (using the schedules discussed in Testing Theorems).

    This function takes the following as arguments:
    - The name of the inductive relation `inductiveName`
    - The constructor name `ctorName`
    - The name (`outputName`) and type (`outputType`) of the output (value to be generated)
    - The names of inputs `inputNames` (arguments to the generator)
    - An array of `unknowns` (the arguments to the inductive relation)
      + Note: `unknowns == inputNames ∪ { outputName }`, i.e. `unknowns` contains all args to the inductive relation
        listed in order, which coincides with `inputNames ∪ { outputName }` -/
def getProducerScheduleForInductiveConstructor (inductiveName : Name) (ctorName : Name) (outputName : Name) (outputType : Expr) (inputNames : List Name)
  (unknowns : Array Unknown) (deriveSort : DeriveSort) : UnifyM Schedule :=
  getScheduleForInductiveRelationConstructor inductiveName ctorName inputNames deriveSort (some (outputName, outputType)) unknowns


/-- Produces an instance of a typeclass for a constrained producer (either `ArbitrarySizedSuchThat` or `EnumSizedSuchThat`).
    The arguments to this function are:

    - `outputVar` and `outputTypeSyntax` are the name & type of the value to be generated,
    - `constrainingProp` is the proposition constraining the generated values need to satisfy
    - `deriveSort` is the sort of function we are deriving (either `.Generator` or `.Enumerator`) -/
def deriveConstrainedProducer (outputVar : Ident) (outputTypeSyntax : TSyntax `term) (constrainingProp : TSyntax `term) (deriveSort : DeriveSort) : CommandElabM (TSyntax `command) := do
  -- Determine what sort of producer we're deriving (a `Generator` or an `Enumerator`)
  let producerSort := convertDeriveSortToProducerSort deriveSort

  -- Parse the body of the lambda for an application of the inductive relation
  let (inductiveSyntax, argIdents) ← parseInductiveApp constrainingProp
  let inductiveName := inductiveSyntax.getId

  -- Figure out the name and type of the value we wish to generate (the "output")
  let outputName := outputVar.getId
  let outputType ← liftTermElabM $ elabTerm outputTypeSyntax none

  -- Find the index of the argument in the inductive application for the value we wish to generate
  -- (i.e. find `i` s.t. `argIdents[i] == outputName`)
  let outputIdxOpt := findTargetVarIndex outputName argIdents
  if let .none := outputIdxOpt then
    throwError "cannot find index of value to be generated"
  let outputIdx := Option.get! outputIdxOpt

  -- Obtain Lean's `InductiveVal` data structure, which contains metadata about the inductive relation
  let inductiveVal ← getConstInfoInduct inductiveName

  -- Determine the type for each argument to the inductive
  let inductiveTypeComponents ← liftTermElabM $ getComponentsOfArrowType inductiveVal.type

  -- To obtain the type of each arg to the inductive,
  -- we pop the last element (`Prop`) from `inductiveTypeComponents`
  let argTypes := inductiveTypeComponents.pop
  let argNames := (fun ident => ident.getId) <$> argIdents
  let argNamesTypes := argNames.zip argTypes

  -- Add the name & type of each argument to the inductive relation to the `LocalContext`
  -- Then, derive `baseProducers` & `inductiveProducers` (the code for the sub-producers
  -- that are invoked when `size = 0` and `size > 0` respectively),
  -- and obtain freshened versions of the output variable / arguments (`freshenedOutputName`, `freshArgIdents`)
  let (baseProducers, inductiveProducers, freshenedOutputName, freshArgIdents, localCtx) ←
    liftTermElabM $ withLocalDeclsDND argNamesTypes (fun _ => do
      let mut localCtx ← getLCtx
      let mut freshUnknowns := #[]

      -- For each arg to the inductive relation (as specified to the user),
      -- create a fresh name (to avoid clashing with names that may appear in constructors
      -- of the inductive relation). Note that this requires updating the `LocalContext`.
      for argName in argNames do
        let freshArgName := localCtx.getUnusedName argName
        localCtx := localCtx.renameUserName argName freshArgName
        freshUnknowns := freshUnknowns.push freshArgName

      -- Since the `output` also appears as an argument to the inductive relation,
      -- we also need to freshen its name
      let freshenedOutputName := freshUnknowns[outputIdx]!

      -- Each argument to the inductive relation (except the one at `outputIdx`)
      -- is treated as an input
      let freshenedInputNamesExcludingOutput := (Array.eraseIdx! freshUnknowns outputIdx).toList

      let mut nonRecursiveProducers := #[]
      let mut recursiveProducers := #[]

      let freshSize' := mkIdent $ localCtx.getUnusedName `size'

      let mut requiredInstances := #[]

      for ctorName in inductiveVal.ctors do
        let scheduleOption ← (UnifyM.runInMetaM
          (getProducerScheduleForInductiveConstructor inductiveName ctorName freshenedOutputName
            outputType freshenedInputNamesExcludingOutput freshUnknowns deriveSort)
            emptyUnifyState)
        match scheduleOption with
        | some schedule =>
          -- Obtain a sub-producer for this constructor, along with an array of all typeclass instances that need to be defined beforehand.
          -- (Under the hood, we compile the schedule to an `MExp`, then compile the `MExp` to a Lean term containing the code for the sub-producer.
          -- This is all done in a state monad: when we detect that a new instance is required, we append it to an array of `TSyntax term`s
          -- (where each term represents a typeclass instance)
          let (subProducer, instances) ← StateT.run (s := #[]) (do
            let mexp ← MExp.scheduleToMExp schedule (.MId `size) (.MId `initSize) outputType
            MExp.mexpToTSyntax mexp deriveSort)

          requiredInstances := requiredInstances ++ instances

          -- Determine whether the constructor is recursive
          -- (i.e. if the constructor has a hypothesis that refers to the inductive relation we are targeting)
          let isRecursive ← isConstructorRecursive inductiveName ctorName

          if isRecursive then
            -- Following the QuickChick convention,
            -- recursive sub-generators have a weight of `.succ size'`
            -- and sub-enumerators don't have any weight associated with them
            let subProducerTerm ←
              match producerSort with
              | .Generator => `( ($(mkIdent ``Nat.succ) $freshSize', $subProducer) )
              | .Enumerator => pure subProducer
            recursiveProducers := recursiveProducers.push subProducerTerm
          else
            -- Following the QuickChick convention,
            -- non-recursive sub-generators have a weight of 1
            -- (sub-enumerators don't have any weight associated with them)
            let subGeneratorTerm ←
              match producerSort with
              | .Generator => `( (1, $subProducer) )
              | .Enumerator => pure subProducer
            nonRecursiveProducers := nonRecursiveProducers.push subGeneratorTerm

        | none => throwError m!"Unable to derive producer schedule for constructor {ctorName}"

      if (not requiredInstances.isEmpty) then
        let deduplicatedInstances := List.eraseDups requiredInstances.toList
        trace[plausible.deriving.arbitrary]  m!"Required typeclass instances (please derive these first if they aren't already defined):\n{deduplicatedInstances}"

      -- Collect all the base / inductive producers into two Lean list terms
      -- Base producers are invoked when `size = 0`, inductive producers are invoked when `size > 0`
      let baseProducers ← `([$nonRecursiveProducers,*])
      let inductiveProducers ← `([$nonRecursiveProducers,*, $recursiveProducers,*])

      return (baseProducers, inductiveProducers, freshenedOutputName, Lean.mkIdent <$> freshUnknowns, localCtx))

  -- Create an instance of the appropriate producer typeclass
  mkConstrainedProducerTypeClassInstance
    baseProducers
    inductiveProducers
    inductiveSyntax
    freshArgIdents
    freshenedOutputName
    outputTypeSyntax
    producerSort
    localCtx


/-- Derives an instance of the `ArbitrarySuchThat` typeclass,
    where `outputVar` and `outputTypeSyntax` are the name & type of the value to be generated,
    and `constrainingProp` is a proposition which generated values need to satisfy -/
def deriveArbitrarySuchThatInstance (outputVar : Ident) (outputTypeSyntax : TSyntax `term) (constrainingProp : TSyntax `term) : CommandElabM (TSyntax `command) :=
  deriveConstrainedProducer outputVar outputTypeSyntax constrainingProp (deriveSort := .Generator)

/-- Derives an instance of the `EnumSuchThat` typeclass,
    where `outputVar` and `outputTypeSyntax` are the name & type of the value to be generated,
    and `constrainingProp` is a proposition which generated values need to satisfy -/
def deriveEnumSuchThatInstance (outputVar : Ident) (outputTypeSyntax : TSyntax `term) (constrainingProp : TSyntax `term) : CommandElabM (TSyntax `command) :=
  deriveConstrainedProducer outputVar outputTypeSyntax constrainingProp (deriveSort := .Enumerator)

/-- Command for deriving a constrained generator for an inductive relation -/
syntax (name := derive_generator) "#derive_generator" "(" "fun" "(" ident ":" term ")" "=>" term ")" : command

/-- Elaborator for the `#derive_generator` command which derives a constrained generator
    using generator schedules from Testing Theorems & the unification algorithm from Generating Good Generators -/
@[command_elab derive_generator]
def elabDeriveGenerator : CommandElab := fun stx => do
  match stx with
  | `(#derive_generator ( fun ( $var:ident : $outputTypeSyntax:term ) => $body:term )) => do
    -- Derive an instance of the `ArbitrarySuchThat` typeclass
    let typeClassInstance ← deriveArbitrarySuchThatInstance var outputTypeSyntax body

    -- Pretty-print the derived generator
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeClassInstance)

    -- Display the code for the derived generator to the user
    logInfo m!"Try this generator: {Format.pretty genFormat}"

    elabCommand typeClassInstance

  | _ => throwUnsupportedSyntax

/-- Command for deriving a constrained generator for an inductive relation -/
syntax (name := derive_enumerator) "#derive_enumerator" "(" "fun" "(" ident ":" term ")" "=>" term ")" : command

/-- Elaborator for the `#derive_generator` command which derives a constrained generator
    using generator schedules from Testing Theorems & the unification algorithm from Generating Good Generators -/
@[command_elab derive_enumerator]
def elabDeriveScheduledEnumerator : CommandElab := fun stx => do
  match stx with
  | `(#derive_enumerator ( fun ( $var:ident : $outputTypeSyntax:term ) => $body:term )) => do
    -- Derive an instance of the `ArbitrarySuchThat` typeclass
    let typeClassInstance ← deriveEnumSuchThatInstance var outputTypeSyntax body

    -- Pretty-print the derived generator
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeClassInstance)

    -- Display the code for the derived generator to the user
    logInfo m!"Try this enumerator: {Format.pretty genFormat}"

    elabCommand typeClassInstance

  | _ => throwUnsupportedSyntax
