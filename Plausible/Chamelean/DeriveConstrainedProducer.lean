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
def mkInitialUnknownMap (inputNames: List Name)
  (outputName : Name) (outputType : Expr)
  (forAllVariables : List (Name × Expr)) : UnknownMap :=
  let inputConstraints := inputNames.map (fun n => (n, .Fixed))
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
def mkProducerInitialUnifyState (inputNames : List Name)
  (outputName : Name)
  (outputType : Expr)
  (forAllVariables : List (Name × Expr))
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
def mkCheckerInitialUnifyState (inputNames : List Name)
  (forAllVariables : List (Name × Expr))
  (hypotheses : List (Name × List ConstructorExpr)) : UnifyState :=
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
    else if constInfo.isDefinition then
      throwError m!"Cannot convert definition {term} to a Range"
    else /- TODO: Does this case need to exist? -/
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
def getScheduleSort (conclusion : HypothesisExpr)
  (outputVars : List Unknown)
  (ctorNameOpt : Option Name)
  (deriveSort : DeriveSort) (returnOption : Bool) : UnifyM ScheduleSort :=
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
    3. Additionally, checks for nonlinear variable occurrences (variables appearing multiple times) and creates fresh variables
       for all but the first occurrence, adding equality hypotheses between the fresh and original variables.
    4. We add the fresh variables to the `unknowns` set and the `constraints` map in `UnifyState`, where they map to `Undef` ranges.
    5. We then rewrite the conclusion, replacing occurrences of function calls and duplicate variables with fresh variables.
    The updated hypotheses, conclusion, a list of the names & types of the fresh variables produced, and new `LocalContext` are subsequently returned.
    - Note: it is the caller's responsibility to check that `conclusion` does indeed contain
      a non-trivial function application (e.g. by using `containsNonTrivialFuncApp`) -/
def linearizeAndFlatten
  (hypotheses : Array Expr) (conclusion : Expr) (outputIndex : Option Nat) (localCtx : LocalContext) :
  UnifyM (Array Expr × Expr × List (Name × Expr) × LocalContext) := do
  -- Find all sub-terms which are non-trivial function applications
  let funcAppExprs ← collectUnmatchableProperSubterms conclusion

  withLCtx' localCtx do

  let mut freshUnknownsAndTypes := #[]

  -- Handle function calls
  for i in List.range funcAppExprs.length do
    let funcAppExpr := funcAppExprs[i]!
    let funcAppType ← inferType funcAppExpr
    let freshUnknown := localCtx.getUnusedName <| (`unk).appendAfter s!"_{i}"

    UnifyM.insertUnknown freshUnknown
    UnifyM.update freshUnknown (.Undef funcAppType)
    freshUnknownsAndTypes := freshUnknownsAndTypes.push (freshUnknown, funcAppType)

  withLocalDeclsDND freshUnknownsAndTypes (fun freshVarExprs => do
    -- Association list mapping each function call to the corresponding fresh variable
    let funcCallEqualities := List.zip funcAppExprs freshVarExprs.toList

    let mut additionalHyps := #[]

    -- Add hypotheses for function calls
    for (funcAppExpr, newVarExpr) in funcCallEqualities do
      let newHyp ← mkEq newVarExpr funcAppExpr
      additionalHyps := additionalHyps.push newHyp

    trace[plausible.deriving.arbitrary] m!"Original Conclusion: {conclusion}"
    let conclusion := replaceExprsRecursivelyOnce conclusion funcCallEqualities none
    trace[plausible.deriving.arbitrary] m!"Rewritten Conclusion after flattening: {conclusion}"

    let functionsNewTypedVars := freshUnknownsAndTypes
    let functionsNewHyps := additionalHyps

    -- Count variable occurrences to find nonlinear patterns
    let varOccurrences := collectFVarOccurrences conclusion outputIndex

    trace[plausible.deriving.arbitrary] s!"varOccurences: {repr varOccurrences.toList} \n expr: {conclusion} \n outputIndex {outputIndex}"

    let nonlinearVars := varOccurrences.toList.filter (fun (_, count) => count > 1)

    -- Handle nonlinear variables
    let mut nonlinearReplacements := []

    let mut freshUnknownsAndTypes := #[]
    for (fvarId, count) in nonlinearVars do
      let originalVar := mkFVar fvarId
      let varType ← inferType originalVar
      if varType.isSort then continue
      let varName ← fvarId.getUserName

      -- Create count-1 fresh variables (keeping first occurrence as original)
      for i in List.range (count - 1) do
        let freshName := varName.appendAfter s!"_{i + 1}"
        let freshUnknown := localCtx.getUnusedName freshName
        UnifyM.insertUnknown freshUnknown
        UnifyM.update freshUnknown (.Undef varType)
        freshUnknownsAndTypes := freshUnknownsAndTypes.push (freshUnknown, varType)
        nonlinearReplacements := (originalVar, freshUnknown) :: nonlinearReplacements

     -- We use `withLocalDecl` to add all the fresh variables produced to the local context
    withLocalDeclsDND freshUnknownsAndTypes (fun freshVarExprs => do
      -- Map nonlinear variable replacements to fresh variables
    let nonlinearVarEqualities := List.zip (nonlinearReplacements.reverse.map (·.1)) (freshVarExprs.toList)
    let mut additionalHyps := #[]
    -- Add hypotheses for nonlinear variables
    for (originalVar, freshVar) in nonlinearVarEqualities do
      let newHyp ← mkEq freshVar originalVar
      additionalHyps := additionalHyps.push newHyp

    let updatedHypotheses := hypotheses ++ additionalHyps ++ functionsNewHyps

    trace[plausible.deriving.arbitrary] m!"Flattened Conclusion: {conclusion}"
    let rewrittenConclusion := replaceExprsRecursivelyOnce conclusion nonlinearVarEqualities outputIndex
    trace[plausible.deriving.arbitrary] m!"Rewritten Conclusion after linearizing: {rewrittenConclusion}"


    -- Insert the fresh variable into the bound-variable context
    return (updatedHypotheses, rewrittenConclusion, freshUnknownsAndTypes.toList ++ functionsNewTypedVars.toList, ← getLCtx)

    )
  )

structure ScheduleScore where
  checks : Nat
  length : Nat
  unconstrained : Nat
  deriving Ord, Repr

def scheduleStepsScore (schedule : List ScheduleStep) : ScheduleScore :=
  let steps := schedule
  Id.run do
    let mut checks := 0
    let mut length := 0
    let mut unconstrained := 0
    for step in steps do
      length := length + 1
      match step with
      | .Check .. => checks := checks + 1
      | .Unconstrained .. => unconstrained := unconstrained + 1
      | _ => ()
    ⟨checks, length, unconstrained⟩

instance scheduleStepsScoreLT : LT ScheduleScore := ⟨fun a b => compare a b |>.isLT⟩

instance scheduleScoreLTDecidable {a b : ScheduleScore} : Decidable (a < b) :=
  decidable_of_bool ((compare a b).isLT) (by simp [scheduleStepsScoreLT])

def scheduleLT (a b : List ScheduleStep) := scheduleStepsScore a < scheduleStepsScore b

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
  (deriveSort : DeriveSort) (outputNameTypeOption : Option (Name × Expr × Nat)) (unknownsArray : Array Unknown) (localCtx : LocalContext) : UnifyM Schedule := do
  trace[plausible.deriving.arbitrary] "Schedule requested for inductive {inductiveName}'s constructor, {ctorName} with inputs: {inputNames} and variables: {unknownsArray}, outputInfo: {outputNameTypeOption}"

  let ctorInfo ← getConstInfoCtor ctorName
  let ctorType := ctorInfo.type

  withLCtx' localCtx do

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

    let outputIndex := (fun a => a.snd.snd) <$> outputNameTypeOption

    -- For each function call in the cocnlusion, rewrite it by introducing a fresh variable
    -- equal to the result of the function call, and adding an extra hypothesis asserting equality
    -- between the function call and the variable.
    -- `freshNamesAndTypes` is a list containing the names & types of the fresh variables produced during this procedure.
    let (updatedHypotheses, updatedConclusion, freshNamesAndTypes, updatedLocalCtx) ←
      linearizeAndFlatten hypotheses conclusion outputIndex (← getLCtx)
    -- Enter the updated `LocalContext` containing the fresh variable that was created when rewriting the conclusion
    withLCtx' updatedLocalCtx (do
      let hypothesisExprs := (← monadLift (updatedHypotheses.toList.mapM exprToHypothesisExpr)).toArray

      trace[plausible.deriving.arbitrary] m!"Hypotheses to be ordered as HypothesisExprs: {updatedHypotheses}"

      -- Creates the initial `UnifyState` needed for the unification algorithm
      let initialUnifyState ←
        match deriveSort with
        | .Generator | .Enumerator =>
           match outputNameTypeOption with
          | none => throwError "Output name & type not specified when deriving producer"
          | some (outputName, outputType, _outputIndex) => pure $ mkProducerInitialUnifyState inputNames outputName outputType forAllVars hypothesisExprs.toList
        | .Checker | .Theorem => pure $ mkCheckerInitialUnifyState inputNames forAllVars hypothesisExprs.toList



      -- Extend the current state with the contents of `initialUnifyState`
      UnifyM.extendState initialUnifyState

      trace[plausible.deriving.arbitrary] m!"Initial Unify State: \n{← get}"

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

      trace[plausible.deriving.arbitrary] m!"Unify State after processing unknown ranges: \n{← get}"

      -- Compute the appropriate `Range` for each argument in the constructor's conclusion
      let conclusionArgs := updatedConclusion.getAppArgs
      let conclusionRanges ← conclusionArgs.mapM convertExprToRangeInCurrentContext
      let conclusionArgsAndRanges := conclusionArgs.zip conclusionRanges

      for ((_, r1), (_, r2)) in conclusionArgsAndRanges.zip unknownArgsAndRanges do
        unify r1 r2
        trace[plausible.deriving.arbitrary] m!"Current Unify State after unifying {r1} and {r2} \n: {← get}"
        assert! (← get).equalities.isEmpty

      -- Convert the conclusion from an `Expr` to a `HypothesisExpr`
      let conclusionExpr ← exprToHypothesisExpr updatedConclusion

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

      let updatedForAllVars := forAllVars ++ freshNamesAndTypes
      let fixedVars ← updatedForAllVars.filterMapM (fun (v, _) => do
        if (← UnifyM.isUnknownFixed v) then
          return some v
        else
          return none)

      -- Include any fresh variables produced (when rewriting function calls in conclusions)
      -- in the list of universally-quantified variables
      let updatedForAllVars := List.map (fun (n,ty) => ⟨n,ty⟩) updatedForAllVars
      trace[plausible.deriving.arbitrary] s!"Updated ForAll Vars: {repr updatedForAllVars}"
      trace[plausible.deriving.arbitrary] s!"Fixed Vars: {repr fixedVars}"

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

      let mut countSeen  := 1
      let mut bestScore := scheduleStepsScore fstSchd
      let mut bestSchedule   := fstSchd

      let prefixSize := 100000

      trace[plausible.deriving.arbitrary] m!"First Schedule: {scheduleStepsToString bestSchedule} \nScore: {repr bestScore}\nSchedules Considered: {repr countSeen}"

      for schdM in LazyList.take prefixSize rest.get do
        let schd ← schdM
        let score := scheduleStepsScore schd
        countSeen := countSeen + 1
        if score < bestScore then
          bestSchedule := schd
          bestScore := score
          trace[plausible.deriving.arbitrary] m!"Better Schedule: {scheduleStepsToString bestSchedule} \nScore: {repr bestScore}\nSchedules Considered: {repr countSeen}"


      trace[plausible.deriving.arbitrary] m!"Chosen Schedule: {scheduleStepsToString bestSchedule} \nScore: {repr bestScore}\nSchedules Considered: {repr countSeen}"

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
def getProducerScheduleForInductiveConstructor
  (inductiveName : Name) (ctorName : Name) (outputName : Name) (outputType : Expr) (outputIndex : Nat) (inputNames : List Name)
  (unknowns : Array Unknown) (deriveSort : DeriveSort) (localCtx : LocalContext) : UnifyM Schedule :=
  getScheduleForInductiveRelationConstructor inductiveName ctorName inputNames deriveSort (some (outputName, outputType, outputIndex)) unknowns localCtx


/-- Produces an instance of a typeclass for a constrained producer (either `ArbitrarySizedSuchThat` or `EnumSizedSuchThat`).
    The arguments to this function are:

    - `outputVar` and `outputType` are the name & type of the value to be generated,
    - `constrainingInductive` is the inductive predicate constraining the generated values need to satisfy
    - `constrArgs` are the arguments of the inductive predicate
    - `deriveSort` is the sort of function we are deriving (either `.Generator` or `.Enumerator`) -/
def deriveConstrainedProducer
  (_args : Array Expr)
  (outputVar : Expr)
  (outputType : Expr)
  (constrainingInductive : Name)
  (constrArgs : Array Expr)
  (deriveSort : DeriveSort) : TermElabM (TSyntax `command) := do
  -- Determine what sort of producer we're deriving (a `Generator` or an `Enumerator`)
  let producerSort := convertDeriveSortToProducerSort deriveSort

  let inductiveName := constrainingInductive

  -- Figure out the name and type of the value we wish to generate (the "output")
  let outputName := outputVar.fvarId!

  -- Find the index of the argument in the inductive application for the value we wish to generate
  -- (i.e. find `i` s.t. `argIdents[i] == outputName`)
  let outputIdxOpt := findTargetVarIndex outputName constrArgs
  if let .none := outputIdxOpt then
    throwError "cannot find index of value to be generated"
  let outputIdx := Option.get! outputIdxOpt

  -- Obtain Lean's `InductiveVal` data structure, which contains metadata about the inductive relation
  let inductiveVal ← getConstInfoInduct inductiveName

  -- Determine the type for each argument to the inductive
  let inductiveTypeComponents ← getComponentsOfArrowType inductiveVal.type

  -- To obtain the type of each arg to the inductive,
  -- we pop the last element (`Prop`) from `inductiveTypeComponents`
  let argTypes := inductiveTypeComponents.pop

  -- For now we fail if any argument is not a variable
  let argNames ← constrArgs.mapM
    (fun ident : Expr =>
      if ident.isFVar then
        ident.fvarId!.getUserName
      else throwError m!"{ident} is expected to be a variable.")
  let argNamesTypes := argNames.zip argTypes

  -- Add the name & type of each argument of the inductive relation to the `LocalContext`
  -- Then, derive `baseProducers` & `inductiveProducers` (the code for the sub-producers
  -- that are invoked when `size = 0` and `size > 0` respectively),
  -- and obtain freshened versions of the output variable / arguments (`freshenedOutputName`, `freshArgIdents`)
  let (baseProducers, inductiveProducers, freshenedOutputName, freshArgIdents, localCtx) ←
    withLocalDeclsDND argNamesTypes (fun _ => do
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
            outputType outputIdx freshenedInputNamesExcludingOutput freshUnknowns deriveSort localCtx)
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
    constrainingInductive
    freshArgIdents
    freshenedOutputName
    outputType
    producerSort
    localCtx


private def deriveArbitrarySuchThatInstance'
  (args : Array Expr)
  (outputVar : Expr)
  (outputType : Expr)
  (constrainingInductive : Name)
  (constrArgs : Array Expr) :
  TermElabM (TSyntax `command) := do
  deriveConstrainedProducer args outputVar outputType constrainingInductive constrArgs (deriveSort := .Generator)

private def withParsedDerivingArgs (input : Expr)
  (action :
    (args : Array Expr) → (out : Expr) → (outTy : Expr) →
    (constrInd : Name) → (constrArgs : Array Expr) → TermElabM α) : TermElabM α :=
  lambdaTelescope input <|
  fun args body => do
  let .some (outTy, body) := body.app2? ``Exists | throwError m!"Error in parsing constraint: {body} is not of the form ∃ x, P."
  let body ← whnf body
  lambdaTelescope body <|
  fun outVars body =>
  body.withApp <|
  fun ind indArgs => do
  if outVars.size ≠ 1 then throwError m!"Error in parsing constraint: Expected a single output variable, got {outVars}."
  let out := outVars[0]!
  if !ind.isConst then throwError m!"Error in parsing constraint: {ind} is expected to be a constant."
  let indName := ind.constName!
  action args out outTy indName indArgs

/-- Derives an instance of the `ArbitrarySuchThat` typeclass,
    where `outputVar` and `outputTypeSyntax` are the name & type of the value to be generated,
    and `constrainingProp` is a proposition which generated values need to satisfy -/
def deriveArbitrarySuchThatInstance (tm : Term) : TermElabM Command := do
  let e ← elabTerm tm .none
  withParsedDerivingArgs e deriveArbitrarySuchThatInstance'

def deriveEnumSuchThatInstance' (args : Array Expr) (outputVar : Expr) (outputType : Expr)
  (constrainingProp : Name) (constrArgs : Array Expr) : TermElabM (TSyntax `command) :=
  deriveConstrainedProducer args outputVar outputType constrainingProp constrArgs (deriveSort := .Enumerator)

/-- Derives an instance of the `EnumSuchThat` typeclass,
    where `outputVar` and `outputTypeSyntax` are the name & type of the value to be generated,
    and `constrainingProp` is a proposition which generated values need to satisfy -/
def deriveEnumSuchThatInstance (tm : Term) : TermElabM Command := do
  let e ← elabTerm tm .none
  withParsedDerivingArgs e deriveEnumSuchThatInstance'

/-- Command for deriving a constrained generator for an inductive relation -/
syntax (name := generator_deriver) "derive_generator" term : command

/-- Elaborator for the `derive_generator` command which derives a constrained generator
    using generator schedules from Testing Theorems & the unification algorithm from Generating Good Generators -/
@[command_elab generator_deriver]
def elabDeriveGenerator : CommandElab := fun stx => do
  match stx with
  | `(derive_generator $descr:term) => do
    -- Derive an instance of the `ArbitrarySuchThat` typeclass
    let typeClassInstance ← liftTermElabM <| deriveArbitrarySuchThatInstance descr

    -- Pretty-print the derived generator
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeClassInstance)

    -- Display the code for the derived generator to the user
    -- & prompt the user to accept it in the VS Code side panel
    liftTermElabM $ Tactic.TryThis.addSuggestion stx
      (Format.pretty genFormat) (header := "Try this generator: ")

    elabCommand typeClassInstance

  | _ => throwUnsupportedSyntax

/-- Command for deriving a constrained generator for an inductive relation -/
syntax (name := enumerator_deriver) "derive_enumerator" term : command

/-- Elaborator for the `derive_generator` command which derives a constrained generator
    using generator schedules from Testing Theorems & the unification algorithm from Generating Good Generators -/
@[command_elab enumerator_deriver]
def elabDeriveScheduledEnumerator : CommandElab := fun stx => do
  match stx with
  | `(derive_enumerator $descr:term) => do
    -- Derive an instance of the `Enumerate` typeclass
    let typeClassInstance ← liftTermElabM <| deriveEnumSuchThatInstance descr

    -- Pretty-print the derived generator
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeClassInstance)

    -- Display the code for the derived enumerator to the user
    -- & prompt the user to accept it in the VS Code side panel
    liftTermElabM $ Tactic.TryThis.addSuggestion stx
      (Format.pretty genFormat) (header := "Try this enumerator: ")

    elabCommand typeClassInstance

  | _ => throwUnsupportedSyntax
