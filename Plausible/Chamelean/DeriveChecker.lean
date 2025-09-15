import Lean

import Plausible.Chamelean.MakeConstrainedProducerInstance
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.Idents
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.UnificationMonad

open Lean Std Elab Command Meta Term Parser
open Idents



/-- Unifies each argument in the conclusion of an inductive relation with the top-level arguments to the relation
    (using the unification algorithm from Generating Good Generations),
    and subsequently computes a *naive* checker schedule for a sub-checker corresponding to the constructor
    (using the schedules discussed in Testing Theorems).

    Note: this function processes the entire type of the constructor within the same `LocalContext`
    (the one produced by `forallTelescopeReducing`).

    This function takes the following as arguments:
    - The name of the inductive relation `inductiveName`
    - The constructor name `ctorName`
    - The names of inputs `inputNames` (arguments to the checker, i.e. all arguments to the inductive relation) -/
def getCheckerScheduleForInductiveConstructor (inductiveName : Name) (ctorName : Name) (inputNames : List Name) : UnifyM Schedule :=
  getScheduleForInductiveRelationConstructor inductiveName ctorName inputNames (deriveSort := .Checker) none #[]


/-- Produces an instance of the `DecOpt` typeclass containing the definition for the top-level derived checker.
    The arguments to this function are:
    - a list of `baseCheckers` (each represented as a Lean term), to be invoked when `size == 0`
    - a list of `inductiveCheckers`, to be invoked when `size > 0`
    - the name of the inductive relation (`inductiveStx`)
    - the arguments (`args`) to the inductive relation

    - Note: this function is identical to `mkTopLevelChecker`, except it doesn't take in a `NameMap` argument
    - TODO: refactor to avoid code duplication -/
def mkDecOptInstance (baseCheckers : TSyntax `term) (inductiveCheckers : TSyntax `term)
  (inductiveStx : TSyntax `term) (args : TSyntaxArray `term) (topLevelLocalCtx : LocalContext) : CommandElabM (TSyntax `command) := do

  -- Produce a fresh name for the `size` argument for the lambda
  -- at the end of the checker function, as well as the `aux_dec` inner helper function
  let freshSizeIdent := mkFreshAccessibleIdent topLevelLocalCtx `size
  let freshSize' := mkFreshAccessibleIdent topLevelLocalCtx `size'
  let auxDecIdent := mkFreshAccessibleIdent topLevelLocalCtx `aux_dec
  let checkerType ← `($optionTypeConstructor $boolIdent)

  let inductiveName := inductiveStx.raw.getId

  -- Create the cases for the pattern-match on the size argument
  let mut caseExprs := #[]
  let zeroCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $checkerBacktrackFn $baseCheckers)
  caseExprs := caseExprs.push zeroCase

  let succCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.succ) $freshSize' => $checkerBacktrackFn $inductiveCheckers)
  caseExprs := caseExprs.push succCase

  -- Create function arguments for the checker's `size` & `initSize` parameters
  -- (former is the generator size, latter is the size argument with which to invoke other auxiliary generators/checkers)
  let initSizeParam ← `(Term.letIdBinder| ($initSizeIdent : $natIdent))
  let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))
  let matchExpr ← liftTermElabM $ mkMatchExpr sizeIdent caseExprs

  -- Add parameters for each argument to the inductive relation
  let paramInfo ← analyzeInductiveArgs inductiveName args

  -- Inner params are for the inner `aux_dec` function
  let mut innerParams := #[]
  innerParams := innerParams.push initSizeParam
  innerParams := innerParams.push sizeParam

  -- Outer params are for the top-level lambda function which invokes `aux_dec`
  let mut outerParams := #[]
  for (paramName, paramType) in paramInfo do
    let outerParamIdent := mkIdent paramName
    outerParams := outerParams.push outerParamIdent

    -- Inner parameters are for the inner `aux_arb` function
    let innerParam ← `(Term.letIdBinder| ($(mkIdent paramName) : $paramType))
    innerParams := innerParams.push innerParam

  -- Produces an instance of the `DecOpt` typeclass containing the definition for the derived generator
  `(instance : $decOptTypeclass ($inductiveStx $args*) where
      $unqualifiedDecOptFn:ident :=
        let rec $auxDecIdent:ident $innerParams* : $checkerType :=
          $matchExpr
        fun $freshSizeIdent => $auxDecIdent $freshSizeIdent $freshSizeIdent $outerParams*)



/-- Derives a checker which checks the `inductiveProp` (an inductive relation, represented as a `TSyntax term`)
    using the unification algorithm from Generating Good Generators and the schedules discuseed in Testing Theorems -/
def deriveScheduledChecker (inductiveProp : TSyntax `term) : CommandElabM (TSyntax `command) := do
  -- Parse `inductiveProp` for an application of the inductive relation
  let (inductiveSyntax, argIdents) ← parseInductiveApp inductiveProp
  let inductiveName := inductiveSyntax.getId

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
  let (baseCheckers, inductiveCheckers, freshArgIdents, localCtx) ←
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

      let mut nonRecursiveCheckers := #[]
      let mut recursiveCheckers := #[]
      let mut requiredInstances := #[]

      for ctorName in inductiveVal.ctors do
        let scheduleOption ← (UnifyM.runInMetaM
          (getCheckerScheduleForInductiveConstructor inductiveName ctorName freshUnknowns.toList)
            emptyUnifyState)
        match scheduleOption with
        | some schedule =>
          -- Obtain a sub-checker for this constructor, along with an array of all typeclass instances that need to be defined beforehand.
          -- (Under the hood, we compile the schedule to an `MExp`, then compile the `MExp` to a Lean term containing the code for the sub-producer.
          -- This is all done in a state monad: when we detect that a new instance is required, we append it to an array of `TSyntax term`s
          -- (where each term represents a typeclass instance)
          let (subChecker, instances) ← StateT.run (s := #[]) (do
            let mexp ← scheduleToMExp schedule (.MId `size) (.MId `initSize)
            mexpToTSyntax mexp (deriveSort := .Checker))

          requiredInstances := requiredInstances ++ instances

          -- Determine whether the constructor is recursive
          -- (i.e. if the constructor has a hypothesis that refers to the inductive relation we are targeting)
          let isRecursive ← isConstructorRecursive inductiveName ctorName

          -- Sub-checkers need to be thunked, since we don't want the `checkerBacktrack` combinator
          -- (which expects a list of sub-checkers as inputs) to evaluate all the sub-checkers eagerly
          let thunkedSubChecker ← `(fun _ => $subChecker)

          if isRecursive then
            recursiveCheckers := recursiveCheckers.push thunkedSubChecker
          else
            nonRecursiveCheckers := nonRecursiveCheckers.push thunkedSubChecker

        | none => throwError m!"Unable to derive producer schedule for constructor {ctorName}"

      if (not requiredInstances.isEmpty) then
        let deduplicatedInstances := List.eraseDups requiredInstances.toList
        logWarning m!"Required typeclass instances (please derive these first if they aren't already defined):\n{deduplicatedInstances}"

      -- Collect all the base / inductive checkers into two Lean list terms
      -- Base checkers are invoked when `size = 0`, inductive checkers are invoked when `size > 0`
      let baseCheckers ← `([$nonRecursiveCheckers,*])
      let inductiveCheckers ← `([$nonRecursiveCheckers,*, $recursiveCheckers,*])

      return (baseCheckers, inductiveCheckers, Lean.mkIdent <$> freshUnknowns, localCtx))

  -- Create an instance of the `DecOpt` typeclass
  mkDecOptInstance
    baseCheckers
    inductiveCheckers
    inductiveSyntax
    freshArgIdents
    localCtx

----------------------------------------------------------------------
-- NEW Command elaborator driver
-----------------------------------------------------------------------

/-- Command which derives a checker using the new schedule and unificaiton-based algorithm -/
syntax (name := derive_checker) "#derive_checker" "(" term ")" : command

/-- Command elaborator that produces the function header for the checker -/
@[command_elab derive_checker]
def elabDeriveScheduledChecker : CommandElab := fun stx => do
  match stx with
  | `(#derive_checker ( $indProp:term )) => do

    -- Produce an instance of the `DecOpt` typeclass corresponding to the inductive proposition `indProp`
    let typeclassInstance ← deriveScheduledChecker indProp

    -- Pretty-print the derived checker
    let genFormat ← liftCoreM (PrettyPrinter.ppCommand typeclassInstance)

    -- Display the code for the derived checker to the user
    -- & prompt the user to accept it in the VS Code side panel
    liftTermElabM $ Tactic.TryThis.addSuggestion stx
      (Format.pretty genFormat) (header := "Try this checker: ")

    -- Elaborate the typeclass instance and add it to the local context
    elabCommand typeclassInstance

  | _ => throwUnsupportedSyntax
