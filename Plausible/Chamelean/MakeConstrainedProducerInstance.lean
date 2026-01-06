/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
import Lean
import Std
import Plausible.Gen
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.GeneratorCombinators
import Plausible.Chamelean.TSyntaxCombinators
import Plausible.Chamelean.Idents
import Plausible.Chamelean.Utils
import Plausible.Chamelean.Schedules


open Lean Elab Command Meta Term Parser Std
open Idents Schedules

/-- Extracts the name of the induction relation and its arguments -/
def parseInductiveApp (body : Term) :
  TermElabM (TSyntax `ident × TSyntaxArray `ident) := do
  match body with
  | `($indRel:ident $args:ident*) => do
    return (indRel, args)
  | `($indRel:ident) => do
    return (indRel, #[])
  | _ => throwErrorAt body "Expected inductive type application"

/-- Instantiates a known-to-be well-typed call to inductive with array of arguments `es` one
    at a time and infers each arguments type, so renamings and dependent types are supported.
    Returns the array of types for each argument in `es`. -/
def getCorrectTypes (es : Array Expr) (ind : Name) (inductiveLevels : List Level) : TermElabM (Array Expr) := do
  trace[plausible.deriving.arbitrary] m!"Levels for inductive {ind}: {inductiveLevels}"
  let mut t : Expr := .const ind inductiveLevels
  let mut tys : Array Expr := #[]
  for e in es do
    tys := tys.push (← inferType t).bindingDomain!
    t := .app t e
  let resolvedExpr ← instantiateMVars t
  trace[plausible.deriving.arbitrary] m!"Resolved mvar type: {t} {resolvedExpr}"
  return tys

/-- Analyzes the type of the inductive relation and matches each
    argument with its expected type, returning an array of
    (parameter name, type expression) pairs -/
def analyzeInductiveArgs (inductiveName : Name) (inductiveLevels : List Level) (args : Array Term) :
  TermElabM (Array (Name × Expr × TSyntax `term)) := do
  let argNames ← monadLift <| args.mapM extractParamName
  let types ← getCorrectTypes (argNames.map (mkFVar ⟨·⟩)) inductiveName inductiveLevels
  let typesSyntax ← monadLift <| types.mapM PrettyPrinter.delab
  trace[plausible.deriving.arbitrary] m!"Types for inductive args: {typesSyntax}"
  return argNames.zip (types.zip typesSyntax)

def mkTypeClassInstanceBinders (typeParams : Array Name) (typeClasses : Array Name) : TermElabM (TSyntaxArray `Lean.Parser.Term.bracketedBinder) := do
  let instances ← typeParams.flatMapM fun param =>
    typeClasses.mapM fun tc =>
      `(Lean.Elab.Deriving.instBinderF| [$(mkIdent tc) $(mkIdent param)])
  return TSyntaxArray.mk instances

/-- Finds the index of the argument in the inductive application for the value we wish to generate
    (i.e. finds `i` s.t. `args[i] == targetVar`) -/
def findTargetVarIndex (targetVar : FVarId) (args : Array Expr) : (Option Nat) := do
  for i in [:args.size] do
    let arg := args[i]!
    if arg.isFVar then
      let varName := arg.fvarId!
      if varName == targetVar then
        return i
  none

/-- Produces an instance of the `ArbitrarySizedSuchThat` / `EnumSizedSuchThat` typeclass containing the definition for a constrained generator.
    The arguments to this function are:
    - a list of `baseGenerators` (each represented as a Lean term), to be invoked when `size == 0`
    - a list of `inductiveGenerators`, to be invoked when `size > 0`
    - the name of the inductive relation (`inductiveName`)
    - the arguments (`args`) to the inductive relation
    - the name and type for the value we wish to generate (`targetVar`, `targetType`)
    - the `producerSort`, which determines what typeclass is to be produced
      + If `producerSort = .Generator`, an `ArbitrarySizedSuchThat` instance is produced
      + If `producerSort = .Enumerator`, an `EnumSizedSuchThat` instance is produced
    - The `LocalContext` associated with the top-level inductive relation (`topLevelLocalCtx`) -/
def mkConstrainedProducerTypeClassInstance
  (baseGenerators : TSyntax `term)
  (inductiveGenerators : TSyntax `term)
  (inductiveName : Name)
  (inductiveLevels : List Level)
  (args : TSyntaxArray `term) (targetVar : Name)
  (_targetType : Expr)
  (producerSort : ProducerSort)
  (topLevelLocalCtx : LocalContext) : TermElabM (TSyntax `command) := do
    -- Produce a fresh name for the `size` argument for the lambda
    -- at the end of the generator function, as well as the `aux_arb` inner helper function
    let freshSizeIdent := mkFreshAccessibleIdent topLevelLocalCtx `size
    let freshSize' := mkFreshAccessibleIdent topLevelLocalCtx `size'

    -- The (backtracking) combinator to be invoked
    -- (`GeneratorCombinators.backtrack` for generators, `EnumeratorCombinators.enumerate` for enumerators)
    let combinatorFn :=
      match producerSort with
      | .Generator => genBacktrackFn
      | .Enumerator => enumerateFn

    -- Create the cases for the pattern-match on the size argument
    let mut caseExprs := #[]
    let zeroCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.zero) => $combinatorFn $baseGenerators)
    caseExprs := caseExprs.push zeroCase

    let succCase ← `(Term.matchAltExpr| | $(mkIdent ``Nat.succ) $freshSize' => $combinatorFn $inductiveGenerators)
    caseExprs := caseExprs.push succCase

    -- Create function arguments for the producer's `size` & `initSize` parameters
    -- (former is the generator size, latter is the size argument with which to invoke other auxiliary producers/checkers)
    let initSizeParam ← `(Term.letIdBinder| ($initSizeIdent : $natIdent))
    let sizeParam ← `(Term.letIdBinder| ($sizeIdent : $natIdent))
    let matchExpr ← mkMatchExpr sizeIdent caseExprs

    -- Add parameters for each argument to the inductive relation
    -- (except the target variable, which we'll filter out later)
    let paramInfo ← analyzeInductiveArgs inductiveName inductiveLevels args

    -- Inner params are for the inner `aux_arb` / `aux_enum` function
    let mut innerParams := #[]
    innerParams := innerParams.push initSizeParam
    innerParams := innerParams.push sizeParam

    -- Outer params are for the top-level lambda function which invokes `aux_arb` / `aux_enum`
    let mut outerParams := #[]
    let mut outputType := none
    let mut typeParams := #[]
    for (paramName, paramType, paramTypeSyntax) in paramInfo do
      -- Only add a function parameter is the argument to the inductive relation is not the target variable
      -- (We skip the target variable since that's the value we wish to generate)
      if paramType.isSort then
        typeParams := typeParams.push paramName
      if paramName != targetVar then
        let outerParamIdent := mkIdent paramName
        outerParams := outerParams.push outerParamIdent

        let innerParamIdent := mkIdent paramName

        let innerParam ← if paramType.isSort then
          `(Term.letIdBinder| ($innerParamIdent : Sort _))
          else
          `(Term.letIdBinder| ($innerParamIdent : $paramTypeSyntax))

        innerParams := innerParams.push innerParam
      else
        outputType := some paramTypeSyntax

    -- Figure out which typeclass should be derived
    -- (`ArbitrarySizedSuchThat` for generators, `EnumSizedSuchThat` for enumerators)
    let producerTypeClass :=
      match producerSort with
      | .Generator => arbitrarySizedSuchThatTypeclass
      | .Enumerator => enumSizedSuchThatTypeclass

    -- Similarly, figure out the name of the function corresponding to the typeclass above
    let producerTypeClassFunction :=
      match producerSort with
      | .Generator => unqualifiedArbitrarySizedSTFn
      | .Enumerator => unqualifiedEnumSizedSTFn

    -- Generators use `aux_arb` as the inner function, enumerators use `aux_enum`
    let innerFunctionIdent :=
      match producerSort with
      | .Generator => mkFreshAccessibleIdent topLevelLocalCtx `aux_arb
      | .Enumerator => mkFreshAccessibleIdent topLevelLocalCtx `aux_enum

    -- Get the syntax for the target type, it must exist!
    assert! outputType != none
    let targetTypeSyntax := outputType.get!

    -- Determine the appropriate type of the final producer
    -- (either `Plausible.Gen α` or `ExceptT GenError Enum α`)
    let optionTProducerType ←
      match producerSort with
      | .Generator => `($genTypeConstructor $targetTypeSyntax)
      | .Enumerator => `($exceptTTypeConstructor $genErrorType $enumTypeConstructor $targetTypeSyntax)

    let producerUnconstrainedClass :=
      match producerSort with
      | .Generator => ``Plausible.Arbitrary
      | .Enumerator => ``Enum

    let arbitraryTypeParamInstances ← mkTypeClassInstanceBinders typeParams #[producerUnconstrainedClass, ``DecidableEq]

    -- Produce an instance of the appropriate typeclass containing the definition for the derived producer
    `(instance $arbitraryTypeParamInstances:bracketedBinder* : $producerTypeClass $targetTypeSyntax (fun $(mkIdent targetVar) => @$(mkIdent inductiveName) $args*) where
        $producerTypeClassFunction:ident :=
          let rec $innerFunctionIdent:ident $innerParams* $arbitraryTypeParamInstances:bracketedBinder* : $optionTProducerType :=
            $matchExpr
          fun $freshSizeIdent => $innerFunctionIdent $freshSizeIdent $freshSizeIdent $outerParams*)
