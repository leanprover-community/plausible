import Lean
import Std
import Plausible.Gen
import Plausible.Chamelean.TSyntaxCombinators
import Plausible.Chamelean.OptionTGen
import Plausible.Chamelean.Idents
import Plausible.Chamelean.Utils
import Plausible.Chamelean.Schedules


open Lean Elab Command Meta Term Parser Std
open Idents

/-- Extracts the name of the induction relation and its arguments -/
def parseInductiveApp (body : Term) : CommandElabM (TSyntax `ident × TSyntaxArray `ident) := do
  match body with
  | `($indRel:ident $args:ident*) => do
    return (indRel, args)
  | `($indRel:ident) => do
    return (indRel, #[])
  | _ => throwErrorAt body "Expected inductive type application"

/-- Analyzes the type of the inductive relation and matches each
    argument with its expected type, returning an array of
    (parameter name, type expression) pairs -/
def analyzeInductiveArgs (inductiveName : Name) (args : Array Term) :
  CommandElabM (Array (Name × TSyntax `term)) := do

  -- Extract the no. of parameters & indices for the inductive
  let inductInfo ← getConstInfoInduct inductiveName
  let numParams := inductInfo.numParams
  let numIndices := inductInfo.numIndices
  let numArgs := numParams + numIndices

  if args.size != numArgs then
    throwError s!"Expected {numArgs} arguments but received {args.size} arguments instead"

  -- Extract the type of the inductive relation
  let inductType := inductInfo.type

  liftTermElabM $
    forallTelescope inductType (fun xs _ => do
      let mut paramInfo : Array (Name × TSyntax `term) := #[]

      for i in [:args.size] do
        -- Match each argument with its expected type
        let arg := args[i]!
        let paramFVar := xs[i]!
        let paramType ← inferType paramFVar

        -- Extract parameter name from the argument syntax
        let paramName ← extractParamName arg

        -- Use Lean's delaborator to express the parameter type
        -- using concrete surface-level syntax
        let typeSyntax ← PrettyPrinter.delab paramType

        paramInfo := paramInfo.push (paramName, typeSyntax)

      pure paramInfo)

/-- Finds the index of the argument in the inductive application for the value we wish to generate
    (i.e. finds `i` s.t. `args[i] == targetVar`) -/
def findTargetVarIndex (targetVar : Name) (args : TSyntaxArray `term) : Option Nat :=
  Array.findIdx? (fun arg => arg.getId == targetVar) (TSyntaxArray.raw args)

/-- Produces an instance of the `ArbitrarySizedSuchThat` / `EnumSizedSuchThat` typeclass containing the definition for a constrained generator.
    The arguments to this function are:
    - a list of `baseGenerators` (each represented as a Lean term), to be invoked when `size == 0`
    - a list of `inductiveGenerators`, to be invoked when `size > 0`
    - the name of the inductive relation (`inductiveStx`)
    - the arguments (`args`) to the inductive relation
    - the name and type for the value we wish to generate (`targetVar`, `targetTypeSyntax`)
    - the `producerType`, which determines what typeclass is to be produced
      + If `producerType = .Generator`, an `ArbitrarySizedSuchThat` instance is produced
      + If `producerType = .Enumerator`, an `EnumSizedSuchThat` instance is produced
    - The `LocalContext` associated with the top-level inductive relation (`topLevelLocalCtx`) -/
def mkConstrainedProducerTypeClassInstance
  (baseGenerators : TSyntax `term)
  (inductiveGenerators : TSyntax `term)
  (inductiveStx : TSyntax `term)
  (args : TSyntaxArray `term) (targetVar : Name)
  (targetTypeSyntax : TSyntax `term)
  (producerSort : ProducerSort)
  (topLevelLocalCtx : LocalContext) : CommandElabM (TSyntax `command) := do
    -- Produce a fresh name for the `size` argument for the lambda
    -- at the end of the generator function, as well as the `aux_arb` inner helper function
    let freshSizeIdent := mkFreshAccessibleIdent topLevelLocalCtx `size
    let freshSize' := mkFreshAccessibleIdent topLevelLocalCtx `size'

    let inductiveName := inductiveStx.raw.getId

    -- The (backtracking) combinator to be invoked
    -- (`OptionTGen.backtrack` for generators, `EnumeratorCombinators.enumerate` for enumerators)
    let combinatorFn :=
      match producerSort with
      | .Generator => OptionTBacktrackFn
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
    let matchExpr ← liftTermElabM $ mkMatchExpr sizeIdent caseExprs

    -- Add parameters for each argument to the inductive relation
    -- (except the target variable, which we'll filter out later)
    let paramInfo ← analyzeInductiveArgs inductiveName args

    -- Inner params are for the inner `aux_arb` / `aux_enum` function
    let mut innerParams := #[]
    innerParams := innerParams.push initSizeParam
    innerParams := innerParams.push sizeParam

    -- Outer params are for the top-level lambda function which invokes `aux_arb` / `aux_enum`
    let mut outerParams := #[]
    for (paramName, paramType) in paramInfo do
      -- Only add a function parameter is the argument to the inductive relation is not the target variable
      -- (We skip the target variable since that's the value we wish to generate)
      if paramName != targetVar then
        let outerParamIdent := mkIdent paramName
        outerParams := outerParams.push outerParamIdent

        let innerParamIdent := mkIdent paramName

        let innerParam ← `(Term.letIdBinder| ($innerParamIdent : $paramType))
        innerParams := innerParams.push innerParam

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

    -- Determine the appropriate type constructor to use as the producer's type
    -- (either `Gen` or `Enumerator`)
    let producerTypeConstructor :=
      match producerSort with
      | .Generator => genTypeConstructor
      | .Enumerator => enumTypeConstructor

    -- Determine the appropriate type of the final producer
    -- (either `OptionT Plausible.Gen α` or `OptionT Enum α`)
    let optionTProducerType ← `($optionTTypeConstructor $producerTypeConstructor $targetTypeSyntax)

    -- Produce an instance of the appropriate typeclass containing the definition for the derived producer
    `(instance : $producerTypeClass $targetTypeSyntax (fun $(mkIdent targetVar) => $inductiveStx $args*) where
        $producerTypeClassFunction:ident :=
          let rec $innerFunctionIdent:ident $innerParams* : $optionTProducerType :=
            $matchExpr
          fun $freshSizeIdent => $innerFunctionIdent $freshSizeIdent $freshSizeIdent $outerParams*)
