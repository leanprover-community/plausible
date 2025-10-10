import Plausible.Chamelean.UnificationMonad
import Plausible.Chamelean.Utils

open Lean

----------------------------------------------
-- Type definitions
----------------------------------------------

/-- A `HypothesisExpr` is a datatype representing a hypothesis for a
    constructor of an inductive relation, consisting of a constructor name
    applied to some list of arguments, each of which are `ConstructorExpr`s -/
abbrev HypothesisExpr := Name × List ConstructorExpr

/-- `ToExpr` instance for `HypothesisExpr`
    (for converting `HypothesisExpr`s to Lean `Expr`s) -/
instance : ToExpr HypothesisExpr where
  toExpr (hypExpr : HypothesisExpr) : Expr :=
    let (ctorName, ctorArgs) := hypExpr
    mkAppN (mkConst ctorName) (toExpr <$> ctorArgs.toArray)
  toTypeExpr := mkConst ``Expr

local instance [Ord α][Ord β]: Ord (α × β) := lexOrd

/-- A source is the thing we wish to check/generate/enumerate -/
inductive Source
  | NonRec : HypothesisExpr → Source
  | Rec : Name → List ConstructorExpr → Source
  deriving Repr, BEq, Ord

/-- Producers are either enumerators or generators -/
inductive ProducerSort
  | Enumerator
  | Generator
  deriving Repr, BEq, Ord

/-- The sort of function we are deriving based on an inductive relation:
    determines whether we are deriving a (constrained) generator, enumerator or a checker.

    Note: the `Theorem` constructor is used in the artifact of "Testing Theorems, Fully Automatically"
    for automatically testing whether a theorem holds (we replicate it here for completeness). -/
inductive DeriveSort
  | Generator
  | Enumerator
  | Checker
  | Theorem
  deriving Repr, BEq, Ord

/-- Determines if a `DeriveSort` corresponds to a producer
    (only generators & enumerators are considered producers) -/
def DeriveSort.isProducer : DeriveSort → Bool
  | .Generator | .Enumerator => true
  | .Checker | .Theorem => false

/-- The type of schedule we wish to derive -/
inductive ScheduleSort
  /-- tuple of produced outputs from conclusion of constructor -/
  | ProducerSchedule (producerSort : ProducerSort) (conclusion : List ConstructorExpr)

  /-- checkers need not bother with conclusion of constructor,
      only hypotheses need be checked and conclusion of constructor follows-/
  | CheckerSchedule

  /-- In a `TheoremSchedule`, we check the `conclusion` of the theorem, and take in a `Bool`
      which is true if we need to find a checker by identifying the `DecOpt` instance,
      and false otherwise (we're currently dealing with a function that returns `Option Bool`) -/
  | TheoremSchedule (conclusion : HypothesisExpr) (typeClassUsed : Bool)

  deriving Repr, Ord, BEq


/-- A single step in a generator schedule -/
inductive ScheduleStep
  /-- Unconstrained generation -/
  | Unconstrained : Name → Source → ProducerSort → ScheduleStep

  /-- Generate a value such that a predicate is satisfied -/
  | SuchThat : List (Name × Option ConstructorExpr) → Source → ProducerSort → ScheduleStep

  /-- Check whether some proposition holds
     (the bool is the desired truth value of the proposition we're checking) -/
  | Check : Source → Bool → ScheduleStep

  /-- Used when you decompose a constructor constrained arg into a
    fresh variable followed by a pattern match -/
  | Match : Name → Pattern → ScheduleStep

  deriving Repr, BEq, Ord

/-- Stringifier for `Source` -/
def sourceToString source := match source with
  | Source.Rec name ctrArgs => s!"{ToExpr.toExpr (name,ctrArgs)}"
  | Source.NonRec hyp => s!"{ToExpr.toExpr hyp}"

/-- Stringifier for `step` -/
def stepToString step := match step with
    | ScheduleStep.Unconstrained name src _ => s!"{name} ← {sourceToString src}"
    | .SuchThat vars src _ => s!"{vars.map (fun ((name : Name), (_ : Option ConstructorExpr)) => name)} ← {sourceToString src}"
    | .Check src true => s!"check {sourceToString src}"
    | .Check src false => s!"check ¬{sourceToString src}"
    | .Match name pattern => s!"match {name} with {repr pattern}"

/-- Stringifier for lists of steps. -/
def scheduleStepsToString (steps : List ScheduleStep) := "do\n  " ++ String.intercalate "\n  " (stepToString <$> steps)

/-- A schedule is a pair consisting of an ordered list of `ScheduleStep`s,
    and the sort of schedule we're dealing with (the latter is the "conclusion" of the schedule) -/
abbrev Schedule := List ScheduleStep × ScheduleSort

/-- Each `ScheduleStep` is associated with a `Density`, which represents a failure mode of a generator -/
inductive Density
  /-- Invokes a call to a checker -/
  | Checking

  /-- A call to `ArbitrarySuchThat`, followed by a pattern-match on the generated value
      (this happens when we want the output of the generator to have a certain shape) -/
  | Backtracking

  /-- a call to `ArbitrarySuchThat` ??? -/
  | Partial

  /-- Unconstrained generation, i.e. calls to `arbitrary` -/
  | Total
  deriving Repr, BEq

/-- Converts a `HypothesisExpr` to a `TSyntax term` -/
def hypothesisExprToTSyntaxTerm (hypExpr : HypothesisExpr) : MetaM (TSyntax `term) := do
  let (ctorName, ctorArgs) := hypExpr
  let ctorArgTerms ← ctorArgs.toArray.mapM constructorExprToTSyntaxTerm
  `($(mkIdent ctorName) $ctorArgTerms:term*)

/-- Converts an `Expr` to a `ConstructorExpr` -/
partial def exprToConstructorExpr (e : Expr) : MetaM ConstructorExpr := do
  match e with
  | .fvar id =>
    let localDecl ← FVarId.getDecl id
    return ConstructorExpr.Unknown localDecl.userName
  | .const name _ =>
    -- Check if this is a constructor
    let env ← getEnv
    if env.isConstructor name then
      return ConstructorExpr.Ctor name []
    else
      return ConstructorExpr.FuncApp name []
  | .app f arg => do
    let fExpr ← exprToConstructorExpr f
    let argExpr ← exprToConstructorExpr arg
    match fExpr with
    | ConstructorExpr.Ctor name args =>
      return ConstructorExpr.Ctor name (args ++ [argExpr])
    | ConstructorExpr.FuncApp name args =>
      return ConstructorExpr.FuncApp name (args ++ [argExpr])
    | ConstructorExpr.Unknown name =>
      throwError m!"exprToConstructorExpr: We do not support higher order application of {name} in Expr {e}"
  | _ =>
    -- For other expression types (literals, lambdas, etc.), generate a placeholder name
    throwError m!"exprToConstructorExpr can only handle free variables, constants, and applications. Attempted to convert: {e}"

/-- Converts an `Expr` to an `Option HypothesisExpr` -/
def exprToHypothesisExpr (e : Expr) : MetaM HypothesisExpr := do
  let e ← Meta.whnf e
  let (ctorName, args) := e.getAppFnArgs
  let env ← getEnv
  -- Only proceed if `ctorName` refers to a constructor or the name of an `inductive`
  if env.isConstructor ctorName || (← isInductive ctorName) then
    let constructorArgs ← args.mapM exprToConstructorExpr
    return (ctorName, constructorArgs.toList)
  else
    throwError m!"exprToHypothesisExpr: unable to convert {e} to a HypothesisExpr, \
                  must be a constructor or an inductive applied to arguments."

/-- Helper function called by `updateSource`, which updates variables in a hypothesis `hyp`
    with the result of unification (provided via the `UnifyM` monad) -/
def updateNonRecSource (k : UnknownMap) (hyp : HypothesisExpr) : UnifyM Source := do
  let (ctorName, args) := hyp
  let updatedArgs ← List.mapM (UnifyM.updateConstructorArg k) args
  return .NonRec (ctorName, updatedArgs)

/-- Updates a `Source` with the result of unification as contained in the `UnknownMap` -/
def updateSource (k : UnknownMap) (src : Source) : UnifyM Source := do
  match src with
  | .NonRec hyp => do
    let hypExpr := toExpr hyp

    -- To do so, we first extract the constructor in the hypothesis
    -- and see if it corresponds to a type constructor for a parameterized type `inductive` type (e.g. `List`)
    -- If yes, we can just return the source as is, since the source is just the name of a type
    let (ctor, _) := hypExpr.getAppFnArgs

    try (do
      -- Determine the return type of the constructor in the hypothesis
      let inductiveVal ← getConstInfoInduct ctor
      let ctorTy := inductiveVal.type
      let returnType ← Array.back! <$> getComponentsOfArrowType ctorTy
      -- If the return type is *not* `Prop`, then the `Source` is
      -- a generator for some inductive type (as opposed to an inductive `Prop`),
      -- so we don't need to update the source
      if (not returnType.isProp) then
        pure src
      else
        updateNonRecSource k hyp)
    catch _ =>
      -- `ctor` is not an inductive type (calling Lean's `getConstInfoInduct` function raised an exception)
      -- This means we have a hypothesis which is *not* an application of some inductive type/proposition,
      -- i.e. we can just update the variables in the `hyp` w/ the result of unification
      updateNonRecSource k hyp

  | .Rec r tys => do
    let updatedTys ← List.mapM (UnifyM.updateConstructorArg k) tys
    return .Rec r updatedTys

/-- Updates a list of `ScheduleSteps` with the result of unification -/
def updateScheduleSteps (scheduleSteps : List ScheduleStep) : UnifyM (List ScheduleStep) := do
  UnifyM.withConstraints $ fun k => scheduleSteps.mapM (fun step =>
    match step with
    | .Match u p => do
      let updatedScrutinee ← UnifyM.findCanonicalUnknown k u
      let updatedPattern ← UnifyM.updatePattern k p
      return .Match updatedScrutinee updatedPattern
    | .Unconstrained u src producerSort => do
      let updatedUnknown ← UnifyM.findCanonicalUnknown k u
      let updatedSrc ← updateSource k src
      return .Unconstrained updatedUnknown updatedSrc producerSort
    | .SuchThat unknownsAndTypes src dst => do
      let updatedUnknownsAndTypes ← unknownsAndTypes.mapM (fun (u, ty) => do
        let u' ← UnifyM.findCanonicalUnknown k u
        return (u', ty))
      let updatedSource ← updateSource k src
      return .SuchThat updatedUnknownsAndTypes updatedSource dst
    | .Check src polarity => do
      let updatedSrc ← updateSource k src
      return .Check updatedSrc polarity)

/-- Takes the `patterns` and `equalities` fields from `UnifyState` (which are created after
    the conclusion of a constructor has been unified with the top-level arguments to the inductive relation),
    converts them to the appropriate `ScheduleStep`s, and prepends them to the `currentSchedule`.

    - The intuition for prepending these newly-created steps to the existing schedule is that we want to
      make sure all the equalities & pattern-matches needed for the conclusion hold before
      processing the rest of the schedule. -/
def addConclusionPatternsAndEqualitiesToSchedule (patterns : List (Unknown × Pattern)) (equalities : Std.HashSet (Unknown × Unknown)) (currentSchedule : Schedule) : Schedule :=
  let (existingScheduleSteps, scheduleSort) := currentSchedule
  let matchSteps := (Function.uncurry ScheduleStep.Match) <$> patterns
  let equalityCheckSteps := (fun (u1, u2) => ScheduleStep.Check (Source.NonRec (`BEq.beq, [.Unknown u1, .Unknown u2])) true) <$> equalities.toList
  (matchSteps ++ equalityCheckSteps ++ existingScheduleSteps, scheduleSort)
