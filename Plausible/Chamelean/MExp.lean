/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
import Plausible.Arbitrary
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.TSyntaxCombinators
import Batteries.Lean.Expr
import Plausible.Chamelean.Schedules
import Plausible.Chamelean.UnificationMonad
import Plausible.Chamelean.Idents
import Plausible.Chamelean.Utils

namespace MExp

open Plausible
open Idents Schedules
open Lean Parser Elab Term Command ToExpr TSyntax

-- Adapted from QuickChick source code
-- https://github.com/QuickChick/QuickChick/blob/internal-rewrite/plugin/newGenericLib.ml

/-- The sort of monad we are compiling to, i.e. one of the following:
    - An unconstrained / constrained generator (`Gen`)
    - An unconstrained / constrained enumerator (`Enumerator` / `Except GenError Enumerator`)
    - A Checker (`Except GenError Bool` monad) -/
inductive MonadSort
  | Gen
  | Enumerator
  | OptionTEnumerator
  | Checker
  deriving Repr, BEq

/-- Determines whether a `MonadSort` corresponds to a monad
    for an enumerator (i.e. `Enumerator` or `OptionT Enumerator`) -/
def MonadSort.isEnumerator : MonadSort → Bool
  | .Enumerator | .OptionTEnumerator => true
  | _ => false

/-- An intermediate representation of monadic expressions that are
    used in generators/enumerators/checkers.
    - Schedules are compiled to `MExp`s, which are then compiled to Lean code
    - Note: `MExp`s make it easy to optimize generator code down the line
      (e.g. combine pattern-matches when we have disjoint patterns
    - The cool thing about `MExp` is that we can interpret it differently
      based on the `MonadSort` -/
inductive MExp : Type where
  /-- `MRet e` represents `return e` in some monad -/
  | MRet (e : MExp)

  /-- `MBind monadSort m1 vars m2` represents `m1 >>= fun vars => m2` in a particular monad,
       as determined by `monadSort` -/
  | MBind (monadSort : MonadSort) (m1 : MExp) (vars : List (Name × Option Expr)) (m2 : MExp)

  /-- N-ary function application -/
  | MApp (explicit : Explicit) (f : MExp) (args : List MExp)

  /-- N-ary constructor application -/
  | MCtr (explicit : Explicit) (c : Name) (args : List MExp)

  /-- Some constant name (e.g. refers to functions) -/
  | MConst (name : Name)

  /-- `MMatch scrutinee [(p1, e1), …, (pn, en)]` represents
       ```lean
       match scrutinee with
       | p1 => e1
       ...
       | pn => en
       ```
  -/
  | MMatch (explicit : Explicit) (scrutinee : MExp) (cases : List (Pattern × MExp))

  /-- Refers to a variable identifier -/
  | MId (name : Name)

  /-- A function abstraction, where `args` is a list of variable names,
      and `body` is an `MExp` representing the function body -/
  | MFun (args : List (Name × Option Expr)) (body : MExp)

  /-- A natural number or string literal. -/
  | MLit (l : Literal)

  /-- Signifies failure (corresponds to the term `OptionT.fail`) -/
  | MFail

  /-- Signifies running out of fuel -/
  | MOutOfFuel

  | MHole
  | MSort (lvl : Level)

  deriving Repr, Inhabited, BEq


/-- Converts a `ProducerSort` to a `MonadSort`
    representing an unconstrained producer (i.e. `Gen` or `Enumerator`) -/
def prodSortToMonadSort (prodSort : ProducerSort) : MonadSort :=
  match prodSort with
  | .Enumerator => MonadSort.Enumerator
  | .Generator => MonadSort.Gen

/-- Converts a `ProducerSort` to a `MonadSort`
    representing a *constrained* producer
    (i.e. `OptionT Gen` or `OptionT Enumerator`) -/
def prodSortToOptionTMonadSort (prodSort : ProducerSort) : MonadSort :=
  match prodSort with
  | .Enumerator => MonadSort.OptionTEnumerator
  | .Generator => MonadSort.Gen

/-- `MExp` representation of `EnumSizedSuchThat.enumSizedST`,
    where `prop` is the `Prop` constraining the value being enumerated
    and `fuel` is an `MExp` representing the fuel argument to the enumerator -/
def enumSizedST (prop : MExp) (fuel : MExp) : MExp :=
  .MApp .allExplicit (.MConst ``EnumSizedSuchThat.enumSizedST) [.MHole, prop, .MHole, fuel]

/-- `MExp` representation of `ArbitrarySizedSuchThat.arbitrarySizedST`,
    where `prop` is the `Prop` constraining the value being generated
    and `fuel` is an `MExp` representing the fuel argument to the generator -/
def arbitrarySizedST (prop : MExp) (fuel : MExp) : MExp :=
  .MApp .allExplicit (.MConst ``ArbitrarySizedSuchThat.arbitrarySizedST) [.MHole, prop, .MHole, fuel]

/-- `ok x` is an `MExp` representing `Except.ok x`. -/
def ok (x : MExp) : MExp :=
  .MApp .allowImplicit (.MConst ``Except.ok) [x]

/-- `okTrue` is an `MExp` representing `ok true`
    - This expression is often used when deriving checkers, so we define it here as an abbreviation. -/
def okTrue : MExp :=
  ok (.MConst ``true)

/-- `okFalse` is an `MExp` representing `ok false`
    - This expression is often used when deriving checkers, so we define it here as an abbreviation. -/
def okFalse : MExp :=
  ok (.MConst ``false)


/-- Converts a `List α` to a "tuple", where the function `pair`
    is used to create tuples. The `default` element is used when
    the input list `l` is empty, although for most use-cases,
    this function will be called with non-empty lists `l`, so `default`
    will be `none`. -/
def tupleOfList [Inhabited α] (pair : α → α → α) (l : List α) (default : Option α) : α :=
  match l with
  | [] => default.get!
  | [x] => x
  | x :: xs => List.foldl pair x xs

/-- Converts a list of `Pattern`s to a one single `Pattern` expressed
    as a tuple -/
def patternTupleOfList (xs : List Pattern) : Pattern :=
  tupleOfList (fun x y => Pattern.CtorPattern ``Prod.mk [x, y]) xs none

/-- Compiles a `Pattern` to a `TSyntax term` -/
partial def compilePattern (explicit : Explicit) (p : Pattern) : MetaM (TSyntax `term) :=
  match p with
  | .UnknownPattern u => `($(mkIdent u):ident)
  | .CtorPattern ctorName args => do
    let compiledArgs ← args.toArray.mapM <| compilePattern explicit
    match explicit with
    | .allExplicit =>
    `(@$(mkIdent ctorName):ident $compiledArgs*)
    | .allowImplicit =>
    `($(mkIdent ctorName):ident $compiledArgs*)
  | .LitPattern l => mkLiteral l


/-- `MExp` representation of a `DecOpt` instance (a checker).
    Specifically, `decOptChecker prop fuel` represents the term
    `DecOpt.decOpt $prop $fuel`. -/
def decOptChecker (prop : MExp) (fuel : MExp) : MExp :=
  .MApp .allExplicit (.MConst ``DecOpt.decOpt) [prop, .MHole, fuel]

/-- Converts a `ConstructorExpr` to an `MExp` -/
partial def constructorExprToMExp (exp : Explicit) (expr : ConstructorExpr) : MExp :=
  match expr with
  | .Unknown u => .MId u
  | .Ctor c args | .TyCtor c args => .MCtr exp c (constructorExprToMExp exp <$> args)
  | .FuncApp f args => .MApp exp (.MId f) (constructorExprToMExp exp <$> args)
  | .Lit l => .MLit l
  | .CSort lvl => .MSort lvl

partial def mexpToConstructorExpr (m : MExp) : Option ConstructorExpr :=
  match m with
  | .MId u => return .Unknown u
  | .MCtr _explicit c args => do
    let convertedArgs ← args.mapM mexpToConstructorExpr
    return .Ctor c convertedArgs
  | .MApp _explicit (.MId f) args => do
    let convertedArgs ← args.mapM mexpToConstructorExpr
    return .FuncApp f convertedArgs
  | .MLit l => return .Lit l
  | .MSort lvl => return .CSort lvl
  | _ => none

/-- `MExp` representation of a recursive function call,
    where `f` is the function name and `args` are the arguments
    (each represented as a `ConstructorExpr`) -/
def recCall (f : Name) (args : List ConstructorExpr) : MExp :=
  .MApp .allowImplicit (.MId f) $
    [.MId `initSize, .MId `size'] ++ (constructorExprToMExp .allExplicit <$> args)

/-- Converts a `HypothesisExpr` to an `MExp` -/
def hypothesisExprToMExp (hypExpr : HypothesisExpr) : MExp :=
  let (ctorName, ctorArgs) := hypExpr
  .MCtr .allExplicit ctorName (constructorExprToMExp .allExplicit <$> ctorArgs)

def hypothesisMExpToExpr (m : MExp) : Option Expr := do
  let .MCtr .allExplicit ctorName args := m | none
  let cargs ← args.mapM mexpToConstructorExpr
  return constructorExprToExpr ((.Ctor ctorName cargs))

/-- `Pattern` that represents a wildcard (i.e. `_` on the LHS of a pattern-match) -/
def wildCardPattern : Pattern :=
  .UnknownPattern `_

/-- `MExp` representing a pattern-match on a `scrutinee` of type `Except _ Bool`.
     Specifically, `matchOptionBool scrutinee trueBranch falseBranch` represents
     ```lean
     match scrutinee with
     | .ok true => $trueBranch
     | .ok false => $falseBranch
     | .error _ => $MExp.MOutOfFuel
     ```
-/
def matchExceptBool (scrutinee : MExp) (trueBranch : MExp) (falseBranch : MExp) : MExp :=
  .MMatch .allowImplicit scrutinee
    [
      (.CtorPattern ``Except.ok [.UnknownPattern ``true], trueBranch),
      (.CtorPattern ``Except.ok [.UnknownPattern ``false], falseBranch),
      (.CtorPattern ``Except.error [wildCardPattern], .MOutOfFuel)
    ]

/-- `CompileScheduleM` is a monad for compiling `Schedule`s to `TSyntax term`s.
    Under the hood, this is just a `State` monad stacked on top of `TermElabM`,
    where the state is an `Array` of `TSyntax term`s, representing any auxiliary typeclass
    instances that need to derived beforehand.  -/
abbrev CompileScheduleM (α : Type) := StateT (TSyntaxArray `term) TermElabM α

/-- `MExp` representation of an unconstrained producer,
    parameterized by a `producerSort` and the type `ty` (represented as a `TSyntax term`)
    of the value being generated -/
def unconstrainedProducer (prodSort : ProducerSort) (ty : TSyntax `term) : CompileScheduleM MExp := do
  let typeClassName :=
    match prodSort with
    | .Enumerator => ``Enum
    | .Generator => ``Arbitrary
  let typeClassInstance ← `( $(Lean.mkIdent typeClassName) $ty:term )

  -- Add the `typeClassInstance` for the unconstrained producer to the state,
  -- then obtain the `MExp` representing the unconstrained producer
  StateT.modifyGet $ fun instances =>
    let producerMExp :=
      match prodSort with
      | .Enumerator => .MConst ``Enum.enum
      | .Generator => .MConst ``Arbitrary.arbitrary
    (producerMExp, instances.push typeClassInstance)

mutual

  partial def delabMexpAsExpr (mexp : MExp) : CompileScheduleM (TSyntax `term) := do
    let a ← (pure <$> hypothesisMExpToExpr mexp).getD (throwError "hypothesis mexp fails to turn to expr")
    let lctx ← getLCtx
    delabExprInLocalContext lctx a

  /-- Compiles a `MExp` to a Lean `doElem`, according to the `DeriveSort` provided -/
  partial def mexpToTSyntax (mexp : MExp) (deriveSort : DeriveSort) : CompileScheduleM (TSyntax `term) :=
    match mexp with
    | .MSort _ => `(Sort _)
    | .MHole => `(_)
    | .MId v | .MConst v => `($(mkIdent v))
    | .MApp explicit func args => do
      let f ← mexpToTSyntax func deriveSort
      let compiledArgs ← args.toArray.mapM (fun e => mexpToTSyntax e deriveSort)
      match explicit with
      | .allowImplicit => `($f $compiledArgs*)
      | .allExplicit => `(@$f $compiledArgs*)
    | .MCtr explicit ctorName args => do
      let compiledArgs ← args.toArray.mapM (fun e => mexpToTSyntax e deriveSort)
      match explicit with
      | .allowImplicit => `($(mkIdent ctorName) $compiledArgs*)
      | .allExplicit => `(@$(mkIdent ctorName) $compiledArgs*)
    | .MFun vars body => do
      let compiledBody ← mexpToTSyntax body deriveSort
      match vars with
      | [] => throwError "empty list of function arguments supplied to MFun"
        -- When we have multiple args, create a tuple containing all of them
        -- in the argument of the lambda
      | _ =>  do
        let args ← mkTuple vars
        `((fun $args:term => $compiledBody))
    | .MFail | .MOutOfFuel =>
      -- Note: right now we compile `MFail` and `MOutOfFuel` to the same Lean terms
      -- for simplicity, but in the future we may want to distinguish them
      match deriveSort with
      | .Generator | .Enumerator => `($failFn $genericFailure)
      | .Checker => `($(mkIdent ``Except.ok) $(mkIdent ``false))
      | .Theorem => throwError "compiling MExps for Theorem DeriveSorts not implemented"
    | .MRet e => do
      let e' ← mexpToTSyntax e deriveSort
      `(return $e')
    | .MBind monadSort m vars k => do
      -- Compile the monadic expression `m` and the continuation `k` to `TSyntax term`s
      let m1 ← mexpToTSyntax m deriveSort
      let k1 ← mexpToTSyntax k deriveSort
      match deriveSort, monadSort with
      | .Generator, .Gen
      | .Enumerator, .Enumerator
      | .Enumerator, .OptionTEnumerator =>
        -- If there are multiple variables that are bound to the result
        -- of the monadic expression `m`, convert them to a tuple
        let compiledArgs ←
          if vars.isEmpty then
            throwError m!"empty list of vars supplied to MBind, deriveSort = {repr deriveSort}, monadSort = {repr monadSort}, m1 = {m1}, k1 = {k1}"
          else
            mkTuple vars
        -- If we have a producer, we can just produce a monadic bind
        `(do let $compiledArgs:term ← $m1:term ; $k1:term)
      | .Generator, .Checker
      | .Enumerator, .Checker => do
        -- If a producer invokes a checker, we have to invoke the checker
        -- provided by the `DecOpt` instance for the proposition, then pattern
        -- match on its result
        let trueCase ← `(Term.matchAltExpr| | $(mkIdent ``Except.ok) $(mkIdent ``true) => $k1)
        let wildCardCase ← `(Term.matchAltExpr| | _ => $failFn $genericFailure)
        let cases := #[trueCase, wildCardCase]
        `(match $m1:term with $cases:matchAlt*)
      | .Checker, .Checker =>
        -- If the continuation of the bind is just returning `some True`,
        -- we can just inline the checker call `m1` to avoid the extra indirection
        -- of calling checker combinator functions
        if k == okTrue then
          `($m1:term)
        else
          -- For checkers, we can just invoke `DecOpt.andOptList`
          `($andOptListFn [$m1:term, $k1:term])
      | .Checker, .Enumerator
      | .Checker, .OptionTEnumerator => do
          -- If there are multiple variables that are bound to the result
          -- of the enumerator `m`, convert them to a tuple
          let args ←
            if vars.isEmpty then
              throwError m!"empty list of vars supplied to MBind, deriveSort = {repr deriveSort}, monadSort = {repr monadSort}, m1 = {m1}, k1 = {k1}"
            else
              mkTuple vars
          let fuelForEnumerator ← `($initSizeIdent:term)
          match monadSort with
          | .Enumerator =>
            -- If a checker invokes an unconstrained enumerator,
            -- we call `EnumeratorCombinators.enumerating` a la QuickChick
            `($enumeratingFn $m1:term (fun $args:term => $k1:term) $fuelForEnumerator:term)
          | .OptionTEnumerator =>
            -- If a checker invokes a contrained enumerator,
            -- we call `EnumeratorCombinators.enumeratingOpt` a la QuickChick
            `($enumeratingOptFn $m1:term (fun $args:term => $k1:term) $fuelForEnumerator:term)
          | .(_) => throwError "Unreachable pattern match: Checkers can only invoke enumerators in this branch"
      | .Theorem, _ => throwError "Theorem DeriveSort not implemented yet"
      | _, _ => throwError m!"Invalid monadic bind for deriveSort {repr deriveSort}"
    | .MMatch explicit scrutinee cases => do
      -- Compile the scrutinee, the LHS & RHS of each case separately
      let compiledScrutinee ← mexpToTSyntax scrutinee deriveSort
      let compiledCases ← cases.toArray.mapM (fun (pattern, rhs) => do
        let lhs ← compilePattern explicit pattern
        let compiledRHS ← mexpToTSyntax rhs deriveSort
        `(Term.matchAltExpr| | $lhs:term => $compiledRHS))
      `(match $compiledScrutinee:term with $compiledCases:matchAlt*)
    | .MLit l => mkLiteral l

  /-- `MExp` representation of a constrained producer,
      parameterized by a `producerSort`, a list of variable names & their types `varsTys`,
      and a `Prop` (`prop`) constraining the values being produced

      - Note: this function corresponds to `such_that_producer`
        in the QuickChick code -/
  partial def constrainedProducer (prodSort : ProducerSort) (varsTys : List (Name × Option ConstructorExpr)) (prop : MExp) (fuel : MExp) : CompileScheduleM MExp :=
    if varsTys.isEmpty then
      panic! "Received empty list of variables for constrainedProducer"
    else do
      -- Determine whether the typeclass instance for the constrained generator already exists
      -- i.e. check if an instance for `ArbitrarySizedSuchThat` / `EnumSizedSuchThat` with the
      -- specified `argTys` and `prop` already exists
      let (args, argTys) := List.unzip varsTys
      let argTyExprs := argTys.map (Option.map ToExpr.toExpr)
      let typedArgs := List.zip args argTyExprs
      let argsTuple ← mkTuple typedArgs
      let propBody ← delabMexpAsExpr prop
      let typeClassName :=
        match prodSort with
        | .Enumerator => ``EnumSizedSuchThat
        | .Generator => ``ArbitrarySizedSuchThat
      let typeClassInstance ← `($(mkIdent typeClassName) `_ (fun $argsTuple:term => $propBody))

      -- Add the `typeClassInstance` for the constrained producer to the state,
      -- then obtain the `MExp` representing the constrained producer
      StateT.modifyGet $ fun instances =>
        let producerWithArgs := MExp.MFun typedArgs prop
        let producerMExp :=
          match prodSort with
          | .Enumerator => enumSizedST producerWithArgs fuel
          | .Generator => arbitrarySizedST producerWithArgs fuel
        (producerMExp, instances.push typeClassInstance)

end

private def nameAndConstructorExprToTypedVar (v : Name × Option ConstructorExpr) : Name × Option Expr :=
  Prod.map id (ToExpr.toExpr <$> ·) v

/-- Compiles a `ScheduleStep` to an `MExp`.
     Note that `MExp` that is returned by this function is represented
     as a function `MExp → MExp`, akin to difference lists in Haskell
     (see https://www.seas.upenn.edu/~cis5520/22fa/lectures/stub/03-trees/DList.html)

    The arguments to this function are:
    - The current step of the schedule (`step`)
    - The function parameter `k` represents the remainder of the `mexp`
      (the rest of the monadic `do`-block)
    - `mfuel` and `defFuel` are `MExp`s representing the current size and the initial size
      supplied to the generator/enumerator/checker we're deriving
-/

def scheduleStepToMExp (step : ScheduleStep) (defFuel : MExp) (k : MExp) (outputType : Expr) : CompileScheduleM MExp :=
  match step with
  | .Unconstrained v src prodSort => do
    let monadSort := prodSortToMonadSort prodSort
    match src with
    | Source.NonRec hyp => do
      let ty ← hypothesisExprToTSyntaxTerm hyp
      let tyExpr := ToExpr.toExpr hyp
      let producer ← unconstrainedProducer prodSort ty
      pure $ .MBind monadSort producer [⟨v,tyExpr⟩] k
    | Source.Rec f args =>
      pure $ .MBind monadSort (recCall f args) [⟨v, outputType⟩] k

  | .SuchThat varsTys prod ps => do
    let monadSort := prodSortToOptionTMonadSort ps
    let typedVars := List.map (nameAndConstructorExprToTypedVar) varsTys
    match prod with
    | Source.NonRec hypExpr => do
      let producer ← constrainedProducer ps varsTys (hypothesisExprToMExp hypExpr) defFuel
      pure $ .MBind monadSort producer typedVars k
    | Source.Rec f args =>
      pure $ .MBind monadSort (recCall f args) typedVars k
  | .Check src _ =>

    -- TODO: double check if we need to pattern-match on `scheduleSort` here
    let checker :=
      match src with
      | Source.NonRec hypExpr =>
        decOptChecker (hypothesisExprToMExp hypExpr) defFuel
      | Source.Rec f args =>
        recCall f args

    -- TODO: handle checking hypotheses w/ negative polarity (currently not handled)

    -- TODO: double check if this is right
    pure $ .MBind .Checker checker [] k
  | .Match explicit scrutinee pattern =>
    pure $ .MMatch explicit (.MId scrutinee) [(pattern, k), (wildCardPattern, .MFail)]

/-- Converts a `Schedule` (a list of `ScheduleStep`s along with a `ScheduleSort`,
    which acts as the conclusion of the schedule) to an `MExp`.
    - `mfuel` and `defFuel` are auxiliary `MExp`s representing the fuel
      for the function we are deriving (these correspond to `size` and `initSize`
      in the QuickChick code for the derived functions) -/
def scheduleToMExp (schedule : Schedule) (mfuel : MExp) (defFuel : MExp) (recType : Expr) : CompileScheduleM MExp :=
  let (scheduleSteps, scheduleSort) := schedule
  -- Determine the *epilogue* of the schedule (i.e. what happens after we
  -- have finished executing all the `scheduleStep`s)
  let epilogue :=
    match scheduleSort with
    | .ProducerSchedule _ conclusionOutputs =>
      -- Convert all the outputs in the conclusion to `mexp`s
      let conclusionMExps := constructorExprToMExp .allowImplicit <$> conclusionOutputs
      -- If there are multiple outputs, wrap them in a tuple
      match conclusionMExps with
      | [] => panic! "No outputs being returned in producer schedule"
      | [output] => MExp.MRet output
      | outputs => tupleOfList (fun e1 e2 => .MApp .allowImplicit (.MConst ``Prod.mk) [e1, e2]) outputs outputs[0]?
    | .CheckerSchedule => okTrue
    | .TheoremSchedule conclusion typeClassUsed =>
      -- Create a pattern-match on the result of hte checker
      -- on the conclusion, returning `.ok true` or `.ok false` accordingly
      let conclusionMExp := hypothesisExprToMExp conclusion
      let scrutinee :=
        if typeClassUsed then decOptChecker conclusionMExp mfuel
        else conclusionMExp
      matchExceptBool scrutinee okTrue okFalse
  -- Fold over the `scheduleSteps` and convert each of them to a functional `MExp`
  -- Note that the fold composes the `MExp`, and we use `foldr` since
  -- we want the `epilogue` to be the base-case of the fold
  List.foldrM (fun step acc => scheduleStepToMExp step defFuel acc recType)
    epilogue scheduleSteps
