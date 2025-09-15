import Plausible.Arbitrary
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.TSyntaxCombinators
import Plausible.Chamelean.Schedules
import Plausible.Chamelean.UnificationMonad
import Plausible.Chamelean.Idents

open Plausible
open Idents
open Lean Parser Elab Term Command

-- Adapted from QuickChick source code
-- https://github.com/QuickChick/QuickChick/blob/internal-rewrite/plugin/newGenericLib.ml

/-- The sort of monad we are compiling to, i.e. one of the following:
    - An unconstrained / constrained generator (`Gen` / `OptionT Gen`)
    - An unconstrained / constrained enumerator (`Enumerator` / `OptionT Enumerator`)
    - A Checker (`Option Bool` monad) -/
inductive MonadSort
  | Gen
  | OptionTGen
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
  | MBind (monadSort : MonadSort) (m1 : MExp) (vars : List Unknown) (m2 : MExp)

  /-- N-ary function application -/
  | MApp (f : MExp) (args : List MExp)

  /-- N-ary constructor application -/
  | MCtr (c : Name) (args : List MExp)

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
  | MMatch (scrutinee : MExp) (cases : List (Pattern × MExp))

  /-- Refers to a variable identifier -/
  | MId (name : Name)

  /-- A function abstraction, where `args` is a list of variable names,
      and `body` is an `MExp` representing the function body -/
  | MFun (args : List Name) (body : MExp)

  /-- Signifies failure (corresponds to the term `OptionT.fail`) -/
  | MFail

  /-- Signifies running out of fuel -/
  | MOutOfFuel

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
  | .Generator => MonadSort.OptionTGen

/-- `MExp` representation of `EnumSizedSuchThat.enumSizedST`,
    where `prop` is the `Prop` constraining the value being enumerated
    and `fuel` is an `MExp` representing the fuel argument to the enumerator -/
def enumSizedST (prop : MExp) (fuel : MExp) : MExp :=
  .MApp (.MConst ``EnumSizedSuchThat.enumSizedST) [prop, fuel]

/-- `MExp` representation of `ArbitrarySizedSuchThat.arbitrarySizedST`,
    where `prop` is the `Prop` constraining the value being generated
    and `fuel` is an `MExp` representing the fuel argument to the generator -/
def arbitrarySizedST (prop : MExp) (fuel : MExp) : MExp :=
  .MApp (.MConst ``ArbitrarySizedSuchThat.arbitrarySizedST) [prop, fuel]

/-- `mexpSome x` is an `MExp` representing `Option.some x`.
    We call this function `mexpSome` to avoid name clashes with the existing `some` constructor
    for `Option` types. -/
def mexpSome (x : MExp) : MExp :=
  .MApp (.MConst ``Option.some) [x]

/-- `someTrue` is an `MExp` representing `some true`
    - This expression is often used when deriving checkers, so we define it here as an abbreviation. -/
def someTrue : MExp :=
  mexpSome (.MConst ``true)

/-- `someFalse` is an `MExp` representing `some false`
    - This expression is often used when deriving checkers, so we define it here as an abbreviation. -/
def someFalse : MExp :=
  mexpSome (.MConst ``false)


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
partial def compilePattern (p : Pattern) : MetaM (TSyntax `term) :=
  match p with
  | .UnknownPattern u => `($(mkIdent u):ident)
  | .CtorPattern ctorName args => do
    let compiledArgs ← args.toArray.mapM compilePattern
    `($(mkIdent ctorName):ident $compiledArgs*)



/-- `MExp` representation of a `DecOpt` instance (a checker).
    Specifically, `decOptChecker prop fuel` represents the term
    `DecOpt.decOpt $prop $fuel`. -/
def decOptChecker (prop : MExp) (fuel : MExp) : MExp :=
  .MApp (.MConst ``DecOpt.decOpt) [prop, fuel]

/-- Converts a `ConstructorExpr` to an `MExp` -/
partial def constructorExprToMExp (expr : ConstructorExpr) : MExp :=
  match expr with
  | .Unknown u => .MId u
  | .Ctor c args => .MCtr c (constructorExprToMExp <$> args)


/-- `MExp` representation of a recursive function call,
    where `f` is the function name and `args` are the arguments
    (each represented as a `ConstructorExpr`) -/
def recCall (f : Name) (args : List ConstructorExpr) : MExp :=
  .MApp (.MId f) $
    [.MId `initSize, .MId `size'] ++ (constructorExprToMExp <$> args)

/-- Converts a `HypothesisExpr` to an `MExp` -/
def hypothesisExprToMExp (hypExpr : HypothesisExpr) : MExp :=
  let (ctorName, ctorArgs) := hypExpr
  .MCtr ctorName (constructorExprToMExp <$> ctorArgs)

/-- `Pattern` that represents a wildcard (i.e. `_` on the LHS of a pattern-match) -/
def wildCardPattern : Pattern :=
  .UnknownPattern `_

/-- `MExp` representing a pattern-match on a `scrutinee` of type `Option Bool`.
     Specifically, `matchOptionBool scrutinee trueBranch falseBranch` represents
     ```lean
     match scrutinee with
     | some true => $trueBranch
     | some false => $falseBranch
     | none => $MExp.MOutOfFuel
     ```
-/
def matchOptionBool (scrutinee : MExp) (trueBranch : MExp) (falseBranch : MExp) : MExp :=
  .MMatch scrutinee
    [
      (.CtorPattern ``some [.UnknownPattern ``true], trueBranch),
      (.CtorPattern ``some [.UnknownPattern ``false], falseBranch),
      (.UnknownPattern ``none, .MOutOfFuel)
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

  /-- Compiles a `MExp` to a Lean `doElem`, according to the `DeriveSort` provided -/
  partial def mexpToTSyntax (mexp : MExp) (deriveSort : DeriveSort) : CompileScheduleM (TSyntax `term) :=
    match mexp with
    | .MId v | .MConst v => `($(mkIdent v))
    | .MApp func args => do
      let f ← mexpToTSyntax func deriveSort
      let compiledArgs ← args.toArray.mapM (fun e => mexpToTSyntax e deriveSort)
      `($f $compiledArgs*)
    | .MCtr ctorName args => do
      let compiledArgs ← args.toArray.mapM (fun e => mexpToTSyntax e deriveSort)
      `($(mkIdent ctorName) $compiledArgs*)
    | .MFun vars body => do
      let compiledBody ← mexpToTSyntax body deriveSort
      match vars with
      | [] => throwError "empty list of function arguments supplied to MFun"
      | [x] => `((fun $(mkIdent x) => $compiledBody))
      | _ =>
        -- When we have multiple args, create a tuple containing all of them
        -- in the argument of the lambda
        let args ← mkTuple vars
        `((fun $args:term => $compiledBody))
    | .MFail | .MOutOfFuel =>
      -- Note: right now we compile `MFail` and `MOutOfFuel` to the same Lean terms
      -- for simplicity, but in the future we may want to distinguish them
      match deriveSort with
      | .Generator | .Enumerator => `($failFn)
      | .Checker => `($(mkIdent ``some) $(mkIdent ``false))
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
      | .Generator, .OptionTGen
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
        let trueCase ← `(Term.matchAltExpr| | $(mkIdent ``some) $(mkIdent ``true) => $k1)
        let wildCardCase ← `(Term.matchAltExpr| | _ => $failFn)
        let cases := #[trueCase, wildCardCase]
        `(match $m1:term with $cases:matchAlt*)
      | .Checker, .Checker =>
        -- If the continuation of the bind is just returning `some True`,
        -- we can just inline the checker call `m1` to avoid the extra indirection
        -- of calling checker combinator functions
        if k == someTrue then
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
          -- We pass in `(min 2 initSize)` as the amount of fuel for the enumerator to avoid stack-overflow
          -- See https://github.com/ngernest/chamelean/issues/40 for details
          let fuelForEnumerator ← `($(mkIdent `min) 2 $initSizeIdent)
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
    | .MMatch scrutinee cases => do
      -- Compile the scrutinee, the LHS & RHS of each case separately
      let compiledScrutinee ← mexpToTSyntax scrutinee deriveSort
      let compiledCases ← cases.toArray.mapM (fun (pattern, rhs) => do
        let lhs ← compilePattern pattern
        let compiledRHS ← mexpToTSyntax rhs deriveSort
        `(Term.matchAltExpr| | $lhs:term => $compiledRHS))
      `(match $compiledScrutinee:term with $compiledCases:matchAlt*)

  /-- `MExp` representation of a constrained producer,
      parameterized by a `producerSort`, a list of variable names & their types `varsTys`,
      and a `Prop` (`prop`) constraining the values being produced

      - Note: this function corresponds to `such_that_producer`
        in the QuickChick code -/
  partial def constrainedProducer (prodSort : ProducerSort) (varsTys : List (Name × ConstructorExpr)) (prop : MExp) (fuel : MExp) : CompileScheduleM MExp :=
    if varsTys.isEmpty then
      panic! "Received empty list of variables for constrainedProducer"
    else do
      -- Determine whether the typeclass instance for the constrained generator already exists
      -- i.e. check if an instance for `ArbitrarySizedSuchThat` / `EnumSizedSuchThat` with the
      -- specified `argTys` and `prop` already exists
      let (args, argTys) := List.unzip varsTys
      let argsTuple ← mkTuple args
      let argTyTerms ← monadLift $ argTys.toArray.mapM constructorExprToTSyntaxTerm
      let propBody ← mexpToTSyntax prop .Generator
      let typeClassName :=
        match prodSort with
        | .Enumerator => ``EnumSizedSuchThat
        | .Generator => ``ArbitrarySizedSuchThat
      let typeClassInstance ← `($(mkIdent typeClassName) $argTyTerms* (fun $argsTuple:term => $propBody))

      -- Add the `typeClassInstance` for the constrained producer to the state,
      -- then obtain the `MExp` representing the constrained producer
      StateT.modifyGet $ fun instances =>
        let producerWithArgs := MExp.MFun args prop
        let producerMExp :=
          match prodSort with
          | .Enumerator => enumSizedST producerWithArgs fuel
          | .Generator => arbitrarySizedST producerWithArgs fuel
        (producerMExp, instances.push typeClassInstance)

end

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
def scheduleStepToMExp (step : ScheduleStep) (defFuel : MExp) (k : MExp) : CompileScheduleM MExp :=
  match step with
  | .Unconstrained v src prodSort => do
    let producer ←
      match src with
      | Source.NonRec hyp =>
        let ty ← hypothesisExprToTSyntaxTerm hyp
        unconstrainedProducer prodSort ty
      | Source.Rec f args => pure $ recCall f args
    pure $ .MBind (prodSortToMonadSort prodSort) producer [v] k
  | .SuchThat varsTys prod ps => do
    let producer ←
      match prod with
      | Source.NonRec hypExpr =>
        constrainedProducer ps varsTys (hypothesisExprToMExp hypExpr) defFuel
      | Source.Rec f args => pure (recCall f args)
    let vars := Prod.fst <$> varsTys
    pure $ .MBind (prodSortToOptionTMonadSort ps) producer vars k
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
  | .Match scrutinee pattern =>
    pure $ .MMatch (.MId scrutinee) [(pattern, k), (wildCardPattern, .MFail)]

/-- Converts a `Schedule` (a list of `ScheduleStep`s along with a `ScheduleSort`,
    which acts as the conclusion of the schedule) to an `MExp`.
    - `mfuel` and `defFuel` are auxiliary `MExp`s representing the fuel
      for the function we are deriving (these correspond to `size` and `initSize`
      in the QuickChick code for the derived functions) -/
def scheduleToMExp (schedule : Schedule) (mfuel : MExp) (defFuel : MExp) : CompileScheduleM MExp :=
  let (scheduleSteps, scheduleSort) := schedule
  -- Determine the *epilogue* of the schedule (i.e. what happens after we
  -- have finished executing all the `scheduleStep`s)
  let epilogue :=
    match scheduleSort with
    | .ProducerSchedule _ conclusionOutputs =>
      -- Convert all the outputs in the conclusion to `mexp`s
      let conclusionMExps := constructorExprToMExp <$> conclusionOutputs
      -- If there are multiple outputs, wrap them in a tuple
      match conclusionMExps with
      | [] => panic! "No outputs being returned in producer schedule"
      | [output] => MExp.MRet output
      | outputs => tupleOfList (fun e1 e2 => .MApp (.MConst ``Prod.mk) [e1, e2]) outputs outputs[0]?
    | .CheckerSchedule => someTrue
    | .TheoremSchedule conclusion typeClassUsed =>
      -- Create a pattern-match on the result of hte checker
      -- on the conclusion, returning `some true` or `some false` accordingly
      let conclusionMExp := hypothesisExprToMExp conclusion
      let scrutinee :=
        if typeClassUsed then decOptChecker conclusionMExp mfuel
        else conclusionMExp
      matchOptionBool scrutinee someTrue someFalse
  -- Fold over the `scheduleSteps` and convert each of them to a functional `MExp`
  -- Note that the fold composes the `MExp`, and we use `foldr` since
  -- we want the `epilogue` to be the base-case of the fold
  List.foldrM (fun step acc => scheduleStepToMExp step defFuel acc)
    epilogue scheduleSteps
