import Lean.Expr
import Plausible.Chamelean.Utils
import Plausible.Chamelean.Schedules
import Plausible.Chamelean.UnificationMonad
import Plausible.Chamelean.MakeConstrainedProducerInstance
import Plausible.Chamelean.LazyList
import Lean.Util.SCC

namespace Schedules

open Lean Meta
open Schedules

-- Adapted from QuickChick source code
-- https://github.com/QuickChick/QuickChick/blob/internal-rewrite/plugin/newGenericLib.ml

/-- Extracts all the unique variable names that appear in a hypothesis of a constructor for an inductive relation
    (this looks underneath constructor applications).

    For example, given `typing Γ (type.Abs τ1 e) (type.Fun τ1 τ2)`,
    this function returns `[Γ, τ1, e, τ2]`.
 -/
partial def variablesInHypothesisTSyntax (term : TSyntax `term) : MetaM (List Name) :=
  match term with
  | `($id:ident) => return [id.getId.eraseMacroScopes]
  | `($_:ident $args:term*)
  | `(($_:ident $args*)) => do
    -- Note that we have to explicitly pattern match on parenthesized constructor applications,
    -- otherwise we won't be able to handle nested constructor applications, e.g. `typing Γ (type.Abs τ1 e) (type.Fun τ1 τ2)`
    let foo ← args.toList.flatMapM variablesInHypothesisTSyntax
    return (List.eraseDups foo)
  | _ => return []

/-- Extracts all the unique variable names that appear in a `ConstructorExpr`
    (this looks underneath constructor applications). -/
def variablesInConstructorExpr (ctorExpr : ConstructorExpr) : List Name :=
  match ctorExpr with
  | .Unknown u => [u]
  | .Ctor _ args | .FuncApp _ args | .TyCtor _ args => args.flatMap variablesInConstructorExpr
  | .Lit _ => []

/-- Given a hypothesis `hyp`, along with `binding` (a list of variables that we are binding with a call to a generator), plus `recCall` (a pair contianing the name of the inductive and a list of output argument indices),
    this function checks whether the generator we're using is recursive.

    For example, if we're trying to produce a call to the generator [(e, tau) ← typing gamma _ _], then
    we would have `binding = [e,tau]` and `hyp = typing gamma e tau`. -/
def isRecCall (binding : List Name) (hyp : HypothesisExpr) (recCall : Name × List Nat) : MetaM Bool := do
  let (ctorName, args) := hyp
  -- An output position is a position where all vars contained are unbound
  -- if they are unbound, we include them in the list of output indices (`outputPositions`)
  let outputPositions ← filterMapMWithIndex (fun i arg => do
    let vars := variablesInConstructorExpr arg
    if vars.isEmpty then pure none
    else if List.all vars (. ∈ binding) then
      pure (some i)
    else if List.any vars (. ∈ binding) then do
      let v := List.find? (· ∈ binding) vars
      logError m!"error: {v} ∈ {binding} = binding"
      throwError m!"Arguments to hypothesis {hyp} contain both fixed and yet-to-be-bound variables (not allowed)"
    else pure none) args
  let (inductiveName, recCallOutputIdxes) := recCall

  return (ctorName == inductiveName && (recCallOutputIdxes.mergeSort) == (outputPositions.mergeSort))

/-- Given a list of `hypotheses` of an inductive constructor, each containing a list of arguments,
    pairs each hypothesis with a list containing, for each argument, a list of the variables contained
    inside that argument. For instance:

    `(C a (K b (H c d)) (3 * e))` is paired with `[[a],[b,c,d],[e]]`
    It then sorts the list of hypotheses with variables by the total number of variables across all
    arguments.
    (This is a heuristic, since we would like to work w/ hypotheses that have fewer variables first (fewer generation options to deal with).) -/
def mkSortedHypothesesVariablesMap (hypotheses : List HypothesisExpr) : List (HypothesisExpr × List (List Name)) :=
  let hypVarMap := hypotheses.map (fun h@(_, ctorArgs) =>
    (h, ctorArgs.map variablesInConstructorExpr))
  List.mergeSort hypVarMap (le := fun (_, vars1) (_, vars2) => vars1.flatten.length <= vars2.flatten.length)

/-- Environment for the `ScheduleM` reader monad -/
structure ScheduleEnv where
  /-- List of variables which are universally-quantified in the constructor's type,
      along with the types of these variables -/
  vars : List TypedVar

  /-- Hypotheses about the variables in `vars` -/
  sortedHypotheses : List (HypothesisExpr × List (List Name))

  /-- Determines whether we're deriving a checker/enumerator/generator -/
  deriveSort : DeriveSort

  /-- The sort of auxiliary producer (generators / enumerators) invoked by
      the function being derived. Note that if `deriveSort = Checker`, then
      `prodSort = Enumerator`, since checkers have to invoke enumerators
      as discussed in the Computing Correctly paper. -/
  prodSort : ProducerSort

  /-- A pair contianing the name of the inductive relation and a list of indices for output arguments -/
  recCall : Name × List Nat

  /-- A list of fixed variables (i.e. inputs to the inductive relation) -/
  fixed : List Name

/-- A monad for deriving generator schedules. Under the hood,
    `ScheduleM` is just a reader monad stacked on top of `MetaM`,
    with `ScheduleEnv` serving as the environment for the reader monad. -/
abbrev ScheduleM (α : Type) := ReaderT ScheduleEnv MetaM α

/-- After we generate some variables, look at the hypotheses and see if any of them only contain fixed variables
    (if yes, then we need to check that hypothesis)
    - `checkedHypotheses` contains the hypotheses that have been checked so far  -/
def collectCheckSteps (env : ScheduleEnv) (boundVars : List Name) (checkedHypotheses : List Nat) : List (Nat × Source) := do
  let (inductiveName, inputArgs) := env.recCall

  let toCheckSource hyp :=
    let (ctorName, ctorArgs) := hyp
    if env.deriveSort == DeriveSort.Checker && inputArgs.isEmpty && ctorName == inductiveName then
      Source.Rec `aux_dec ctorArgs
    else .NonRec hyp

  let checkSteps := filterMapWithIndex (fun i (hyp, vars) =>
    if i ∉ checkedHypotheses && List.all vars (List.all · (· ∈ boundVars)) then
      some (i, toCheckSource hyp)
    else none) env.sortedHypotheses

  checkSteps

/-- After we generate some variables, look at the hypotheses and see if any of them only contain fixed variables
    (if yes, then we need to check that hypothesis)
    - `checkedHypotheses` contains the hypotheses that have been checked so far. This version returns raw
    hypothesisExprs without checking what their source (recursive/nonrecursive) should be.  -/
def collectCheckedHypotheses (env : ScheduleEnv) (boundVars : List Name) (checkedHypotheses : List Nat) : List (Nat × HypothesisExpr) := do
  let checkSteps := filterMapWithIndex (fun i (hyp, vars) =>
    if i ∉ checkedHypotheses && List.all vars (List.all · (· ∈ boundVars)) then
      some (i, hyp)
    else none) env.sortedHypotheses

  checkSteps

/-- Determines whether inputs & outputs of a generator appear under the same constructor in a hypothesis `hyp`
    - Example: consider the `TApp` constructor for STLC (when we are generating `e` such that `typing Γ e τ` holds):
    ```
    | TApp: ∀ Γ e1 e2 τ1 τ2,
      typing Γ e2 τ1 →
      typing Γ e1 (.Fun τ1 τ2) →
      typing Γ (.App e1 e2) τ2
    ```
    The hypothesis `typing Γ e1 (.Fun τ1 τ2)` contains a term `.Fun τ1 τ2` where
    the existentially quantified variable `τ1` hasn't been generated yet,
    whereas `τ2` is an input to the generator (since it appears in the conclusion of `TApp`).
    Since `τ1, τ2` both appear under the same `.Fun` constructor,
    `outputInputNotUnderSameConstructor (.Fun τ1 τ2) [τ2]` returns `false`.  -/
def outputInputNotUnderSameConstructor (hyp : HypothesisExpr) (outputVars : List Name) : ScheduleM Bool := do
  let (_, args) := hyp
  let result ← not <$> args.anyM (fun arg => do
    let vars := variablesInConstructorExpr arg
    return List.any vars (. ∈ outputVars) && List.any vars (. ∉ outputVars))
  return result

/-- Determines whether the variables in `outputVars` are constrained by a function application or type constructor in the hypothesis `hyp`.
    This function is necessary since we can't output something and then assert that it equals the output of a (non-constructor) function
    (since we don't have access to the function). -/
partial def outputsNotConstrainedByFunctionApplication (hyp : HypothesisExpr) (outputVars : List Name) : ScheduleM Bool :=
  let (_, args) := hyp
  not <$> args.anyM (fun arg => check false arg)
    where
      check (b : Bool) (arg : ConstructorExpr) : ScheduleM Bool :=
        match arg with
        | .Unknown u => return (b && u ∈ outputVars)
        | .Ctor _ args => args.anyM (check b)
        | .TyCtor _ args
        | .FuncApp _ args => args.anyM (check true)
        | .Lit _ => return false

private inductive OptionallyTypedVar where
| TVar : TypedVar -> OptionallyTypedVar
| UVar : Name -> OptionallyTypedVar
  deriving Repr, BEq

/-- If we have a hypothesis that we're generating an argument for,
     and that argument is a constructor application where all of its args are outputs,
     then we just need to produce a backtracking check

     e.g. if we're trying to generate `TFun t1 t2 ← typing G e (TFun t1 t2)`,
     we have to do:
     ```
       v_t1t2 ← typing G e v_t1t2
       match v_t1t2 with
       | TFun t1 t2 => ...
       | _ => none
     ```
     assuming t1 and t2 are *unfixed* (not an input and not generated yet)

     The triple that is output consists of:
     - the list of pattern-matches that need to be produced
       (since TT can handle multiple outputs, each of which may need to be constrained by a pattern)
     - the updated thing we're generating for (e.g. `typing G e v_t1t2` in the example above), ie the RHS of the let-bind
     - the updated output list (e.g. `v_t1t2` in the example above), ie the LHS of the let-bind
     TODO: This function's purpose is to find all the matches that needs to be done for this output, but it tries to do it by looking
     which indicies need to be outputs by searching in them, but we have that info in preschedules, could just use that, filter
     to those indices, and perform the matches.

     -/
def handleConstrainedOutputs (hyp : HypothesisExpr) (outputVars : List TypedVar) : MetaM (List ScheduleStep × HypothesisExpr × List (OptionallyTypedVar)) := do
  let (ctorName, ctorArgs) := hyp

  let outputNamesTypes := outputVars.map (fun x => (x.var, x.type))

  let (patternMatches, args', newOutputs) ← splitThreeLists <$> ctorArgs.mapM (fun arg => do
    let vars := variablesInConstructorExpr arg

    match arg with
    | .Ctor _ _ =>
      match List.mapM (outputNamesTypes.lookup .) vars with
      | none => pure (none, arg, none)

      | some _typedOutputs =>

      if !vars.isEmpty then do
        let localCtx ← getLCtx
        let newName := localCtx.getUnusedName (Name.mkStr1 ("v" ++ String.intercalate "_" (Name.getString! <$> vars)))
        -- let argType ← inferType $ ToExpr.toExpr arg
        match patternOfConstructorExpr arg with
        | none => throwError m!"ConstructorExpr {arg} fails to be converted to pattern in handleConstrainedOutputs"
        | some pat =>
          let newMatch := ScheduleStep.Match .allExplicit newName pat
          pure (some newMatch, .Unknown newName, some (.UVar newName))
      else
        pure (none, arg, none)
    | .Unknown v =>
      match outputNamesTypes.lookup v with
      | some ty =>
        pure (none, arg, some (.TVar ⟨v,ty⟩))
      | none  =>
        pure (none, arg, none)
    | .FuncApp _ _  | .TyCtor _ _ =>
      pure (none, arg, none)
    | .Lit _ =>
      pure (none, arg, none)

      )

  return (patternMatches.filterMap id, (ctorName, args'), newOutputs.filterMap id)

/-- Converts a list of `ScheduleStep`s to *normal form* (i.e. all unconstrained generation
    occurs before constrained generation) -/
def normalizeSchedule (steps : List ScheduleStep) : List ScheduleStep :=
  -- `unconstrainedBlock` is a list of `ScheduleStep`s consisting only of unconstrianed generation
  -- (i.e. calls to `arbitrary`)
  let rec normalize (steps : List ScheduleStep) (unconstrainedBlock : List ScheduleStep) : List ScheduleStep :=
    match steps with
    | [] =>
      -- if we run out of steps, we can just sort the `unconstrainedBlock`
      -- according to the comparison function on `scheduleStep`s
      List.mergeSort (le := compareBlocks) unconstrainedBlock
    | step@(.Unconstrained _ _ _) :: steps =>
      -- If we encounter a step consisting of unconstrained generation,
      -- we cons it onto `unconstrainedBlock` & continue
      normalize steps (step::unconstrainedBlock)
    | step :: steps =>
      -- If we encounter any step that's not unconstrained generation,
      -- the current block of unconstrained generation is over,
      -- so we need to cons it (after sorting) to the head of the list of `step` and continue
      List.mergeSort (le := compareBlocks) unconstrainedBlock ++ step :: normalize steps []
  normalize steps []
    where
      -- Comparison function on blocks of `ScheduleSteps`
      compareBlocks b1 b2 := Ordering.isLE $ Ord.compare b1 b2

/-Lazily enumerates pairs where the first elements is all subsets of
  the given list `as` and the second element is the complement-/
private def subsetsAndComplements {α} (as : List α) : LazyList (List α × List α) :=
  match as with
  | [] => pure ([],[])
  | a :: as' => do
    let (subset,comp) ← subsetsAndComplements as'
    .lcons (a :: subset, comp) ⟨ fun _ => .lcons (subset, a :: comp) ⟨fun _ => .lnil⟩⟩

/- Unused utility function for future if we wish to prune selections of hypotheses by some predicate -/
private def subsetsAndComplementsSuchThat {α} (p : α -> Bool) (as : List α) : LazyList (List α × List α) :=
  match as with
  | [] => pure ([],[])
  | a :: as' => do
    let (subset,comp) ← subsetsAndComplementsSuchThat p as'
    if p a then
    .lcons (subset,a :: comp) ⟨ fun _ => .lcons (a :: subset, comp) ⟨fun _ => .lnil⟩⟩
    else
    .lcons (subset,a::comp) ⟨ fun _ => .lnil ⟩

/-Select takes a list `as` and lazily enumerates pairs of all elements of the list with the unselected remainder of the list-/
def select {α} (as : List α) : LazyList (α × List α) :=
  match as with
  | [] => .lnil
  | a :: as' =>
    .lcons (a, as') ⟨fun _ => LazyList.mapLazyList (fun (x,as'') => (x, a::as'')) (select as')⟩

/-- A `PreScheduleStep α v` is a simplified representation of a `ScheduleStep`. It is parameterized by
  `α`, which represents a hypothesis, and `v`, which is the type of variables. The first parameter
  is useful if we want to construct a preschedule without carrying around a complex representation
  of a hypothesis, the second is useful because we can represent both type-annotated and unannotated
  preschedules. -/
private inductive PreScheduleStep α v where
| Checks (hyps : List α) /- Check a sequence of hypotheses. -/
| Produce (out : List v) (hyp : α) /- Produce a list of variables `out` such that they satisfy hypotheses `hyp`. -/
| InstVars (var : List v) /- Instantiate a list of variables according to their type, unconstrained(Arbitrary/Enum). -/
deriving Repr

instance [Repr α] [Repr v] : Repr (List (PreScheduleStep α v)) where
  reprPrec steps _ :=
    let lines := steps.map fun step =>
      match step with
      | .InstVars vars => s!"{repr vars} ← arbitrary"
      | .Produce out hyp => s!"{repr out} ← {repr hyp}"
      | .Checks hyps => s!"check {repr hyps}"
    "do\n  " ++ String.intercalate "\n  " lines

private def collectRepeatedNames (lists : List (List Name)) : List Name :=
  let allNames := lists.flatten
  let counts := allNames.foldl (fun (acc : NameMap Nat) name => acc.alter name (fun opt => some ((opt.getD 0) + 1))) {}
  counts.toList.filterMap (fun (name, count) =>
    if count > 1 then some name else none)

private partial def containsFunctionCall (ctrExpr : ConstructorExpr) : Bool :=
  match ctrExpr with
  | .Unknown _ => false
  | .Ctor _ args | .TyCtor _ args => List.any args (fun x => containsFunctionCall x)
  | .FuncApp _ _ => true
  | .Lit _ => false

private partial def tyCtorConstrainsVariable (ctrExpr : ConstructorExpr) : Bool :=
  match ctrExpr with
  | .Unknown _ => false
  | .Ctor _ args | .FuncApp _ args => args.any tyCtorConstrainsVariable
  | .TyCtor _ _ => !(variablesInConstructorExpr ctrExpr).isEmpty
  | .Lit _ => false

private def constructHypothesis (hyp : HypothesisExpr × List (List Name)) : HypothesisExpr × List (List Name) × List Name :=
  let repeatedNames := collectRepeatedNames hyp.snd
  let hypIndices := List.zip hyp.fst.snd hyp.snd
  let (mustBind, allSafe) := hypIndices.partition (fun (ctrExpr, vars) =>
    containsFunctionCall ctrExpr || tyCtorConstrainsVariable ctrExpr || (vars.any (List.contains repeatedNames)))
  -- Any variables that appear multiple times in a hypothesis will end up in mustBind the same number of times, so we must deduplicate
  -- to avoid instantiating it multiple times.
  (hyp.fst, allSafe.map (fun x => x.snd), (List.eraseDups mustBind).flatMap (fun x => x.snd))

private def needs_checking {α v} [BEq v] (env : List v) (a_vars : α × List (List v) × List v) : Bool :=
  let (_, potentialIndices, alwaysBound) := a_vars
  alwaysBound.all (List.contains env) &&
  potentialIndices.all (fun idx => idx.all (List.contains env))

private def prune_empties {α v} (schd : List (PreScheduleStep α v)) : List (PreScheduleStep α v) :=
  schd.foldr aux []
  where
    aux pss l :=
      match pss with
      | .Checks [] => l
      | .InstVars [] => l
      | .Produce [] h => .Checks [h] :: l
      | _ => pss :: l

def computeSCC {v a} [DecidableEq v] (hypotheses : List (a × List v)) : List (List (a × List v)) :=
  let indices := List.range hypotheses.length
  let successors := fun i =>
    indices.filter fun j =>
      i ≠ j &&
      match hypotheses[i]?, hypotheses[j]? with
      | some (_, vars), some (_, vars') => vars.any (· ∈ vars')
      | _, _ => false
  let sccIndices := Lean.SCC.scc indices successors
  sccIndices.map fun component =>
    component.filterMap (fun i => hypotheses[i]?)

-- Two connected components {H} and {I,J}, as the latter share the variable 5
/--info: [[("H", [1, 2, 3]), ("J", [5, 1]), ("I", [4, 5])]]-/
#guard_msgs(all) in
#eval computeSCC [("H", [1,2,3]), ("I", [4,5]), ("J",[5,1])]

-- Example: Two connected components H1{a,b,c} & H2{a} vs H3{d} & H4{d,e}; the first two share a, the latter two share d
/--info: [[("H1", ["a", "b", "c"]), ("H2", ["a"])], [("H3", ["d"]), ("H4", ["d", "e"])]]-/
#guard_msgs(all) in
#eval computeSCC [("H1", ["a", "b", "c"]), ("H2", ["a"]), ("H3", ["d"]), ("H4", ["d", "e"])]

-- Example: Transitive dependencies make one big connected component.
/--info: [[("H1", ["a"]), ("H2", ["a", "b"]), ("H3", ["b", "c"]), ("H4", ["c"])]]-/
#guard_msgs(all) in
#eval computeSCC [("H1", ["a"]), ("H2", ["a", "b"]), ("H3", ["b", "c"]), ("H4", ["c"])]

-- Example: No overlap so all hypotheses are singleton components.
/--info: [[("H1", ["a"])], [("H2", ["b"])], [("H3", ["c"])]]-/
#guard_msgs(all) in
#eval computeSCC [("H1", ["a"]), ("H2", ["b"]), ("H3", ["c"])]


/- For each permutation, for each of its hypotheses, select which of its
unbound variables should be instantiated to satisfy it.
Not all unbound variables are able to be instantiated by a hypothesis,
so we must filter out those unbound mentioned in the hypothesis which
are arguments to a function (1) and those which are under a constructor
that contains a bound or invalid unbound variable (2) and those that
appear nonlinearly (as they would require an unlikely equality check)(3).
Here is an encompassing example:
`H (C a (f b)) c (C₃ c) d (C₃ (C₂ e) C₄)`
We can't instantiate `b` because it is under a function (1),
  `a` because it is under a constructor with an invalid variable `b` (2),
  `c` because it appears nonlinearly
We *can* instantiate `d` and `e` because they satisfy all three conditions
Note that despite e being stored under several constructors, there are no
bound or invalid variables mixed in, so we can generate H's 5th argument
and pattern match the result against `(C₃ (C₂ x) C₄)` and if it matches,
`e` to the value `x`.

The remainder of its unbound variables should be instantiated according
to their type unconstrained by a hypothesis. These unconstrained instantiations
should happen before the constrained instantiation. For each `2^|unbound ∩ valid|`
choice, we prepend the unconstrained instantiations behind the constrained one
and lazily cons that version of the schedule to our list.

Finally, we fold through the list, tracking the set of variables bound, as soon
as a constraint has had all its variables bound, a check for it
should be inserted at that point in the schedule. Finally, return
the schedules. -/

/-
  Depth-first enumeration of all possible schedules.

  The list of possible schedules boils down to taking a permutation of list of hypotheses -- what this function
  does is it comes up with the list of possible permutations of hypotheses.

  For `TyApp` in the STLC example, here are the possible permutations (output is e, the unbound vars are {e1, e2, t1}):

  (a.) `[typing Γ e1 (TFun 𝜏1 𝜏2), typing Γ e2 𝜏1]`
  (b.) `[typing Γ e2 𝜏1, typing Γ e1 (TFun 𝜏1 𝜏2)]`

  We first discuss permutation (a).

  For permutation (a), `t1` and `e1` are unbound, so we're generate the max no. of variables possible
    * `e1` is in an outputtable position (since its not under a constructor)
    * `t1` is *not* in an ouputtable position (since `t1` is under the `TFun` constructor, `type` is an input mode, and `t2` is also an input mode)
    * This means `t1` has to be generated first arbitrarily

  We have elaborated this step to:
  ```lean
    t1 ← type                      -- (this uses the `Arbitrary` instance for [type])
    e1 ← typing Γ ? (TFun t1 t2)    -- (this desugars to `arbitraryST (fun e1 => typing Γ e1 (TFun t1 t2))` )
  ```

  Now that we have generated `t1` and `e1`, the next hypothesis is `typing Γ e2 𝜏1`
  * `e2` is the only variable that's unbound
  * Thus, our only option is to do:
  ```lean
    e2 ← typing Γ ? t1
  ```

  + For permutation (b), the first thing we do is check what are the unbound (not generated & not fixed by inputs)
    variables that are constrained by the first hypothesis `typing Γ e2 𝜏1`
    * `e2` is unbound & can be output (since its in the output mode & not generated yet)
    * `t1` can also be output since its not been generated yet & not under a constructor
      * `Γ` is fixed already (bound) b/c its a top-level argument (input) to `aux_arb`
    * Here we have 3 possible choices:
      1. Arbitrary [t1], ArbitrarySuchThat [e2]
      2. Arbitrary [e2], ArbitrarySuchThat [t1]
      3. ArbitrarySuchThat [e2, t1]

    * For each choice, we can then elaborate the next `ScheduleStep` in our hypothesis permutation (i.e. `typing Γ e1 (TFun 𝜏1 𝜏2)`)
    + Rest of the logic for dealing with permutation (b) is similar to as the 1st permutation
-/

/- Variables in third elt of hyp should be disjoint from flatten of snd elt
   Assume that any hyp in hyps should have at least one thing it could generate
   Any hypothesis which lacks an index it can generate from should be checked
   in a prior step. The second element of hyps should contain only lists of unbound
   variables.

   The snd and third elements combined should equal the set vars(hyp.fst)
-/

private partial def enumSchedules {α v} [BEq v] (vars : List v) (hyps : List (α × List (List v) × List v)) (env : List v)
  : LazyList (List (PreScheduleStep α v)) :=
  match hyps with
  | [] => pure (prune_empties [.InstVars $ vars.removeAll env])
  | _ => do
    let ⟨ (hyp, potential_output_indices, always_bound_variables),hyps' ⟩ ← select hyps
    let (some_bound_output_indices, all_unbound_output_indices) := List.partition (List.any . (List.contains env)) potential_output_indices
    let (out,bound) ← subsetsAndComplements all_unbound_output_indices
    if out.length > 1 then .lnil else
    let bound_vars := bound.flatten ++ (always_bound_variables ++ some_bound_output_indices.flatten).filter (not ∘ List.contains env)
    let env' := bound_vars ++ env
    let (prechecks,to_be_satisfied) := List.partition (needs_checking env') hyps'
    let out_vars := out.flatten
    let env'' := out_vars ++ env'
    let (postchecks,to_be_satisfied') := List.partition (needs_checking env'') to_be_satisfied
    LazyList.mapLazyList (fun l => prune_empties [.InstVars bound_vars
                              , .Checks (Prod.fst <$> prechecks)
                              , .Produce out_vars hyp
                              , .Checks (Prod.fst <$> postchecks)
                              ]
                              ++ l) (enumSchedules vars to_be_satisfied' env'')

#guard_msgs(error, drop info) in
#eval (enumSchedules [1,2,3,4] [("A",[[1,2,3],[4]],[]), ("B",[[4]],[])] []).take 15

-- Simple test with 2 hypotheses
#guard_msgs(error, drop info) in
#eval (enumSchedules [1,2,3] [("A",[[1],[2]],[]), ("B",[[2],[3]],[])] []).take 3

-- Test with overlapping variables
#guard_msgs(error, drop info) in
#eval (enumSchedules [1,2,3,4,5] [("H1",[[1],[2],[3]],[]), ("H2",[[3],[4]],[]), ("H3",[[4],[5]],[])] []).take 5

-- Test with some variables already bound
#guard_msgs(error, drop info) in
#eval (enumSchedules [1,2,3] [("A",[[1],[2]],[]), ("B",[[2],[3]],[])] [1])

-- Larger example to test scalability
#guard_msgs(error, drop info) in
#eval (enumSchedules [1,2,3,4] [("P",[[1],[2]],[]), ("Q",[[2],[3]],[]), ("R",[[3],[4]],[]), ("S",[[1],[4]],[])] []).take 10

-- Lots of variables (10 variables in one hypothesis)
#guard_msgs(error, drop info) in
#eval (enumSchedules [1,2,3,4,5,6,7,8,9,10] [("BigHyp",[[1],[2],[3],[4],[5],[6],[7],[8],[9],[10]],[])] []).take 5

-- Lots of hypotheses (10 hypotheses with few variables each)
#guard_msgs(error, drop info) in
#eval (enumSchedules [1,2,3,4,5,6,7,8,9,10] [("H1",[[1]],[]), ("H2",[[2]],[]), ("H3",[[3]],[]), ("H4",[[4]],[]), ("H5",[[5]],[]),
                       ("H6",[[6]],[]), ("H7",[[7]],[]), ("H8",[[8]],[]), ("H9",[[9]],[]), ("H10",[[10]],[])] []).take 3

-- Both: many hypotheses with many variables each
#guard_msgs(error, drop info) in
#eval (enumSchedules (List.range 14) [("A",[[1],[2],[3],[4],[5]],[]), ("B",[[3],[4],[5],[6],[7]],[]), ("C",[[5],[6],[7],[8],[9]],[]),
                       ("D",[[7],[8],[9],[10],[11],[3],[1],[2]],[]), ("E",[[9],[10],[11],[12],[13]],[])] []).take 100

#guard_msgs(error, drop info) in
#eval (@enumSchedules String Nat _ [] [] [])

-- Example for BetweenN constructor:
-- BetweenN : ∀ n m, n <= m -> Between n (.succ n) (.succ (.succ m))
-- Variables: n, m (inputs), output: Between n (.succ n) (.succ (.succ m))
-- Hypothesis: n <= m
-- The hypothesis "n <= m" has variables [n, m] which are both inputs (always bound)
#guard_msgs(error, drop info) in
#eval (enumSchedules [`n, `m] [(`n_le_m, [], [`n, `m])] [`n,`m]).take 5

/--
`enumSchedules'` is a variant of `enumSchedules` where instead of taking a list of hypotheses to permute,
it takes a list of simply connected components of hypotheses based on reachability in the graph
where an edge between hypotheses exists iff their variable sets overlap. It then permutes
only hypotheses within components but not between components. The different components are kept
in a canonical order always, thus dramatically reducing the size of the enumeration. This is okay
because hypotheses in different components cannot possibly depend on each other, so their ordering
does not make a difference.
-/
private partial def enumSchedules' {α v} [BEq v] (vars : List v) (hypComps : List (List (α × List (List v) × List v))) (env : List v)
  : LazyList (List (PreScheduleStep α v)) :=
  match hypComps with
  | [] => pure (prune_empties [.InstVars $ vars.removeAll env])
  | [] :: hypComps' => enumSchedules' vars hypComps' env
  | hyps :: hypComps' => do
    let ⟨ (hyp, potential_output_indices, always_bound_variables),hyps' ⟩ ← select hyps
    let (some_bound_output_indices, all_unbound_output_indices) := List.partition (fun l => List.any l (List.contains env) || l.isEmpty) potential_output_indices
    let (out,bound) ← subsetsAndComplements all_unbound_output_indices
    if out.length > 1 || (out.isEmpty && !bound.isEmpty) then .lnil else
    let bound_vars := bound.flatten ++ (always_bound_variables ++ some_bound_output_indices.flatten).filter (not ∘ List.contains env)
    let env' := bound_vars ++ env
    let (prechecks,to_be_satisfied) := List.partition (needs_checking env') hyps'
    let out_vars := out.flatten
    let env'' := out_vars ++ env'
    let (postchecks,to_be_satisfied') := List.partition (needs_checking env'') to_be_satisfied
    LazyList.mapLazyList (fun l => prune_empties [.InstVars (List.eraseDups bound_vars)
                              , .Checks (Prod.fst <$> prechecks)
                              , .Produce out_vars hyp
                              , .Checks (Prod.fst <$> postchecks)
                              ]
                              ++ l) (enumSchedules' vars (to_be_satisfied' :: hypComps') env'')

#guard_msgs(error, drop info) in
#eval (enumSchedules' [1,2,3,4] [[("A",[[1,2,3],[4]],[])], [("B",[[4]],[])]] []).take 15

-- Two separate SCCs: {H1,H2} share 'a', {H3,H4} share 'd'
#guard_msgs(error, drop info) in
#eval (enumSchedules' ["a","b","c","d","e"] [[("H1",[["a"],["b"],["c"]],[]), ("H2",[["a"]],[])], [("H3",[["d"]],[]), ("H4",[["d"],["e"]],[])]] []).take 100

-- Three SCCs: connected chain, isolated, pair
#guard_msgs(error, drop info) in
#eval (enumSchedules' [1,2,3,4,5,6] [[("A",[[1],[2]],[]), ("B",[[2],[3]],[]), ("C",[[3]],[])], [("D",[[4]],[])], [("E",[[5]],[]), ("F",[[5],[6]],[])]] []).take 100

-- Multiple single-node SCCs
#guard_msgs(error, drop info) in
#eval (enumSchedules' [1,2,3] [[("X",[[1]],[])], [("Y",[[2]],[])], [("Z",[[3]],[])]] []).take 2

-- Comparison: enumSchedules vs enumSchedules' - total schedule counts
-- Example 1: Two separate SCCs should reduce schedules significantly
#guard_msgs(error, drop info) in
#eval (enumSchedules ["a","b","c","d"] [("H1",[["a"],["b"]],[]), ("H2",[["a"]],[]), ("H3",[["c"],["d"]],[]), ("H4",[["c"]],[])] []).length

#guard_msgs(error, drop info) in
#eval (enumSchedules' ["a","b","c","d"] [[("H1",[["a"],["b"]],[]), ("H2",[["a"]],[])], [("H3",[["c"],["d"]],[]), ("H4",[["c"]],[])]] []).length

-- Example 2: Single SCC should have same count
#guard_msgs(error, drop info) in
#eval (enumSchedules [1,2,3] [("A",[[1],[2]],[]), ("B",[[2],[3]],[])] []).length

#guard_msgs(error, drop info) in
#eval (enumSchedules' [1,2,3] [[("A",[[1],[2]],[]), ("B",[[2],[3]],[])]] []).length


-- Compare binary choice approach vs full permutations
-- Generates all possible permutations of a list (factorial growth)
private partial def enumAllPermutations {α} [BEq α] (hyps : List α) : LazyList (List α) :=
  match hyps with
  | [] => pure []
  | _ => do
    let ⟨h, rest⟩ ← select hyps
    let restPerms ← enumAllPermutations rest
    pure (h :: restPerms)

-- Build dependency graph: for each hypothesis, find all other hypotheses that share variables
private def getNeighbors {α v} [BEq α] [BEq v] (hyps : List (α × List v)) : List (α × List α) :=
  hyps.map (fun (hyp, vars) =>
    let neighbors := hyps.filter (fun (otherHyp, otherVars) =>
      hyp != otherHyp && vars.any (otherVars.contains ·))
    (hyp, neighbors.map Prod.fst))

-- Represents a partitioning of an ordering into chunks separated by anchor points
-- Used to efficiently insert new elements while respecting dependency constraints
structure Chunks α where
  beforeAnchor : List α     -- Elements before any anchor
  anchors : List (List α)   -- Chunks starting with anchor elements
  numAnchors : Nat         -- Number of anchor chunks
  deriving Repr

-- Split an ordering into chunks based on anchor points (dependencies that must be preserved)
private def splitIntoChunks {α} [BEq α] (order : List α) (anchors : List α) : Chunks α :=
  let (beforeAnchor, rest) := order.span (!anchors.contains ·)
  let rec split (remaining : List α) (currentChunk : List α) (result : List (List α)) : List (List α) :=
    match remaining with
    | [] => currentChunk.reverse :: result |>.reverse
    | x :: xs =>
      if anchors.contains x then
        split xs [x] (currentChunk.reverse :: result)
      else
        split xs (x :: currentChunk) result
  let anchors :=
    match rest with
    | firstAnchor :: rest' => split rest' [firstAnchor] []
    | [] => []
  let numAnchors := anchors.length
  ⟨beforeAnchor, anchors, numAnchors⟩

-- Insert new hypotheses into chunks while preserving anchor constraints
-- Each new hypothesis can be inserted at any valid chunk boundary
private partial def enumChunkedInsertions {α} [BEq α] (newHyps : List α) (chunks : Chunks α) : LazyList (List α) :=
  match newHyps, chunks with
  | [], _ => pure $ chunks.beforeAnchor ++ chunks.anchors.flatten
  | h :: hs, _ => do
    let chunkIdx ← LazyList.range (chunks.numAnchors + 1)
    let newChunks := {chunks with anchors := chunks.anchors.insertIdx (chunkIdx) [h], numAnchors := chunks.numAnchors + 1}
    enumChunkedInsertions hs newChunks

/-Simple examples  displaying how a list is chunked into relevant sublists to insert around.-/

/--info: { beforeAnchor := ["A"], anchors := [["B", "C"]], numAnchors := 1 } -/
#guard_msgs in
#eval splitIntoChunks ["A", "B", "C"] ["B"]

/--info: { beforeAnchor := [], anchors := [[4], [5, 6]], numAnchors := 2 }-/
#guard_msgs in
#eval (splitIntoChunks [4,5,6] [4,5])

/-Example of the result of chunking followed by insertion around those chunks.-/
/--info: [[1, 4, 5, 6], [4, 1, 5, 6], [4, 5, 6, 1]]-/
#guard_msgs in
#eval enumChunkedInsertions [1] (splitIntoChunks [4,5,6] [4,5])

-- Generate orderings that satisfy dependency constraints between hypotheses
-- Uses chunked insertion to avoid exponential blowup while respecting variable dependencies
private partial def enumDependencySatisfyingOrderings {α v} [BEq α] [Repr α] [Repr v] [BEq v] [Hashable v] (hyps : List (α × List v)) : LazyList (List α) := do
  let neighbors := getNeighbors hyps
  let mut currentOrder := []
  for (h, neighbors) in neighbors do
    -- For each hypothesis, find which of its dependencies are already in the current order
    let inOrder := neighbors.filter (currentOrder.contains ·)
    -- Split current order into chunks based on these dependency anchors
    let chunks := splitIntoChunks currentOrder inOrder
    -- Insert the new hypothesis at all valid positions (respecting dependencies)
    currentOrder ← enumChunkedInsertions [h] chunks
  return currentOrder

/--info: [[2, 5, 1], [1, 2, 5], [5, 1, 2], [1, 5, 2]]-/
#guard_msgs in
#eval (enumChunkedInsertions [2] $ splitIntoChunks · [5]) =<< (enumChunkedInsertions [1,5] (splitIntoChunks [] []))

-- Test chunked approach with simple dependency chain: H depends on var 1, I depends on vars 1&2, J depends on var 2
/--info: [["J", "I", "H"], ["H", "J", "I"], ["I", "H", "J"], ["H", "I", "J"]]-/
#guard_msgs in
#eval enumDependencySatisfyingOrderings [("H",[1]),("I",[1,2]),("J",[2])]

-- Test with linear chain of 26 hypotheses - should generate only a single ordering, much less than 26! permutations
/--info: 1-/
#guard_msgs in
#eval enumDependencySatisfyingOrderings (List.map (fun a => (a,[a+1])) (1...26).toList) |>.take 100 |>.length

-- Test with real Cedar example (with numbers in place of variable names) showing complex variable dependencies
/--info: 288-/
#guard_msgs in
#eval @enumDependencySatisfyingOrderings _ _ _ _ _ _ _ ([("V_eq", [11, 0, 1, 2]),
                                   ("DefinedEntities", [0, 3]),
                                   ("WfCedarType", [3, 4]),
                                   ("SubType_T1", [5, 4]),
                                   ("SubType_T2", [6, 4]),
                                   ("HasType_E2", [11, 12, 8, 10, 6]),
                                   ("HasType_E1", [11, 12, 7, 9, 5])]) |>.length

-- Test cases comparing exponential permutation growth vs dependency-aware ordering
-- Baseline: all permutations of 4 elements = 4! = 24
/--info: 24-/
#guard_msgs in
#eval enumAllPermutations ["H", "I", "J", "K"] |>.length  -- Should be 4! = 24

-- Dependency-constrained: H,I share var 1; I,J share var 2; K is independent
/--info: 4-/
#guard_msgs in
#eval enumDependencySatisfyingOrderings [("H",[1]),("I",[1,2]),("J",[2]),("K",[3])] |>.length  -- Should be much less

-- More complex example: 5 hypotheses with mixed dependencies vs 6! = 720 permutations
/--info: 720-/
#guard_msgs in
#eval enumAllPermutations ["A", "B", "C", "D", "E", "F"] |>.length  -- 5! = 120

-- Complex dependency graph with multiple connected components
/--info: 32-/
#guard_msgs in
#eval enumDependencySatisfyingOrderings [("A",[1]),("B",[1,2]),("C",[2,3]),("D",[4]),("E",[5,1,2]), ("F",[4,6])] |>.length  -- Should be much less

-- Subset with connected component A-B-C-E
/--info: [["E", "C", "B", "A"],
 ["E", "A", "C", "B"],
 ["E", "B", "A", "C"],
 ["E", "A", "B", "C"],
 ["C", "E", "B", "A"],
 ["A", "E", "C", "B"],
 ["B", "E", "A", "C"],
 ["A", "E", "B", "C"],
 ["C", "B", "E", "A"],
 ["A", "C", "E", "B"],
 ["B", "A", "E", "C"],
 ["A", "B", "E", "C"],
 ["C", "B", "A", "E"],
 ["A", "C", "B", "E"],
 ["B", "A", "C", "E"],
 ["A", "B", "C", "E"]]-/
#guard_msgs in
#eval enumDependencySatisfyingOrderings [("A",[1]),("B",[1,2]),("C",[2,3]),("E",[5,1,2])]

-- Separate component D-F
/--info: [["F", "D"], ["D", "F"]]-/
#guard_msgs in
#eval enumDependencySatisfyingOrderings [("D",[4]), ("F",[4,6])]  -- Should be much less

-- Extreme case: 7! = 5040 permutations
/--info: 5040-/
#guard_msgs in
#eval enumAllPermutations (0...7).toList |>.length

-- vs dependency-aware with overlapping variable ranges (much more constrained)
/--info: 720-/
#guard_msgs in
#eval enumDependencySatisfyingOrderings (List.map (fun a => (a,(a...(a + 10)).toList)) (1...7).toList) |>.length  -- Should be much less

/--
`enumSchedules'` is a variant of `enumSchedules` where instead of taking a list of hypotheses to permute,
it takes a list of simply connected components of hypotheses based on reachability in the graph
where an edge between hypotheses exists iff their variable sets overlap. It then permutes
only hypotheses within components but not between components. The different components are kept
in a canonical order always, thus dramatically reducing the size of the enumeration. This is okay
because hypotheses in different components cannot possibly depend on each other, so their ordering
does not make a difference.
-/
private def enumSchedulesChunked {α v} [BEq v] (vars : List v) (hypComps : List (LazyList (List (α × List (List v) × List v)))) (env : List v)
  : LazyList (List (PreScheduleStep α v)) :=
  match hypComps with
  | [] => pure (prune_empties [.InstVars $ vars.removeAll env])
  | componentPerms :: hypComps' => do
    let mut perm ← componentPerms
    let mut sched := []
    let mut env := env
    repeat
      match perm with
      | [] => break
      | (hyp, potential_output_indices, always_bound_variables) :: rest =>
      perm := rest
      let (some_bound_output_indices, all_unbound_output_indices) := List.partition (fun l => List.any l (List.contains env) || l.isEmpty) potential_output_indices
      let (out,bound) ← subsetsAndComplements all_unbound_output_indices
      if out.length > 1 || (out.isEmpty && !bound.isEmpty) then .lnil else
      let bound_vars := bound.flatten ++ (always_bound_variables ++ some_bound_output_indices.flatten).filter (not ∘ List.contains env)
      env := bound_vars ++ env
      let (prechecks,to_be_satisfied) := List.partition (needs_checking env) perm
      let out_vars := out.flatten
      env := out_vars ++ env
      let (postchecks,to_be_satisfied') := List.partition (needs_checking env) to_be_satisfied
      sched := sched ++ prune_empties [.InstVars bound_vars
                                , .Checks (Prod.fst <$> prechecks)
                                , .Produce out_vars hyp
                                , .Checks (Prod.fst <$> postchecks)
                                ];
      perm := to_be_satisfied'
    LazyList.mapLazyList (sched ++ ·) $ enumSchedulesChunked vars hypComps' env

-- Determine the right name for the recursive function in the producer
private def recursiveFunctionName (deriveSort : DeriveSort) : Name :=
  match deriveSort with
  | DeriveSort.Generator => `aux_arb
  | .Enumerator => `aux_enum
  | .Checker | .Theorem => `aux_dec

private def preScheduleStepToScheduleStep (preStep : PreScheduleStep HypothesisExpr TypedVar) : ScheduleM (List ScheduleStep) := do
  let env ← read
  match preStep with
  | .Checks hyps => return (hyps.map (fun hyp =>
    let src := if env.deriveSort == DeriveSort.Checker && env.recCall.fst == hyp.fst then
      Source.Rec (recursiveFunctionName env.deriveSort) hyp.snd
    else
      Source.NonRec hyp;
    ScheduleStep.Check src true))
  | .Produce outs hyp =>
    let (newMatches, hyp', newOutputs) ← handleConstrainedOutputs hyp outs
    let typedOutputs ← newOutputs.mapM
      (fun v =>
        match v with
        | .TVar v => do
          let typ ← exprToConstructorExpr v.type
          pure (v.var, some typ)
        | .UVar n =>
          pure (n, none)
          )
    let (_, hypArgs) := hyp'
    let constrainingRelation ←
      if (← isRecCall (outs.map (fun x => x.var)) hyp env.recCall) then
        let inputArgs := filterWithIndex (fun i _ => i ∉ (Prod.snd env.recCall)) hypArgs
        pure (Source.Rec (recursiveFunctionName env.deriveSort) inputArgs)
      else
        pure (Source.NonRec hyp')
    return (ScheduleStep.SuchThat typedOutputs constrainingRelation env.prodSort :: newMatches)
  | .InstVars vars =>
    vars.mapM (fun ⟨v,ty⟩ => do
    let (ctorName, ctorArgs) := ty.getAppFnArgs
    let src ←
      if ctorName == Prod.fst env.recCall
        then Source.Rec (recursiveFunctionName env.deriveSort) <$> ctorArgs.toList.mapM (fun foo => exprToConstructorExpr foo)
      else
        let hypothesisExpr ← exprToHypothesisExpr ty
        pure (Source.NonRec hypothesisExpr)
    return ScheduleStep.Unconstrained v src env.prodSort
    )

/-- Takes a `deriveSort` and returns the corresponding `ProducerSort`:
    - If we're deriving a `Checker` or a `Enumerator`, the corresponding `ProducerSort` is an `Enumerator`,
      since its more efficient to enumerate values when checking
    - If we're deriving a `Generator` or a function which generates inputs to a `Theorem`,
      the corresponding `ProducerSort` is a `Generator`, since we want to generate random inputs -/
def convertDeriveSortToProducerSort (deriveSort : DeriveSort) : ProducerSort :=
  match deriveSort with
  | .Checker | .Enumerator => ProducerSort.Enumerator
  | .Generator | .Theorem => ProducerSort.Generator

private def typePreScheduleStep {α} (tyMap : NameMap Expr) (step : PreScheduleStep α Name) : (PreScheduleStep α TypedVar) :=
  match step with
  | .Checks hyps => .Checks hyps
  | .Produce out hyp =>
    let typedOut := out.map (fun name =>
      let ty := tyMap.get! name
      ⟨name, ty⟩)
    .Produce typedOut hyp
  | .InstVars vars =>
    let typedVars := vars.map (fun name =>
      let ty := tyMap.get! name
      ⟨name, ty⟩)
    .InstVars typedVars

instance [ToString α] [ToString v] : ToString (List (List (PreScheduleStep α v))) where
  toString schedules :=
    schedules.map (fun steps =>
      let lines := steps.map fun step =>
        match step with
        | .InstVars vars => s!"{vars} ← arbitrary"
        | .Produce out hyp => s!"{out} ← {hyp}"
        | .Checks hyps => s!"check {hyps}"
      "do\n  " ++ String.intercalate "\n  " lines
    ) |> String.intercalate "\n\n"

private def possiblePreSchedules (vars : List TypedVar) (hypotheses : List HypothesisExpr) (deriveSort : DeriveSort)
  (recCall : Name × List Nat) (fixedVars : List Name) : LazyList ((List (PreScheduleStep HypothesisExpr TypedVar))) × ScheduleEnv :=
  let sortedHypotheses := mkSortedHypothesesVariablesMap hypotheses
  let varNames := vars.map (fun x => x.var)
  let prodSort := convertDeriveSortToProducerSort deriveSort
  let scheduleEnv := ⟨ vars, sortedHypotheses, deriveSort, prodSort, recCall, fixedVars ⟩
  let remainingVars := List.filter (fun v => not $ fixedVars.contains v) varNames
  let (newCheckedIdxs, newCheckedHyps) := List.unzip $ (collectCheckedHypotheses scheduleEnv fixedVars [])
  let remainingSortedHypotheses := filterWithIndex (fun i _ => i ∉ newCheckedIdxs) sortedHypotheses
  let connectedHypotheses := remainingSortedHypotheses
                             |>.map (fun (h,vars) => ((h,vars), List.flatten vars))
                             |> computeSCC
                             |>.map (enumDependencySatisfyingOrderings ·
                                    |> LazyList.mapLazyList (List.map constructHypothesis))
  let firstChecks := PreScheduleStep.Checks newCheckedHyps.reverse
  let lazyPreSchedules : LazyList (List (PreScheduleStep HypothesisExpr Name)) := enumSchedulesChunked remainingVars connectedHypotheses fixedVars
  let nameTypeMap := List.foldl (fun m ⟨name,ty⟩ => NameMap.insert m name ty) ∅ vars
  let typedPreSchedules : LazyList (List (PreScheduleStep HypothesisExpr TypedVar)) := lazyPreSchedules.mapLazyList ((firstChecks :: ·) ∘ List.map (typePreScheduleStep nameTypeMap))
  (typedPreSchedules, scheduleEnv)

/-- Computes all possible schedules for a constructor
    (each candidate schedule is represented as a `List ScheduleStep`).

    Arguments:
    - `vars`: list of universally-quantified variables and their types
    - `hypotheses`: List of hypotheses about the variables in `vars`
    - `deriveSort` determines whether we're deriving a checker/enumerator/generator
    - `recCall`: a pair contianing the name of the inductive relation and a list of indices for output arguments
      + `recCall` represents what a recursive call to the function being derived looks like
    - `fixedVars`: A list of fixed variables (i.e. inputs to the inductive relation) -/
def possibleSchedules (vars : List TypedVar) (hypotheses : List HypothesisExpr) (deriveSort : DeriveSort)
  (recCall : Name × List Nat) (fixedVars : List Name) : LazyList (MetaM (List ScheduleStep)) := do
  let (typedPreSchedules, scheduleEnv) := possiblePreSchedules vars hypotheses deriveSort recCall fixedVars
  let lazySchedules := typedPreSchedules.mapLazyList ((ReaderT.run . scheduleEnv) ∘ List.flatMapM preScheduleStepToScheduleStep)
  lazySchedules

/-- Computes all possible schedules for a constructor
    (each candidate schedule is represented as a `List ScheduleStep`).

    Arguments:
    - `vars`: list of universally-quantified variables and their types
    - `hypotheses`: List of hypotheses about the variables in `vars`
    - `deriveSort` determines whether we're deriving a checker/enumerator/generator
    - `recCall`: a pair contianing the name of the inductive relation and a list of indices for output arguments
      + `recCall` represents what a recursive call to the function being derived looks like
    - `fixedVars`: A list of fixed variables (i.e. inputs to the inductive relation) -/
def possibleSchedules' (vars : List TypedVar) (hypotheses : List HypothesisExpr) (deriveSort : DeriveSort)
  (recCall : Name × List Nat) (fixedVars : List Name) : LazyList (MetaM (List ScheduleStep)) := do
  let sortedHypotheses := mkSortedHypothesesVariablesMap hypotheses
  let varNames := vars.map (fun x => x.var)
  let prodSort := convertDeriveSortToProducerSort deriveSort
  let scheduleEnv := ⟨ vars, sortedHypotheses, deriveSort, prodSort, recCall, fixedVars ⟩
  let remainingVars := List.filter (fun v => not $ fixedVars.contains v) varNames
  let (newCheckedIdxs, newCheckedHyps) := List.unzip $ (collectCheckSteps scheduleEnv fixedVars [])
  let remainingSortedHypotheses := filterWithIndex (fun i _ => i ∉ newCheckedIdxs) sortedHypotheses
  let connectedHypotheses := (computeSCC (remainingSortedHypotheses.map (fun (h,vars) => ((h,vars),vars.flatten)))).map (List.map fun ((h,vars),_) => constructHypothesis (h,vars))
  let firstChecks := List.reverse $ (ScheduleStep.Check . true) <$> newCheckedHyps
  let lazyPreSchedules : LazyList (List (PreScheduleStep HypothesisExpr Name)) := enumSchedules' remainingVars connectedHypotheses fixedVars
  let nameTypeMap := List.foldl (fun m ⟨name,ty⟩ => NameMap.insert m name ty) ∅ vars
  let typedPreSchedules : LazyList (List (PreScheduleStep HypothesisExpr TypedVar)) := lazyPreSchedules.mapLazyList (List.map (typePreScheduleStep nameTypeMap))
  let lazySchedules := typedPreSchedules.mapLazyList ((ReaderT.run . scheduleEnv) ∘ ((firstChecks ++ .) <$> .) ∘ List.flatMapM preScheduleStepToScheduleStep)
  lazySchedules

def exampleEnumSchedulesChunked :=
  -- All hypotheses from Cedar.HasType.TContainsAny constructor
  let hypotheses := [
    (`V_eq, [[`ets, `acts, `R]], [`V]),
    (`DefinedEntities, [[`ets], [`ns]], []),
    (`WfCedarType, [[`ns], [`T]], []),
    (`SubType_T1, [[`T1], [`T]], []),
    (`SubType_T2, [[`T2], [`T]], []),
    (`HasType_E1, [ [`E1], [`x1], [`T1]], [`V]),
    (`HasType_E2, [ [`E2], [`x2], [`T2]], [`V])
  ]

  -- Use computeSCC to find connected components then enumerate valid orderings that satisfy dependencies within each.
  let components := hypotheses |>.map (fun (h,vars) => ((h,vars), List.flatten vars.1 ++ vars.2))
                             |> computeSCC
                             |>.map (@enumDependencySatisfyingOrderings _ _ ⟨fun (a,_) (b,_) => BEq.beq a b⟩ _ _ _ _)
  enumSchedulesChunked [`ets,`acts,`R,`ns,`T,`T1,`T2,`E1,`x1,`x2] components [`V]

def countChecks (schd : List (PreScheduleStep α β)) : Nat :=
  schd.foldl (fun acc step => match step with | PreScheduleStep.Checks cs => acc + cs.length | _ => acc) 0

/-
Sorts all the schedules according to the used ordering, so we can examine them.
-/
#guard_msgs(drop info) in
#eval exampleEnumSchedulesChunked.take 200000 |>.mergeSort (le := fun a b =>
  match compare (countChecks a) (countChecks b) with
  | .eq => a.length < b.length
  | .gt => false
  | .lt => true)
