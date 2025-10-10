
import Std.Data.HashMap
import Lean.Expr
import Lean.Exception
import Plausible.Chamelean.Idents


open Lean Idents Elab


-- Adapted from "Generating Good Generators for Inductive Relations", POPL '18
-- and the QuickChick source code
-- https://github.com/QuickChick/QuickChick/blob/internal-rewrite/plugin/newUnifyQC.ml.cppo


/-- An `Unknown` is a Lean `Name` correpsonding to a variable -/
abbrev Unknown := Name
deriving instance Repr, BEq for Unknown

/-- `Ord` instance for `Unknown`s
    (which just uses the `Ord` instance for their underlying string representations) -/
instance : Ord Unknown where
  compare u1 u2 := compare u1.toString u2.toString

/-- *Ranges* represent sets of potential values that a variable can take on during generation -/
inductive Range
  /-- Undefined value, parameterized by a type `ty` (represented as a Lean `Expr`)
      - The `unknowns` we want to generate (e.g. a `Tree` in the BST example) start out
        with `Undef` ranges -/
  | Undef (ty : Expr)

  /-- A `Fixed` range means the corresponding unknown's value serves as an input at runtime
     (e.g. `lo` and `hi` in the BST example) -/
  | Fixed

  /-- The `Range` of an `Unknown` can be another `Unknown` (to facilitate sharing)-/
  | Unknown (u : Unknown)

  /-- A `Range` can be a constructor `C` fully applied to a list of `Range`s -/
  | Ctor (ctor : Name) (rs : List Range)
  deriving Repr, Inhabited, BEq

/-- A `Pattern` is either an unknown or a fully-applied constructor -/
inductive Pattern
  | UnknownPattern : Unknown -> Pattern
  | CtorPattern : Name -> List Pattern -> Pattern
  deriving Repr, Inhabited, BEq, Ord

/-- A *constructor expression* (`ConstructorExpr`) is either a variable (represented by its `Name`),
    or a constructor (identified by its `Name`) applied to some list of arguments,
    each of which are themselves `ConstructorExpr`s

    - Note: this type is isomorphic to `Pattern`, but we define a separate type to avoid confusing
    `ConstructorExpr` with `Pattern` since they are used in different parts of the algorithm -/
inductive ConstructorExpr
  | Unknown : Name -> ConstructorExpr
  | Ctor : Name -> List ConstructorExpr -> ConstructorExpr
  | FuncApp : Name -> List ConstructorExpr -> ConstructorExpr
  deriving Repr, BEq, Inhabited, Ord

/-- Converts a `ConstructorExpr` to a Lean `Expr` -/
partial def constructorExprToExpr (ctorExpr : ConstructorExpr) : Expr :=
  match ctorExpr with
  | .Unknown name => mkConst name
  | .Ctor ctorName ctorArgs =>
    mkAppN (mkConst ctorName) (constructorExprToExpr <$> ctorArgs.toArray)
  | .FuncApp funcName ctorArgs =>
    mkAppN (mkConst funcName) (constructorExprToExpr <$> ctorArgs.toArray)

/-- `ToExpr` instance for `ConstructorExpr` -/
instance : ToExpr ConstructorExpr where
  toExpr := constructorExprToExpr
  toTypeExpr := mkConst ``Expr

/-- Converts a `ConstructorExpr` to a Lean `TSyntax term` -/
partial def constructorExprToTSyntaxTerm (ctorExpr : ConstructorExpr) : MetaM (TSyntax `term) :=
  match ctorExpr with
  | .Unknown name => `($(mkIdent name))
  | .Ctor ctorName ctorArgs
  | .FuncApp ctorName ctorArgs => do
    let argTerms ← ctorArgs.toArray.mapM constructorExprToTSyntaxTerm
    `($(mkIdent ctorName) $argTerms:term*)


/-- Converts a `Pattern` to an equivalent `ConstructorExpr` -/
partial def constructorExprOfPattern (pattern : Pattern) : ConstructorExpr :=
  match pattern with
  | .UnknownPattern u => .Unknown u
  | .CtorPattern ctorName args => .Ctor ctorName (constructorExprOfPattern <$> args)

/-- Converts a `ConstructorExpr` to an equivalent `Pattern` -/
partial def patternOfConstructorExpr (ctorExpr : ConstructorExpr) : Option Pattern :=
  match ctorExpr with
  | .Unknown u => some $ .UnknownPattern u
  | .Ctor ctorName args => .CtorPattern ctorName <$> (List.mapM patternOfConstructorExpr args)
  | .FuncApp _ _ => none


/-- An `UnknownMap` maps `Unknown`s to `Range`s -/
abbrev UnknownMap := Std.HashMap Unknown Range

/-- `UnifyState` stores the current state of the unification algorithm -/
structure UnifyState where
  /-- `constraints` is an `UnknownMap` that maps unknowns to ranges -/
  constraints : UnknownMap

  /-- `equalities` keeps track of equalities between unknowns
      that need to be checked -/
  equalities : Std.HashSet (Unknown × Unknown)

  /-- `patterns` contains a list of necessary pattern matches that
      need to be performed -/
  patterns : List (Unknown × Pattern)

  /-- A set of all existing `Unknown`s -/
  unknowns : Std.HashSet Unknown

  /-- The name of the output variable (variable to be generated) -/
  outputName : Name

  /-- The type of the output variable (variable to be generated) -/
  outputType : Expr

  /-- All inputs (top-level arguments) to the generator -/
  inputNames : List Name

  /-- The list of hypotheses in the constructor's type (excluding the constructor's conclusion)
      Each hypothesis is represented as a pair `(constructor name, constructor args)`
      i.e. a constructor name applied to a list of arguments, each of which are `ConstructorExpr`s -/
  hypotheses : List (Name × List ConstructorExpr)

  deriving Repr

/-- Initial (empty) unification state
    - Note that the dummy `outputName` and `outputType` are never used
      (it will be updated when callers invoke the unification algorithm through this monad) -/
def emptyUnifyState : UnifyState :=
  { constraints := ∅,
    equalities := ∅,
    patterns := [],
    unknowns := ∅,
    outputName := `dummyOutput,
    outputType := mkConst `dummyOutputType
    inputNames := []
    hypotheses := [] }

---------------------------------------------------------------
-- `ToMessageData` instances for pretty-printing
---------------------------------------------------------------

/-- Pretty-prints a `Range` as a `MessageData` -/
partial def toMessageDataRange (range : Range) : MessageData :=
  match range with
  | .Undef tyExpr => m!"Undef {tyExpr}"
  | .Ctor c rs =>
    let rendredCtorArgs := toMessageDataRange <$> rs
    m!"Ctor ({c} {rendredCtorArgs})"
  | .Unknown u => m!"Unknown {u}"
  | .Fixed => m!"Fixed"

instance : ToMessageData Range where
  toMessageData := toMessageDataRange

/-- Pretty-prints a `Pattern` as a `MessageData` -/
partial def toMessageDataPattern (p : Pattern) : MessageData :=
  match p with
  | .UnknownPattern u => m!"UnknownPattern {u}"
  | .CtorPattern c ps =>
    let renderedCtorArgs := toMessageDataPattern <$> ps
    m!"CtorPattern ({c} {renderedCtorArgs})"

instance : ToMessageData Pattern where
  toMessageData pattern := toMessageDataPattern pattern

/-- Pretty-prints a `ConstructorExpr` as a `MessageData` -/
partial def toMessageDataConstructorExpr (ctorExpr : ConstructorExpr) : MessageData :=
  match ctorExpr with
  | .Unknown x => m!"Unknown {x}"
  | .Ctor c args =>
    let renderedArgs := toMessageDataConstructorExpr <$> args
    m!"Ctor ({c} {renderedArgs})"
  | .FuncApp f args =>
    let renderedArgs := toMessageDataConstructorExpr <$> args
    m!"FuncApp ({f} {renderedArgs})"

instance : ToMessageData ConstructorExpr where
  toMessageData := toMessageDataConstructorExpr

instance : ToMessageData UnifyState where
  toMessageData unifyState :=
    let constraints := unifyState.constraints.toList
    -- Sort the constraints map based on the ordering of its keys
    let sortedConstraints := List.mergeSort constraints (fun (u1, _) (u2, _) => Ordering.isLE (compare u1 u2))
    let formattedConstraints :=
      sortedConstraints.map $ fun (u, r) => m!"{u} ↦ {r}"
    let equalities :=
      unifyState.equalities.toList.map $ fun (u1, u2) => m!"{u1} = {u2}"
    let patterns :=
      unifyState.patterns.map $ fun (u, pat) => m!"{u} ≡ {pat}"
    let unknowns :=
      unifyState.unknowns.toList.map $ fun u => m!"{u}"

    let hyps := unifyState.hypotheses.map $ fun hyp => m!"{hyp}"

  m!"⟨\n  constraints := \n{formattedConstraints},\n  equalities := {equalities},\n  patterns := {patterns},\n  unknowns := {unknowns}\n, hypotheses := {hyps}\n⟩"



---------------------------------------------------------------
-- Unification monad (fig. 2 in Generating Good Generators)
---------------------------------------------------------------

/-- `UnifyM` is a monad for unification + code generation.
    Note that the definition of `UnifyM` (after unfolding) is:
    ```
    UnifyM α := UnifyState → MetaM (Option (α × UnifyState))
    ```
-/
abbrev UnifyM (α : Type) := StateT UnifyState (OptionT MetaM) α

namespace UnifyM

/-- `update u r` sets the range of the unknown `u` to be `r` -/
def update (u : Unknown) (r : Range) : UnifyM Unit := do
  modify $ fun s =>
    let k := s.constraints
    { s with constraints := k.insert u r }

/-- Applies a function `f` to the `constraints` map stored in `UnifyState`
    - This function allows us to fetch the `constraints` map without needing
      a seperate `get` call inside the State monad -/
def withConstraints (f : UnknownMap → UnifyM α) : UnifyM α := do
  let unifyState ← get
  f unifyState.constraints

/-- Applies a function `f` to the list of `hypotheses` stored in `UnifyState`
    - This function allows us to fetch the `hypotheses` field without needing
      a seperate `get` call inside the State monad -/
def withHypotheses (f : List (Name × List ConstructorExpr) → UnifyM α) : UnifyM α := do
  let unifyState ← get
  f unifyState.hypotheses

/-- Applies a function `f` to the set of `unknowns` stored in `UnifyState`
    - This function allows us to fetch the `hypotheses` field without needing
      a seperate `get` call inside the State monad -/
def withUnknowns (f : Std.HashSet Unknown → UnifyM α) : UnifyM α := do
  let unifyState ← get
  f unifyState.unknowns

/-- Directly applies a function `f` to the `constraint` map in the state  -/
def modifyConstraints (f : UnknownMap → UnknownMap) : UnifyM Unit :=
  modify $ fun s => { s with constraints := f s.constraints }

  /-- Batches multiple constraint updates together for performance  -/
def updateMany (updates : List (Unknown × Range)) : UnifyM Unit :=
  modifyConstraints $ fun constraints =>
    updates.foldl (fun acc (u, r) => acc.insert u r) constraints

/-- Registers a new equality check between unknowns `u1` and `u2` -/
def registerEquality (u1 : Unknown) (u2 : Unknown) : UnifyM Unit :=
  modify $ fun s =>
    let eqs := s.equalities
    { s with equalities := eqs.union {(u1, u2)} }

/-- Adds a new pattern match -/
def addPattern (u : Unknown) (p : Pattern) : UnifyM Unit :=
  modify $ fun s =>
    let ps := s.patterns
    { s with patterns := (u, p) :: ps }

/-- Produces a fresh unknown that is guaranteed not to be in the
    existing set of `unknowns` -/
def freshUnknown (unknowns : Std.HashSet Unknown) : Unknown :=
  let existingNames := unknowns.toArray
  genFreshName existingNames `u

/-- Produces and registers a new unknown in the `UnifyState` -/
def registerFreshUnknown : UnifyM Unknown := do
  modifyGet $ fun s =>
    let us := s.unknowns
    let u := freshUnknown us
    (u, { s with unknowns := us.union { u } })

/-- Inserts an unknown `u` into the set of existing `unknowns` in `UnifyState` -/
def insertUnknown (u : Unknown) : UnifyM Unit := do
  modify $ fun s => { s with unknowns := s.unknowns.insert u}

/-- Runs a `UnifyM` computation and discards the resulting state,
    with the result returned in the `MetaM` monad as an `Option` -/
def runInMetaM (action : UnifyM α) (st : UnifyState) : MetaM (Option α) := do
  OptionT.run (StateT.run' action st)

/-- Runs a `UnifyM α` to something in `MetaM`, keeping the unification state. -/
def runUnifyM (action : UnifyM α) (st : UnifyState) : MetaM (Option (α × UnifyState)) := do
  OptionT.run (StateT.run action st)

/-- Finds the `Range` corresponding to an `Unknown` `u` in the
    `UnknownMap` `k`, returning an informative error message if `u ∉ k.keys` -/
def findCorrespondingRange (k : UnknownMap) (u : Unknown) : UnifyM Range :=
  match k[u]? with
  | some r => return r
  | none => throwError m!"unable to find unknown {u} in UnknownMap {k.toList}"

/-- Determines if an unknown `u` has a `Range` of `Undef τ` for some type `τ`
    in the constraints map -/
def hasUndefRange (u : Unknown) : UnifyM Bool := do
  UnifyM.withConstraints (fun k => do
    let r ← findCorrespondingRange k u
    match r with
    | .Undef _ => return true
    | _ => return false)

/-- Determines whether a `Range` is fixed with respect to the constraint map `k` -/
partial def hasFixedRange (k : UnknownMap) (r : Range) : UnifyM Bool := do
  match r with
  | .Undef _ => return false
  | .Fixed => return true
  | .Unknown u => do
    let range ← findCorrespondingRange k u
    hasFixedRange k range
  | .Ctor _ rs => rs.allM (hasFixedRange k)

/-- `findUnknownsWithUndefRanges unknowns` returns all `u ∈ unknowns`
    such that `u ↦ Undef τ` for some type `τ` in the `constraints` map stored within `UnifyState` -/
def findUnknownsWithUndefRanges (unknowns : List Unknown) : UnifyM (List Unknown) := do
  let state ← get
  let k := state.constraints
  List.foldlM (fun acc u => do
    let r ← findCorrespondingRange k u
    match r with
    | .Undef _ => return (u :: acc)
    | _ => return acc) [] unknowns

/-- Updates the `constraint` map so that for each `u ∈ unknowns`,
    we have the binding `u ↦ Fixed` in the `UnknownMap` `constraints`
    - Note: this doesn't handle chains of `Unknown`s in `constraints` -/
def fixRanges (unknowns : List Unknown) : UnifyM Unit := do
  updateMany (unknowns.zip (List.replicate unknowns.length .Fixed))

/-- `fixRangeHandleUnknownChains u` updates the `constraint` map
    so that we have the binding `u ↦ Fixed` in the `UnknownMap` `constraints`
    - This handles chains of `Unknown`s in the `UnknownMap`,
      i.e. cases where `u ↦ Unknown u'` where `u'` is another key in
      the `UnknownMap` (in this case, we recursively fix
      the range corresponding to `u'`)

    - This function corresponds to `fixVariable` / `fixRange` in the QuickChick codebase -/
partial def fixRangeHandleUnknownChains (u : Unknown) : UnifyM Unit := do
  let s ← get
  let k := s.constraints
  let r ← findCorrespondingRange k u
  fixRange u r
    where
      /-- `fixRange u r` updates the binding for `u` `UnknownMap`
            so that corresponding range is `Fixed` if `r`
            is not already `Fixed` -/
      fixRange (u : Unknown) (r : Range) : UnifyM Unit :=
        match r with
        | .Fixed => return ()
        | .Undef _ => update u .Fixed
        | .Unknown u' => do
          let s ← get
          let r' ← findCorrespondingRange s.constraints u'
          fixRange u' r'
        | .Ctor _ rs =>
          for range in rs do
            fixRange `unusedParameter range

/--`findCanonicalUnknown k u` finds the *canonical* representation of the unknown `u` based on the `ConstraintMap` `k`.
    Specifically:
    - If `u ↦ Unknown u'` in `k`, then we recursively look up the canonical representation of `u'` by traversing
      the unification graph formed by the `constraints` map in `UnifyState`
    - If `u ↦ r` (where `r` is any `Range` that is not some `Unknown`), then `u` is its own canonical representation
    - If `u ∉ k`, then we just return `u` as is.
    - This function is used to handle cases in `constraints` where an unknown maps to another unknown.
    - Note: this function corresponds to `correct_var` in the QuickChick code.  -/
partial def findCanonicalUnknown (k : UnknownMap) (u : Unknown) : UnifyM Unknown :=
  try (do
    let r ← UnifyM.findCorrespondingRange k u
    match r with
    | .Unknown u' => findCanonicalUnknown k u'
    | _ => return u)
catch _ => return u

/-- `updateConstructorArg k ctorArg` uses the `UnknownMap` `k` to rewrite any unknowns that appear in the
    `ConstructorExpr` `ctorArg`, substituting each `Unknown` with its canonical representation
    (determined by calling `updateUnknown`)
    - See `updateHypothesesWithUnificationResult` for an example of how this function is used.
    - Note: this function corresponds to `correct_rocq_constr` in the QuickChick code. -/
partial def updateConstructorArg (k : UnknownMap) (ctorArg : ConstructorExpr) : UnifyM ConstructorExpr := do
  match ctorArg with
  | .Unknown arg =>
    let canonicalUnknown ← findCanonicalUnknown k arg
    if arg != canonicalUnknown then
      return (.Unknown canonicalUnknown)
    else
      return (.Unknown arg)
  | .Ctor ctorName args
  | .FuncApp ctorName args =>
    let updatedArgs ← args.mapM (updateConstructorArg k)
    return (.Ctor ctorName updatedArgs)

/-- `updatePattern k p` uses the `UnknownMap` `k` to rewrite any unknowns that appear in the
    `Pattern` `p`, substituting each `Unknown` with its canonical representation
    (determined by calling `updateUnknown`)
  - Note: this function corresponds to `correct_pat` in the QuickChick code -/
partial def updatePattern (k : UnknownMap) (p : Pattern) : UnifyM Pattern := do
  match p with
  | .UnknownPattern u => return .UnknownPattern (← findCanonicalUnknown k u)
  | .CtorPattern c args => do
    let updatedArgs ← args.mapM (updatePattern k)
    return .CtorPattern c updatedArgs

/-- Extends the current state with the contents of the fields in `newState`
    (Note that the `outputName` and `outputType` of `newStates` are used) -/
def extendState (newState : UnifyState) : UnifyM Unit := do
  modify $ fun s => { s with
    constraints := s.constraints.union newState.constraints
    equalities := s.equalities.union newState.equalities
    patterns := s.patterns ++ newState.patterns
    unknowns := s.unknowns.union newState.unknowns
    outputName := newState.outputName
    outputType := newState.outputType
    inputNames := s.inputNames ++ newState.inputNames
    hypotheses := s.hypotheses ++ newState.hypotheses
  }


/-- Converts an array of `ConstructorExpr`s to one single `TSyntaxArray term`-/
partial def convertConstructorExprsToTSyntaxTerms (ctorExprs : Array ConstructorExpr) : UnifyM (TSyntaxArray `term) :=
  ctorExprs.mapM (fun ctorExpr => do
    match ctorExpr with
    | .Unknown u => `($(Lean.mkIdent u))
    | .Ctor c args
    | .FuncApp c args =>
      let argTerms ← convertConstructorExprsToTSyntaxTerms args.toArray
      `($(mkIdent c) $argTerms*))

/-- Accumulates all the `Unknown`s in a `ConstructorExpr` -/
def collectUnknownsInConstructorExpr (ctorExpr : ConstructorExpr) : List Unknown :=
  match ctorExpr with
  | .Unknown u => [u]
  | .Ctor c args
  | .FuncApp c args =>
    c :: List.flatMap collectUnknownsInConstructorExpr args

mutual
  /-- Evaluates a `Range`, returning a `ConstructorExpr`. Note that if the
      `Range` is `Fixed` or `Undef`, we return `none` (via `failure`). -/
  partial def evaluateRange (r : Range) : UnifyM ConstructorExpr := do
    match r with
    | .Ctor c args => do
      let args' ← List.mapM evaluateRange args
      return (ConstructorExpr.Ctor c args')
    | .Unknown u => evaluateUnknown u
    | .Fixed | .Undef _ =>
      throwError m!"unable to evaluate range {r}"

  /-- Evaluates an `Unknown` based on the bindings in the `UnknownMap`,
      returning a `ConstructorExpr`.

      Precondition: there must not be any cycles of `Unknown`s in the `UnknownMap`. -/
  partial def evaluateUnknown (v : Unknown) : UnifyM ConstructorExpr := do
    withConstraints $ fun k => do
      let r ← findCorrespondingRange k v
      match r with
      | .Undef _ | .Fixed => return ConstructorExpr.Unknown v
      | .Unknown u =>
        (evaluateUnknown u) <|> (return ConstructorExpr.Unknown v)
      | .Ctor c args => do
        let args' ← args.mapM evaluateRange
        return (ConstructorExpr.Ctor c args')
end

/-- Determines whether a `Range` is `Fixed`. If the `Range` is in the form `Unknown u`,
    we check if the range corresponding to `u` in the `UnknownMap` is `Fixed`
    (this handles chains of `Unknowns` in the `UnknownMap`)  -/
partial def isRangeFixed (r : Range) : UnifyM Bool :=
  match r with
  | .Fixed => return true
  | .Undef _ => return false
  | .Unknown u => do
    withConstraints $ fun k => do
      match k[u]? with
      | none => return false
      | some r' => isRangeFixed r'
  | .Ctor _ args => List.allM isRangeFixed args

/-- Determines if an `Unknown` has a `Fixed` `Range` in the `UnknownMap`
    (this handles chains of `Unknowns` in the `UnknownMap`) -/
def isUnknownFixed (u : Unknown) : UnifyM Bool :=
  isRangeFixed (.Unknown u)



end UnifyM

------------------------------------------------------------------
-- Unification algorithm (fig. 3 of Generating Good Generators)
------------------------------------------------------------------


mutual
  /-- Top-level unification function which unifies the ranges mapped to by two unknowns -/
  partial def unify (range1 : Range) (range2 : Range) : UnifyM Unit := do
    match range1, range2 with
    | .Unknown u1, .Unknown u2 =>
      if u1 == u2 then
        return ()
      else UnifyM.withConstraints $ fun k => do
        let r1 ← UnifyM.findCorrespondingRange k u1
        let r2 ← UnifyM.findCorrespondingRange k u2
        unifyR (u1, r1) (u2, r2)
    | c1@(.Ctor _ _), c2@(.Ctor _ _) =>
      unifyC c1 c2
    | .Unknown u1, c2@(.Ctor _ _) =>
      UnifyM.withConstraints $ fun k => do
        let r1 ← UnifyM.findCorrespondingRange k u1
        unifyRC (u1, r1) c2
    | c1@(.Ctor _ _), .Unknown u2 =>
      UnifyM.withConstraints $ fun k => do
        let r2 ← UnifyM.findCorrespondingRange k u2
        unifyRC (u2, r2) c1
    | r1, r2 => throwError "Unable to unify {r1} with {r2}"

  /-- Takes two `(Unknown, Range)` pairs & unifies them based on their `Range`s -/
  partial def unifyR : Unknown × Range → Unknown × Range → UnifyM Unit
    -- If the range of an unknown (e.g. `u1`) is undefined,
    -- we update `u1` to point to the range of `u2`
    | (u1, .Undef _), (u2, _) => UnifyM.update u1 (.Unknown u2)
    | (u1, _), (u2, .Undef _) => UnifyM.update u2 (.Unknown u1)
    | (_, u1'@(.Unknown _)), (u2, _) => unify u1' (.Unknown u2)
    | (u1, _), (_, u2'@(.Unknown _)) => unify (.Unknown u1) u2'
    | (_, c1@(.Ctor _ _)), (_, c2@(.Ctor _ _)) => unifyC c1 c2
    | (u1, .Fixed), (u2, .Fixed) => do
      -- Assert that whatever the values of `u1` and `u2` are, they are equal
      -- Record this equality check using `equality`, then update `u1`'s range to the other
      UnifyM.registerEquality u1 u2
      UnifyM.update u1 (.Unknown u2)
    | (u1, .Fixed), (_, c2@(.Ctor _ _)) => handleMatch u1 c2
    | (_, c1@(.Ctor _ _)), (u2, .Fixed) => handleMatch u2 c1

  /-- Unifies two `Range`s that are both constructors -/
  partial def unifyC (r1 : Range) (r2 : Range) : UnifyM Unit :=
    match r1, r2 with
    | .Ctor c1 rs1, .Ctor c2 rs2 =>
      -- Recursively unify each of the constructor arguments
      -- Invariant: all ranges that appear as constructor args contain only constructors & unknowns
      if c1 == c2 && rs1.length == rs2.length then
        for (r1, r2) in (List.zip rs1 rs2) do
          unify r1 r2
      else do
        let st ← get
        let constraints := st.constraints
        throwError m!"unifyC: unable to unify {r1} with {r2}, constraints = {constraints.toList}"
    | _, _ => throwError m!"unifyC: unable to unify r1 = {r1}, r2 = {r2} which are not both constructors"

  /-- Unifies an `(Unknown, Range)` pair with a `Range` -/
  partial def unifyRC : Unknown × Range → Range → UnifyM Unit
    | (u1, .Undef _), c2@(.Ctor _ _) => UnifyM.update u1 c2
    | (_, .Unknown u'), c2@(.Ctor _ _) =>
      UnifyM.withConstraints $ fun k => do
        let r ← UnifyM.findCorrespondingRange k u'
        unifyRC (u', r) c2
    | (u, .Fixed), c2@(.Ctor _ _) => handleMatch u c2
    | (_, c1@(.Ctor _ _)), c2@(.Ctor _ _) => unifyC c1 c2
    | (u, r), r' => throwError m!"unifyRC called, unable to unify (unknown {u}, range {r}) with range {r'}"

  /-- Corresponds to `match` in the pseudocode
     (we call this `handleMatch` since `match` is a reserved keyword in Lean) -/
  partial def handleMatch (unknown : Unknown) (range : Range) : UnifyM Unit := do
    match unknown, range with
    | u, .Ctor c rs => do
      let ps ← rs.mapM matchAux
      UnifyM.addPattern u (Pattern.CtorPattern c ps)
    | u, r => throwError m!"handleMatch called, unable to match unknown {u} with range {r} which is not in constructor form"

  /-- `matchAux` traverses a `Range` and converts it into a
      pattern which can be used in a `match` expression -/
  partial def matchAux (range : Range) : UnifyM Pattern := do
    match range with
    | .Ctor c rs => do
      -- Recursively handle ranges
      let ps ← rs.mapM matchAux
      return (.CtorPattern c ps)
    | .Unknown u => UnifyM.withConstraints $ fun k => do
      let r ← UnifyM.findCorrespondingRange k u
      match r with
      | .Undef _ => do
        -- Unknown becomes a pattern variable (bound by the pattern match)
        -- (i.e. the unknown serves as an input at runtime)
        -- We update `u`'s range to be `fixed`
        -- (since we're extracting information out of the scrutinee)
        UnifyM.update u .Fixed
        return (.UnknownPattern u)
      | .Fixed => do
        -- Handles non-linear patterns:
        -- produce a fresh unknown `u'`, use `u'` as the pattern variable
        -- & enforce an equality check between `u` and `u'`
        let u' ← UnifyM.registerFreshUnknown
        UnifyM.registerEquality u' u
        UnifyM.update u' r
        return (.UnknownPattern u')
      | u'@(.Unknown _) => matchAux u'
      | .Ctor c rs => do
        let ps ← rs.mapM matchAux
        return (.CtorPattern c ps)
    | _ => throwError m!"matchAux called with unexpected range {range}"

end
