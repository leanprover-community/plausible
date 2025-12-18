
module

public import Lean

open Lean Meta LocalContext Std

public section

/-- A variable along with its fully elaborated type.
Will likely be replaced by variables directly living in `Expr` at some point. -/
structure TypedVar where
  /-- The variable name -/
  var : Name
  /-- The variable's fully elaborated type. -/
  type : Expr
  deriving Repr, BEq

/-- `containsNonTrivialFuncApp e inductiveRelationName` determines whether `e` contains a non-trivial function application
    (i.e. a function application where the function name is *not* the same as `inductiveRelationName`,
    and where the function is also *not* a constructor of an inductive data type) -/
def containsNonTrivialFuncApp (e : Expr) (inductiveRelationName : Name) : MetaM Bool := do
  -- Helper function to check whether a sub-term is a non-trivial function application
  let rec checkSubTerm (subExpr : Expr) : MetaM Bool :=
    if subExpr.isApp then
      let fn := subExpr.getAppFn
      if fn.isConst then
        let constName := fn.constName!
        if constName.getRoot != inductiveRelationName.getRoot then do
          let info ← getConstInfo constName
          return !info.isCtor
        else
          return false
      else
        return false
    else
      return false

  match e with
  | (.app (.app (.app (.const ``OfNat.ofNat _) _) (.lit _)) _) => return false
  | .app f arg =>
    if (← checkSubTerm f)
      then return true
    else
      checkSubTerm arg
  | .lam _ _ body _ => checkSubTerm body
  | .forallE _ _ body _ => checkSubTerm body
  | .letE _ _ value body _ => do
    if (← checkSubTerm value) then
      return true
    else
      checkSubTerm body
  | .mdata _ expr => checkSubTerm expr
  | .proj _ _ struct => checkSubTerm struct
  | .lit _ => return false
  | _ => return false


/-- `Monad` instance for List.
    Note that:
    - The Lean standard library does not have a Monad instance for List (see https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Option.20do.20notation.20regression.3F.html#231433226)
    - MathLib4 does have a Monad instance for List, but we wish to avoid having Chamelean rely on Mathlib
    as a dependency, so we reproduce instance here instead. -/
instance : Monad List where
  pure x := [x]
  bind xs f := xs.flatMap f

/-- `Alternative` instance for List.
     - MathLib4 does have an `Alternative` instance for List, but we wish to avoid having Chamelean rely on Mathlib
    as a dependency, so we reproduce the instance here instead. -/
instance : Alternative List where
  failure := List.nil
  orElse l l' := List.append l (l' ())

/-- Decomposes an array `arr` into a pair `(xs, x)`
   where `xs = arr[0..=n-2]` and `x = arr[n - 1]` (where `n` is the length of `arr`).
   - If `arr` is empty, this function returns `none`
   - If `arr = #[x]`, this function returns `some (#[], x)`
   - Note: this function is morally the same as `unsnoc` in the Haskell's `Data.List` library -/
def Array.unsnoc (arr : Array α) : Option (Array α × α) :=
  match arr.back? with
  | none => none
  | some a => some (arr.extract 0 (arr.size - 1), a)

/-- Takes a type expression `tyExpr` representing an arrow type, and returns an array of type-expressions
    where each element is a component of the arrow type.
    For example, `getComponentsOfArrowType (A -> B -> C)` produces `#[A, B, C]`. -/
partial def getComponentsOfArrowType (tyExpr : Expr) : MetaM (Array Expr) := do
  let rec helper (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    match e with
    | Expr.forallE name domain body _ =>
      withLocalDeclD name domain fun fvar => do
        helper (body.instantiate1 fvar) (acc.push domain)
    | e => return acc.push e
  helper tyExpr #[]

/-- Variant of `List.flatMap` where the function `f` expects two arguments:
    the current argument of the list and all *other* elements in the list (in order) excluding the current one.
    Intuitively, this is a version of `flatMap` where each element is processed
    by `f` with contextual information from the other elements. -/
def flatMapWithContext (xs : List α) (f : α → List α → List β) : List β :=
  aux [] xs
    where
      aux (acc : List α) (l : List α) : List β :=
        match l with
        | [] => []
        | hd :: tl => f hd (List.reverse acc ++ tl) ++ aux (hd :: acc) tl

/-- Variant of `flatMapWithContext` where the function `f` is monadic
    and returns `m (List β)` -/
def flatMapMWithContext [Monad m] (xs : List α) (f : α → List α → m (List β)) : m (List β) :=
  aux [] xs
    where
      aux (acc : List α) (l : List α) : m (List β) :=
        match l with
        | [] => return []
        | hd :: tl => do
            let xs ← f hd (List.reverse acc ++ tl)
            let ys ← aux (hd :: acc) tl
            return (xs ++ ys)


/-- Variant of `List.filterMap` where the function `f` also takes in the index of the
    current element in the list -/
def filterMapWithIndex (f : Nat → α → Option β) (xs : List α) : List β :=
  xs.zipIdx.filterMap (Function.uncurry $ flip f)

/-- Variant of `List.filterMapM` where the function `f` also takes in the index of the
    current element in the list -/
def filterMapMWithIndex [Monad m] (f : Nat → α → m (Option β)) (xs : List α) : m (List β) :=
  xs.zipIdx.filterMapM (Function.uncurry $ flip f)

/-- Variant of `List.filter` where the predicate `p` takes in the index of
    the element as its first argument -/
def filterWithIndex (p : Nat → α → Bool) (xs : List α) : List α :=
  Prod.fst <$> xs.zipIdx.filter (Function.uncurry $ flip p)

/-- `mkInitialContextForInductiveRelation inputTypes inputNames`
    creates the initial `LocalContext` where each `(x, τ)` in `Array.zip inputTypes inputNames`
    is given the declaration `x : τ` in the resultant context.

    This function returns a quadruple containing `inputTypes`, `inputNames` represented as an `Array` of `Name`s,
    the resultant `LocalContext` and a map from original names to freshened names. -/
def mkInitialContextForInductiveRelation (inputTypes : Array Expr) (inputNames : Array Name) : MetaM (Array Expr × Array Name × LocalContext × HashMap Name Name) := do
  let localDecls := inputNames.zip inputTypes
  withLocalDeclsDND localDecls $ fun exprs => do
    let mut nameMapBindings := #[]
    let mut localCtx ← getLCtx
    for currentName in inputNames do
      let freshName := getUnusedName localCtx currentName
      localCtx := renameUserName localCtx currentName freshName
      nameMapBindings := nameMapBindings.push (currentName, freshName)
    let nameMap := HashMap.ofList (Array.toList nameMapBindings)
    return (exprs, inputNames, localCtx, nameMap)


/-- Looks up the user-facing `Name` corresponding to an `FVarId` in a specific `LocalContext`
    - Panics if `fvarId` is not in the `LocalContext` -/
def getUserNameInContext! (lctx : LocalContext) (fvarId : FVarId) : Name :=
  (lctx.get! fvarId).userName

/-- Helper function for setting delaborator options
  (used in `delabExprInLocalContext`, which calls `PrettyPrinter.delab`)

  - Note: this function forces delaborator to pretty-print pattern cases in prefix position,
    as opposed to using postfix dot-notation, which is not allowed in pattern-matches -/
def setDelaboratorOptions (opts : Options) : Options :=
  opts.setBool `pp.fieldNotation false
    |>.setBool `pp.notation true
    |>.setBool `pp.instances true
    |>.setBool `pp.instanceTypes false
    |>.setBool `pp.all false
    |>.setBool ``pp.explicit true


/-- Delaborates an `Expr` in a `LocalContext` to a `TSyntax term` -/
def delabExprInLocalContext (lctx : LocalContext) (e : Expr) : MetaM (TSyntax `term) :=
  withOptions setDelaboratorOptions $
    withLCtx lctx #[] do
      PrettyPrinter.delab e

/-- Determines if an instance of the typeclass `className` exists for a particular `type`
    represented as an `Expr`. Under the hood, this tries to synthesize an instance of the typeclass for the type.

    Example:
    ```
    #eval hasInstance `Repr (Expr.const `Nat []) -- returns true
    ```
-/
def hasInstance (className : Name) (type : Expr) : MetaM Bool := do
  let classType ← mkAppM className #[type]
  Option.isSome <$> synthInstance? classType


/-- Determines if a constructor for an inductive relation is *recursive*
    (i.e. the constructor's type mentions the inductive relation)
    - Note: this function only considers constructors with arrow types -/
def isConstructorRecursive (inductiveName : Name) (ctorName : Name) : MetaM Bool := do
  let ctorInfo ← getConstInfo ctorName
  let ctorType := ctorInfo.type

  let componentsOfArrowType ← getComponentsOfArrowType ctorType
  match componentsOfArrowType.unsnoc with
  | some (hypotheses, _) =>
    for hyp in hypotheses do
      if hyp.getAppFn.constName == inductiveName then
        return true
    return false
  | none => throwError "constructors with non-arrow types are not-considered to be recursive"

def foldlWithIndex (f : α → Nat → β → β) (init : β) (l : List α) : β :=
  let rec aux (idx : Nat) (acc : β) (l : List α) :=
    match l with
    | [] => acc
    | a :: l' => aux (idx + 1) (f a idx acc) l'
  aux 0 init l

/-- Recursively collects all free variables in an expression and counts their occurrences.
    If skipArgIndex is provided and the top-level expression is an application,
    skips the argument at that index when counting occurrences. -/
partial def collectFVarOccurrences (e : Expr) (skipArgIndex : Option Nat := none) : FVarIdMap Nat :=
  let rec aux (expr : Expr) (acc : FVarIdMap Nat) (isTopLevel : Bool) : FVarIdMap Nat :=
    match expr with
    | .fvar fvarId => acc.insert fvarId (acc.getD fvarId 0 + 1)
    | .app f arg =>
      if isTopLevel then
        -- Handle top-level application with potential argument skipping
        let args := expr.getAppArgs
        Id.run do
          let mut result := acc
          for h : i in [:args.size] do
            if some i != skipArgIndex then
              result := aux args[i] result false
          result
      else
        aux arg (aux f acc false) false
    | .lam _ domain body _ => aux body (aux domain acc false) false
    | .forallE _ domain body _ => aux body (aux domain acc false) false
    | .letE _ type value body _ => aux body (aux value (aux type acc false) false) false
    | .mdata _ expr => aux expr acc isTopLevel
    | .proj _ _ struct => aux struct acc false
    | _ => acc
  aux e {} true

/-`collectUnmatchableSubterms` traverses an expression from top down until it finds anything except a constructor application
or a variable or an inductive. It collects all such subterms. These subterms we cannot match on during unifications so we
turn them later into equality constraints. -/
partial def collectUnmatchableSubterms (e : Expr) : MetaM (List Expr) := do
  let eType ← inferType e
  if eType.isSort then return []
  match e with
  | .app .. | .const .. => do
    let (f, args) := e.getAppFnArgs
    let inf ← getConstInfo f
    if inf.isDefinition then
      return [e]
    else
      args.foldlM (fun acc arg => (· ++ acc) <$> collectUnmatchableSubterms arg) []
  | .fvar .. => return []
  | _ => return [e] -- If it is not an application or a const, it is also not matchable, so we
                    -- should also flatten it out.

/-`collectUnmatchableProperSubterms` traverses an expression from top down (ignoring the head, which is a hypothesis that does not need to be
matched on) until it finds anything except a constructor application or a variable or an inductive. It collects all such subterms. These
subterms we cannot match on during unifications so we turn them later into equality constraints.-/
partial def collectUnmatchableProperSubterms (e : Expr) : MetaM (List Expr) :=
  match e with
  | .app .. => do
    let args := e.getAppArgs
    args.foldlM (fun acc arg => (· ++ acc) <$> collectUnmatchableSubterms arg) []
  | _ => return []

/-- Looks up a key in a list and returns the value along with the list without that entry -/
def lookupAndRemove [BEq α] (key : α) (list : List (α × β)) : Option (β × List (α × β)) :=
  let rec aux (acc : List (α × β)) : List (α × β) → Option (β × List (α × β))
  | [] => none
  | (k, v) :: rest =>
    if key == k then
      some (v, acc ++ rest)
    else
      aux ((k, v) :: acc) rest
  aux [] list

/-- Recursively replaces expressions in an expression tree using a replacement map,
    removing each replacement after it's used.
    If skipArgIndex is provided and the top-level expression is an application,
    skips replacement in the argument at that index. -/
partial def replaceExprsRecursivelyOnce (e : Expr) (replacements : List (Expr × Expr)) (skipArgIndex : Option Nat := none) : Expr :=
  let (result, _) := StateT.run (aux e true) replacements
  result
where
  aux (expr : Expr) (isTopLevel : Bool) : StateT (List (Expr × Expr)) Id Expr := do
    let currentReplacements ← get
    -- First check if this expression should be replaced
    match lookupAndRemove expr currentReplacements with
    | some (replacement, remainingReplacements) =>
      -- Update state with remaining replacements
      set remainingReplacements
      return replacement
    | none =>
      -- If not, recursively process subexpressions
      match expr with
      | .app f arg =>
        if isTopLevel then
          -- Handle top-level application with potential argument skipping
          let (fn, args) := expr.getAppFnArgs
          let args' ← args.toList.mapIdxM (fun i arg =>
            match skipArgIndex with
            | some skipIdx => if i == skipIdx then return arg else aux arg false
            | none => aux arg false)
          return mkAppN (mkConst fn []) args'.toArray
        else do
          let f' ← aux f false
          let arg' ← aux arg false
          return .app f' arg'
      | .lam name domain body bi => do
        let domain' ← aux domain false
        let body' ← aux body false
        return .lam name domain' body' bi
      | .forallE name domain body bi => do
        let domain' ← aux domain false
        let body' ← aux body false
        return .forallE name domain' body' bi
      | .letE name type value body nonDep => do
        let type' ← aux type false
        let value' ← aux value false
        let body' ← aux body false
        return .letE name type' value' body' nonDep
      | .mdata data expr => do
        let expr' ← aux expr isTopLevel
        return .mdata data expr'
      | .proj name idx struct => do
        let struct' ← aux struct false
        return .proj name idx struct'
      | _ => return expr

/--info: Lean.Expr.app (Lean.Expr.const `f []) (Lean.Expr.const `g [])-/
#guard_msgs() in
#eval replaceExprsRecursivelyOnce (.app (.const `f []) (.app (.const `f2 []) (.const `a []))) [((.app (.const `f2 []) (.const `a [])),(.const `g []))]

/-- `replicateM n act` performs the action `act` for `n` times, returning a list of results. -/
def replicateM [Monad m] (n : Nat) (action : m α) : m (List α) :=
  match n with
  | 0 => pure []
  | n + 1 => do
    let x ← action
    let xs ← replicateM n action
    pure (x :: xs)


def traverse [Applicative F] (f : α → F β) : List α → F (List β)
  | [] => pure []
  | x :: xs => List.cons <$> f x <*> traverse f xs


/-- Converts a list of options to an optional list
    (akin to Haskell's `sequence`) -/
def sequence (xs : List (Option α)) : Option (List α) := traverse id xs

/-- Helper function for splitting a list of triples into a triple of lists -/
def splitThreeLists (abcs : List (α × β × γ)) : List α × List β × List γ :=
  match abcs with
  | [] => ([], [], [])
  | (a,b,c) :: xs =>
    let (as, bs, cs) := splitThreeLists xs
    (a::as, b::bs, c::cs)
