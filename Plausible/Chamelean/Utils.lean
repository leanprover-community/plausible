
import Lean

import Batteries.Data.List.Basic

open Lean Meta LocalContext Std


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
    |>.setBool `pp.explicit false


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

/-- `replicateM n act` performs the action `act` for `n` times, returning a list of results. -/
def replicateM [Monad m] (n : Nat) (action : m α) : m (List α) :=
  match n with
  | 0 => pure []
  | n + 1 => do
    let x ← action
    let xs ← replicateM n action
    pure (x :: xs)

/-- Converts a list of options to an optional list
    (akin to Haskell's `sequence`) -/
def List.sequence (xs : List (Option α)) : Option (List α) :=
  List.traverse id xs

/-- Helper function for splitting a list of triples into a triple of lists -/
def splitThreeLists (abcs : List (α × β × γ)) : List α × List β × List γ :=
  match abcs with
  | [] => ([], [], [])
  | (a,b,c) :: xs =>
    let (as, bs, cs) := splitThreeLists xs
    (a::as, b::bs, c::cs)
