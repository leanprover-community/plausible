
import Lean
import Batteries.Data.List.Basic

open Lean Meta

/-- Decomposes an array `arr` into a pair `(xs, x)`
   where `xs = arr[0..=n-2]` and `x = arr[n - 1]` (where `n` is the length of `arr`).
   - If `arr` is empty, this function returns `none`
   - If `arr = #[x]`, this function returns `some (#[], x)`
   - Note: this function is the same as `unsnoc` in the Haskell's `Data.List` library -/
def splitLast? (arr : Array α) : Option (Array α × α) :=
  match arr.back? with
  | none => none
  | some a => some (arr.extract 0 (arr.size - 1), a)

/-- Takes a universally-quantified expression of the form `∀ (x1 : τ1) … (xn : τn), body`
    and returns the pair `(#[(x1, τ1), …, (xn, τn)], body)` -/
partial def extractForAllBinders (e : Expr) : Array (Name × Expr) × Expr :=
  let rec go (e : Expr) (acc : Array (Name × Expr)) :=
    match e with
    | Expr.forallE n t b _ =>
      if b.hasLooseBVar 0 then
        go (b.instantiate1 (mkFVar ⟨n⟩)) (acc.push (n, t))
      else
        (acc, e)
    | _ => (acc, e)
  go e #[]

/-- Takes a type expression `tyexpr` representing an arrow type, and returns an array of type-expressions
    where each element is a component of the arrow type.
    For example, `getComponentsOfArrowType (A -> B -> C)` produces `#[A, B, C]`. -/
partial def getComponentsOfArrowType (tyexpr : Expr) : MetaM (Array Expr) := do
  let rec helper (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    match e with
    | Expr.forallE _ domain body _ =>
      helper (body.instantiate1 (mkFVar ⟨`x⟩)) (acc.push domain)
    | e => return acc.push e
  helper tyexpr #[]

/-- Decomposes a universally-quantified type expression whose body is an arrow type
    (i.e. `∀ (x1 : τ1) … (xn : τn), Q1 → … → Qn → P`), and returns a triple of the form
    `(#[(x1, τ1), …, (xn, τn)], Q1 → … → Qn → P, #[Q1, …, Qn, P])`.
    - The 2nd component is the body of the forall-expression
    - The 3rd component is an array containing each subterm of the arrow type -/
def decomposeType (e : Expr) : MetaM (Array (Name × Expr) × Expr × Array Expr) := do
  let (binder, exp) := extractForAllBinders e
  let tyexp ← getComponentsOfArrowType exp
  return (binder, exp, tyexp)

/-- Looks up the user-facing `Name` corresponding to an `FVarId` in a specific `LocalContext` -/
def getUserNameInContext (lctx : LocalContext) (fvarId : FVarId) : Name :=
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

  let (_, _, type_exprs_in_arrow_type) ← decomposeType ctorType
  match splitLast? type_exprs_in_arrow_type with
  | some (hypotheses, _conclusion) =>
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
