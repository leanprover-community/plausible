import Lean
import Plausible.Chamelean.Utils
import Batteries.Lean.Expr
open Lean Elab Command Meta Term Parser

/-- `mkLetBind lhs rhsTerms` constructs a monadic let-bind expression of the form
    `let lhs ← e0 e1 … en`, where `rhsTerms := #[e0, e1, …, en]`.
    - Note: `rhsTerms` cannot be empty, otherwise this function throws an exception -/
def mkLetBind (lhs : Ident) (rhsTerms : TSyntaxArray `term) : MetaM (TSyntax `doElem) := do
  let rhsList := rhsTerms.toList
  match rhsList with
  | f :: args =>
    let argTerms := args.toArray
    `(doElem| let $lhs:term ← $f:term $argTerms* )
  | [] => throwError "rhsTerms can't be empty"

/-- `mkTuple components` creates an n-ary tuple from the `Name`s in the list `components`
    - If `components` is Empty, we produce the unit value `()`
    - If `components` has length 1, we just produce one single `Ident` -/
def mkTuple (components : List (Name × Option Expr)) : MetaM (TSyntax `term) := do
  let lctx ← getLCtx
  aux lctx components
  where
  aux (lctx : LocalContext) components : MetaM (TSyntax `term) :=
  match components with
  | [] => `(())
  | [(var, some ty)] => do
    let tSyn ← (withOptions setDelaboratorOptions (delabExprInLocalContext lctx ty))
    `(($(mkIdent var) : $tSyn))
  | [(var, none)] => do
    `($(mkIdent var))
  | (var, oty) :: xs => do
    let tail ← aux lctx xs
    match oty with
    | some type =>
      let tSyn ← withOptions setDelaboratorOptions (delabExprInLocalContext lctx type)
      `( (($(mkIdent var):term : $tSyn), $tail:term ) )
    | none =>
      `( ($(mkIdent var):term, $tail:term))

/-- Constructs a Lean monadic `do` block out of an array of `doSeq`s
    (expressions that appear in the `do` block) -/
def mkDoBlock (doElems : TSyntaxArray `doElem) : MetaM (TSyntax `term) := do
  `(do $[$doElems:doElem]*)

/-- `mkIfExprWithNaryAnd predicates trueBranch elseBranch` creates a *monadic* if-expression
    `if (p1 && … && pn) then $trueBranch else $elseBranch`, where `predicates := #[p1, …, pn]`.
    Note:
    - `trueBranch` and `elseBranch` are `doElem`s, since the if-expr is intended to be part of
    a monadic `do`-block
    - If `predicates` is empty, the expression created is `if True then $trueBranch else $elseBranch` -/
def mkIfExprWithNaryAnd (predicates : Array Term)
  (trueBranch : TSyntax `doElem) (elseBranch : TSyntax `doElem) : MetaM (TSyntax `doElem) := do
  let condition ←
    match predicates.toList with
    | [] => `(True)
    | [p] => pure p
    | p :: ps =>
      List.foldlM (fun acc pred => `($acc && $pred)) (init := p) ps
  `(doElem| if $condition then $trueBranch:doElem else $elseBranch:doElem)

/-- Creates a match expression (represented as a `TSyntax term`),
    where the `scrutinee` is an `Ident` and the `cases` are specified as an array of `matchAlt`s -/
def mkMatchExpr (scrutinee : Ident) (cases : TSyntaxArray ``Term.matchAlt) : MetaM (TSyntax `term) :=
  `(match $scrutinee:ident with $cases:matchAlt*)

/-- Creates a match expression with simultaneous matching on multiple scrutinees.
    The `scrutinees` are provided as an array of `Ident`s and the `cases` are specified
    as an array of `matchAlt`s where each alternative should have patterns corresponding
    to all scrutinees -/
def mkSimultaneousMatch (scrutineeIdents : Array Ident)
  (cases : TSyntaxArray ``Term.matchAlt) : MetaM (TSyntax `term) := do
  let scrutinees ← Array.mapM (fun ident => `(matchDiscr| $ident:ident)) scrutineeIdents
  `(match $[$scrutinees:matchDiscr],* with $cases:matchAlt*)

/-- Variant of `mkMatchExpr` where the `scrutinee` is a `TSyntax term` rather than an `Ident` -/
def mkMatchExprWithScrutineeTerm (scrutinee : TSyntax `term) (cases : TSyntaxArray ``Term.matchAlt) : MetaM (TSyntax `term) :=
  `(match $scrutinee:term with $cases:matchAlt*)

/-- Variant of `mkMatchExpr` where the `scrutinee` is a `TSyntax term`, and the resultant match expression
    is a `doElem` (i.e. it is part of a monadic `do`-block) -/
def mkDoElemMatchExpr (scrutinee : TSyntax `term) (cases : TSyntaxArray ``Term.matchAlt) : MetaM (TSyntax `doElem) :=
  `(doElem| match $scrutinee:term with $cases:matchAlt*)

/-- Converts a `Literal`, the datatype used to store `Nat` and `String` literals in `Lean.Expr` into the corresponding literal `TSyntax`.
    Note, the `Nat` literal will be wrapped in an `OfNat.ofNat` call.
-/
def mkLiteral (l : Literal) : MetaM (TSyntax `term) :=
  match l with
  | .natVal n => `($(Syntax.mkNatLit n))
  | .strVal s => `($(Syntax.mkStrLit s))
