/-
Copyright (c) 2025 Ernest Ng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ernest Ng
-/
import Lean
open Lean Elab Command Meta Term Parser

/-!
# Combinators for `TSyntax`

This file contains combinators for creating `TSyntax` terms and monadic expressions (`doElem`s),
which are used when deriving the code for generators.


## References
* https://leanprover-community.github.io/lean4-metaprogramming-book/main/05_syntax.html

-/

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
