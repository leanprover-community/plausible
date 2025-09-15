-- This file contains various examples of inductive relations.

/-- List membership expressed as an inductive relation:
   `inList x l` means `x ∈ l`. -/
inductive inList : Nat → List Nat → Prop where
| Here : ∀ x l, inList x (x::l)
| There : ∀ x y l, inList x l → inList x (y::l)

/-- A datatype for binary trees -/
inductive Tree where
| Leaf : Tree
| Node : Nat → Tree → Tree → Tree
deriving Repr

/-- `balanced n t` describes whether the tree `t` of height `n` is *balanced*, i.e.
    every path through the tree has length either `n` or `n-1`. -/
inductive balanced : Nat → Tree → Prop where
| B0 : balanced .zero .Leaf
| B1 : balanced (.succ .zero) .Leaf
| BS : ∀ n x l r,
  balanced n l → balanced n r →
  balanced (.succ n) (.Node x l r)

/-- `between lo x hi` means `lo < x < hi` -/
inductive between : Nat -> Nat -> Nat -> Prop where
| BetweenN : ∀ n m, n <= m -> between n (.succ n) (.succ (.succ m))
| BetweenS : ∀ n m o,
  between n m o -> between n (.succ m) (.succ o)

/-- `bst lo hi t` describes whether a tree `t` is a BST that contains values strictly within `lo` and `hi` -/
inductive bst : Nat → Nat → Tree → Prop where
| BstLeaf: ∀ lo hi, bst lo hi .Leaf
| BstNode: ∀ lo hi x l r,
  between lo x hi →
  bst lo x l →
  bst x hi r →
  bst lo hi (.Node x l r)

/-- Base types in the STLC (either Nat or functions) -/
inductive type where
  | Nat : type
  | Fun: type → type → type
  deriving BEq, DecidableEq

/-- Pretty-printer for `type`s -/
def typeToString (ty : type) : String :=
  match ty with
  | .Nat => "ℕ"
  | .Fun τ1 τ2 => s!"{typeToString τ1} → {typeToString τ2}"

/-- Repr instance for `type`s -/
instance : Repr type where
  reprPrec ty _ := typeToString ty

/-- Terms in the STLC extended with naturals and addition -/
inductive term where
  | Const: Nat → term
  | Add: term → term → term
  | Var: Nat → term
  | App: term → term → term
  | Abs: type → term → term
  deriving BEq

/-- Pretty-printer for `term`s -/
def termToString (e : term) : String :=
  match e with
  | .Const n => s!"Const {n}"
  | .Add e1 e2 => s!"({termToString e1} + {termToString e2})"
  | .Var id => s!"Id {id}"
  | .App e1 e2 => s!"({termToString e1} {termToString e2})"
  | .Abs τ e2 => s!"(λ _ : {typeToString τ}. {termToString e2})"

/-- Repr instance for `term`s -/
instance : Repr term where
  reprPrec (e : term) _ := termToString e

/-- `lookup Γ n τ` checks whether the `n`th element of the context `Γ` has type `τ` -/
inductive lookup : List type -> Nat -> type -> Prop where
  | Now : forall τ Γ, lookup (τ :: Γ) .zero τ
  | Later : forall τ τ' n Γ,
      lookup Γ n τ -> lookup (τ' :: Γ) (.succ n) τ

/-- `typing Γ e τ` is the typing judgement `Γ ⊢ e : τ` -/
inductive typing: List type → term → type → Prop where
| TConst : ∀ Γ n,
    typing Γ (.Const n) .Nat
| TAdd: ∀ Γ e1 e2,
    typing Γ e1 .Nat →
    typing Γ e2 .Nat →
    typing Γ (.Add e1 e2) .Nat
| TAbs: ∀ Γ e τ1 τ2,
    typing (τ1::Γ) e τ2 →
    typing Γ (.Abs τ1 e) (.Fun τ1 τ2)
| TVar: ∀ Γ x τ,
    lookup Γ x τ →
    typing Γ (.Var x) τ
| TApp: ∀ Γ e1 e2 τ1 τ2,
    typing Γ e2 τ1 →
    typing Γ e1 (.Fun τ1 τ2) →
    typing Γ (.App e1 e2) τ2

/-- Non-empty trees (trees that are not just leaves) -/
inductive nonempty : Tree → Prop where
  | NonEmpty : forall x l r, nonempty (.Node x l r)

/-- Complete trees (aka perfect trees) are binary trees whose leaves are all at the same depth -/
inductive complete : Nat → Tree → Prop where
  | CompleteLeaf : complete 0 .Leaf
  | CompleteNode : forall n x l r,
    complete n l ->
    complete n r ->
    complete (.succ n) (.Node x l r)

/-- Example with non-linear patterns, taken from Generating Good Generators -/
inductive goodTree : Nat → Nat → Tree → Prop where
  | GoodLeaf : forall n, goodTree n n .Leaf

/-- An inductive relation for left-leaning trees where all right children have to be leaves -/
inductive LeftLeaning : Tree → Prop where
  | LeftSubTreeOnly : ∀ x l,
    LeftLeaning .Leaf →
    LeftLeaning (.Node x l .Leaf)

/-- Determines whether a list is sorted
    (example taken from Computing Correctly, section 6.3)
    -- TODO: figure out why we're unable to derive a generator for this `Prop` -/
inductive Sorted : List Nat → Prop where
  | SortedNil : Sorted []
  | SortedSingleton : ∀ x, Sorted [x]
  | SortedCons : ∀ x y l,
    LE.le x y →
    Sorted (List.cons y l) →
    Sorted (List.cons x (List.cons y l))
