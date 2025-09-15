import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.EnumeratorCombinators

/-- Base types in the Simply-Typed Lambda Calculus (STLC)
    (either Nat or functions) -/
inductive type where
  | Nat : type
  | Fun : type → type → type
  deriving BEq, DecidableEq, Repr

/-- Terms in the STLC extended with naturals and addition -/
inductive term where
  | Const: Nat → term
  | Add: term → term → term
  | Var: Nat → term
  | App: term → term → term
  | Abs: type → term → term
  deriving BEq, Repr

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
