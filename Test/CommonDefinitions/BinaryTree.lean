/-- A datatype for binary trees. This type definition is used in the following test files:
   - `DeriveBalancedTreeGenerator.lean`
   - `DeriveBSTGenerator.lean`
   - `NonLinearPatternsTest.lean` -/
inductive BinaryTree where
  | Leaf : BinaryTree
  | Node : Nat → BinaryTree → BinaryTree → BinaryTree
  deriving Repr

/-- `Between lo x hi` means `lo < x < hi` -/
inductive Between : Nat -> Nat -> Nat -> Prop where
| BetweenN : ∀ n m, n <= m -> Between n (.succ n) (.succ (.succ m))
| BetweenS : ∀ n m o,
  Between n m o -> Between n (.succ m) (.succ o)

/-- `BST lo hi t` describes whether a tree `t` is a BST that contains values strictly within `lo` and `hi` -/
inductive BST : Nat → Nat → BinaryTree → Prop where
  | BstLeaf: BST lo hi .Leaf
  | BstNode: ∀ lo hi x l r,
    Between lo x hi →
    BST lo x l →
    BST x hi r →
    BST lo hi (.Node x l r)
