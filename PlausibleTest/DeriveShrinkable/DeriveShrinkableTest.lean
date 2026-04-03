import Plausible

open Plausible

namespace ShrinkableTests

-- Simple enum type
inductive Color where
  | Red | Green | Blue
  deriving Repr, Shrinkable

-- Binary tree (recursive, with non-recursive field)
inductive Tree where
  | Leaf : Tree
  | Node : Nat → Tree → Tree → Tree
  deriving Repr, Shrinkable

-- Parameterized type
inductive ShrinkList (α : Type) where
  | Nil : ShrinkList α
  | Cons : α → ShrinkList α → ShrinkList α
  deriving Repr, Shrinkable

-- Structure (single-constructor inductive)
structure Point where
  x : Nat
  y : Nat
  deriving Repr, Shrinkable

-- Nullary constructors shrink to []
/-- info: [] -/
#guard_msgs in
#eval Shrinkable.shrink Color.Red

/-- info: [] -/
#guard_msgs in
#eval Shrinkable.shrink Tree.Leaf

-- Shrinking a Node yields subterms (Leaf, Leaf) + argument shrinks (shrinking the Nat)
/--
info: [ShrinkableTests.Tree.Leaf,
 ShrinkableTests.Tree.Leaf,
 ShrinkableTests.Tree.Node 2 (ShrinkableTests.Tree.Leaf) (ShrinkableTests.Tree.Leaf),
 ShrinkableTests.Tree.Node 1 (ShrinkableTests.Tree.Leaf) (ShrinkableTests.Tree.Leaf),
 ShrinkableTests.Tree.Node 0 (ShrinkableTests.Tree.Leaf) (ShrinkableTests.Tree.Leaf)]
-/
#guard_msgs in
#eval Shrinkable.shrink (Tree.Node 5 Tree.Leaf Tree.Leaf)

-- Shrinking a parameterized list
/--
info: [ShrinkableTests.ShrinkList.Cons 1 (ShrinkableTests.ShrinkList.Nil),
 ShrinkableTests.ShrinkList.Cons 1 (ShrinkableTests.ShrinkList.Cons 1 (ShrinkableTests.ShrinkList.Nil)),
 ShrinkableTests.ShrinkList.Cons 0 (ShrinkableTests.ShrinkList.Cons 1 (ShrinkableTests.ShrinkList.Nil)),
 ShrinkableTests.ShrinkList.Cons 3 (ShrinkableTests.ShrinkList.Nil),
 ShrinkableTests.ShrinkList.Cons 3 (ShrinkableTests.ShrinkList.Cons 0 (ShrinkableTests.ShrinkList.Nil))]
-/
#guard_msgs in
#eval Shrinkable.shrink (ShrinkList.Cons 3 (ShrinkList.Cons 1 ShrinkList.Nil))

-- Shrinking a structure
/--
info: [{ x := 5, y := 20 },
 { x := 2, y := 20 },
 { x := 1, y := 20 },
 { x := 0, y := 20 },
 { x := 10, y := 10 },
 { x := 10, y := 5 },
 { x := 10, y := 2 },
 { x := 10, y := 1 },
 { x := 10, y := 0 }]
-/
#guard_msgs in
#eval Shrinkable.shrink (Point.mk 10 20)

end ShrinkableTests
