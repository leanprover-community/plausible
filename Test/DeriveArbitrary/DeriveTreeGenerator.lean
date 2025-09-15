import Plausible.Attr
import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Testable

open Plausible Gen

set_option guard_msgs.diff true

/-- A binary tree is either a single `Leaf`,
    or a `Node` containing a `Nat` with left & right sub-trees -/
inductive Tree where
| Leaf : Tree
| Node : Nat → Tree → Tree → Tree
deriving BEq, Repr

-- Invoke deriving instance handler for the `Arbitrary` typeclass on `type` and `term`
set_option trace.plausible.deriving.arbitrary true in
/--
trace: [plausible.deriving.arbitrary] ⏎
    [mutual
       def arbitraryTree✝ : Nat → Plausible.Gen (@Tree✝) :=
         let rec aux_arb (fuel✝ : Nat) : Plausible.Gen (@Tree✝) :=
           match fuel✝ with
           | Nat.zero => Plausible.Gen.oneOfWithDefault (pure Tree.Leaf) [(pure Tree.Leaf)]
           | fuel'✝ + 1 =>
             Plausible.Gen.frequency (pure Tree.Leaf)
               [(1, (pure Tree.Leaf)),
                 (fuel'✝ + 1,
                   (do
                     let a✝ ← Plausible.Arbitrary.arbitrary
                     let a✝¹ ← aux_arb fuel'✝
                     let a✝² ← aux_arb fuel'✝
                     return Tree.Node a✝ a✝¹ a✝²))]
         fun fuel✝ => aux_arb fuel✝
     end,
     instance : Plausible.ArbitraryFueled✝ (@Tree✝) :=
       ⟨arbitraryTree✝⟩]
-/
#guard_msgs in
deriving instance Arbitrary for Tree

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitraryFueled`

/-- info: instArbitraryFueledTree -/
#guard_msgs in
#synth ArbitraryFueled Tree

/-- info: instArbitraryOfArbitraryFueled -/
#guard_msgs in
#synth Arbitrary Tree


/-!
Test that we can use the derived generator to find counterexamples.

We construct a faulty property, which (erroneously) states that
mirroring a tree does not yield the original tree. (Example taken
from "Generating Good Generators for Inductive Relations", POPL '18)

```lean
∀ t : Tree, mirror (mirror t) != t
```

where `mirror` is defined as follows:

```lean
def mirror (t : Tree) : Tree :=
  match t with
  | .Leaf => .Leaf
  | .Node x l r => .Node x r l
```

(This property is faulty, since `mirror` is an involution.)

We then test that the derived generator for `Tree`s succesfully
generates a counterexample (e.g. `Leaf`) which refutes the property.
-/

/-- Mirrors a tree, i.e. interchanges the left & right children of all `Node`s -/
def mirror (t : Tree) : Tree :=
  match t with
  | .Leaf => .Leaf
  | .Node x l r => .Node x r l

/-- A shrinker for `Tree`, adapted from Penn CIS 5520 lecture notes
    https://www.seas.upenn.edu/~cis5520/current/lectures/stub/05-quickcheck/QuickCheck.html -/
def shrinkTree (t : Tree) : List Tree :=
    match t with
    | .Leaf => [] -- empty trees can't be shrunk
    | .Node x l r =>
      [.Leaf, l, r]                                         -- left and right trees are smaller
      ++ (fun l' => .Node x l' r) <$> shrinkTree l          -- shrink left subtree
      ++ (fun r' => .Node x l r') <$> shrinkTree r          -- shrink right tree
      ++ (fun x' => .Node x' l r) <$> Shrinkable.shrink x   -- shrink the value

/-- `Shrinkable` instance for `Tree` -/
instance : Shrinkable Tree where
  shrink := shrinkTree

/-- `SampleableExt` instance for `Tree` -/
instance : SampleableExt Tree :=
  SampleableExt.mkSelfContained Arbitrary.arbitrary

-- Mirroring a tree twice should yield the original tree
-- Test that we can succesfully generate a counterexample to the erroneous property

/-- error: Found a counter-example! -/
#guard_msgs in
#eval Testable.check (∀ t : Tree, mirror (mirror t) != t)
  (cfg := {numInst := 10, maxSize := 5, quiet := true})
