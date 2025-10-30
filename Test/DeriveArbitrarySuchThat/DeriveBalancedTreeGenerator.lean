
import Plausible.Gen
import Plausible.Arbitrary
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Test.CommonDefinitions.BinaryTree

open Plausible
open ArbitrarySizedSuchThat

set_option guard_msgs.diff true

-- `balancedTree n t` describes whether the tree `t` of height `n` is *balancedTree*, i.e. every path through the tree has length either `n` or `n-1`. -/
inductive balancedTree : Nat → BinaryTree → Prop where
  | B0 : balancedTree .zero BinaryTree.Leaf
  | B1 : balancedTree (.succ .zero) BinaryTree.Leaf
  | BS : ∀ n x l r,
    balancedTree n l → balancedTree n r →
    balancedTree (.succ n) (BinaryTree.Node x l r)

#guard_msgs(drop info, drop warning) in
derive_generator (fun n => ∃ (t : BinaryTree), balancedTree n t)
