import Plausible.Gen
import Plausible.Arbitrary
import Plausible.Gen
import Plausible.DeriveArbitrary

open Plausible Gen

set_option guard_msgs.diff true

/-- A binary tree is either a single `Leaf`,
    or a `Node` containing a `Nat` with left & right sub-trees -/
inductive Tree where
| Leaf : Tree
| Node : Nat → Tree → Tree → Tree
deriving Repr

-- Invoke deriving instance handler for the `Arbitrary` typeclass on `type` and `term`
deriving instance Arbitrary for Tree

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instArbitrarySizedTree -/
#guard_msgs in
#synth ArbitrarySized Tree

/-- info: instArbitraryOfArbitrarySized -/
#guard_msgs in
#synth Arbitrary Tree

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this generator: instance : Plausible.ArbitrarySized Tree where
  arbitrarySized :=
    let rec aux_arb (size : Nat) : Plausible.Gen Tree :=
      match size with
      | Nat.zero => Plausible.Gen.oneOfWithDefault (pure Tree.Leaf) [Plausible.Gen.thunkGen (fun _ => pure Tree.Leaf)]
      | Nat.succ size' =>
        Plausible.Gen.frequency (pure Tree.Leaf)
          [(1, Plausible.Gen.thunkGen (fun _ => pure Tree.Leaf)),
            (Nat.succ size',
              Plausible.Gen.thunkGen
                (fun _ => do
                  let a_0 ← Plausible.Arbitrary.arbitrary
                  let a_1 ← aux_arb size'
                  let a_2 ← aux_arb size'
                  return Tree.Node a_0 a_1 a_2))]
    fun size => aux_arb size
-/
#guard_msgs(info, drop warning) in
#derive_arbitrary Tree

end CommandElaboratorTest
