/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/

import Plausible.Gen
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Test.CommonDefinitions.BinaryTree
import Test.DeriveDecOpt.DeriveBSTChecker
import Plausible.Testable

open Plausible
open ArbitrarySizedSuchThat

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_generator (fun lo hi => ∃ (x : Nat), Between lo x hi)

deriving instance Arbitrary for BinaryTree

#guard_msgs(drop info, drop warning) in
derive_generator (fun lo hi => ∃ (t : BinaryTree), BST lo hi t)


/-- Inserts an element into a tree, respecting the BST invariants -/
def insert (x : Nat) (t : BinaryTree) : BinaryTree :=
  match t with
  | .Leaf => .Node x .Leaf .Leaf
  | .Node y l r =>
    if x < y then
      .Node y (insert x l) r
    else if x > y then
      .Node y l (insert x r)
    else t

/-- A buggy insertion function which ignores the input tree and
    returns a two-node tree where both values are `x` -/
def buggyInsert (x : Nat) (_ : BinaryTree) : BinaryTree :=
  .Node x (.Node x .Leaf .Leaf) .Leaf

/-- Test harness for testing the property `∀ (x : Nat) (t : Tree), BST 0 10 t → BST 0 10 (insert x t)`.

    To check that the derived generator can be used for catching bugs,
    set `useBuggyVersion := true` -/
def runTests (numTrials : Nat) (useBuggyVersion : Bool := false) : IO Unit := do
  let size := 10
  let mut numSucceeded := 0
  for _ in [:numTrials] do
    let x ← Gen.run (Subtype.val <$> Gen.chooseNatLt 1 10 (by decide)) size
    let t ← Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => BST 0 10 t) size) size
    let insertFn := if useBuggyVersion then buggyInsert else insert
    let t' := insertFn x t
    let b := DecOpt.decOpt (BST 0 10 t') size
    match b with
    | .ok bool =>
      if bool then
        numSucceeded := numSucceeded + 1
      else
        IO.println s!"Property falsified!\nt = {repr t}\nx = {x}\nt' = {repr t'}"
        return
    | .error (.genError e) => IO.println s!"unable to generate valid BST: {e}"
  IO.println s!"Chamelean: finished {numTrials} tests, {numSucceeded} passed"

-- Uncomment this to run the aforementioned test harness
-- Sadly this cannot be made a #guard_msg since the counter-example is non-deterministic

-- #eval runTests (numTrials := 100) (useBuggyVersion := true)
