
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

/--
info: Try this generator: instance : ArbitrarySizedSuchThat Nat (fun x_1 => Between lo_1 x_1 hi_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (lo_1 : Nat) (hi_1 : Nat) : Plausible.Gen Nat :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match hi_1 with
              | Nat.succ (Nat.succ m) =>
                match DecOpt.decOpt (LE.le lo_1 m) initSize with
                | Except.ok Bool.true => return Nat.succ lo_1
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match hi_1 with
              | Nat.succ (Nat.succ m) =>
                match DecOpt.decOpt (LE.le lo_1 m) initSize with
                | Except.ok Bool.true => return Nat.succ lo_1
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size',
              match hi_1 with
              | Nat.succ o => do
                let m ← aux_arb initSize size' lo_1 o;
                return Nat.succ m
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size lo_1 hi_1
-/
#guard_msgs(info, drop warning, whitespace:=lax) in
#derive_generator (fun (x : Nat) => Between lo x hi)


/--
info: Try this generator: instance : ArbitrarySizedSuchThat BinaryTree (fun t_1 => BST lo_1 hi_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (lo_1 : Nat) (hi_1 : Nat) : Plausible.Gen BinaryTree :=
      (match size with
      | Nat.zero => GeneratorCombinators.backtrack [(1, return BinaryTree.Leaf)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1, return BinaryTree.Leaf),
            (Nat.succ size', do
              let x ← ArbitrarySizedSuchThat.arbitrarySizedST (fun x => Between lo_1 x hi_1) initSize;
              do
                let l ← aux_arb initSize size' lo_1 x;
                do
                  let r ← aux_arb initSize size' x hi_1;
                  return BinaryTree.Node x l r)])
    fun size => aux_arb size size lo_1 hi_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (t : BinaryTree) => BST lo hi t)


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
-- #eval runTests (numTrials := 100) (useBuggyVersion := true)
