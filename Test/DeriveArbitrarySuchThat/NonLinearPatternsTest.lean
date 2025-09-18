
import Plausible.Gen
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Test.CommonDefinitions.BinaryTree

open Plausible
open ArbitrarySizedSuchThat

set_option guard_msgs.diff true

-- Example taken from "Generating Good Generators for Inductive Relations", section 3
inductive GoodTree : Nat → Nat → BinaryTree → Prop where
  | GoodLeaf : ∀ n, GoodTree n n .Leaf

/--
info: Try this generator: instance : ArbitrarySizedSuchThat BinaryTree (fun t_1 => GoodTree in1_1 in2_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (in1_1 : Nat) (in2_1 : Nat) : Plausible.Gen BinaryTree :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match DecOpt.decOpt (BEq.beq in1_1 in2_1) initSize with
              | Except.ok Bool.true => return BinaryTree.Leaf
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match DecOpt.decOpt (BEq.beq in1_1 in2_1) initSize with
              | Except.ok Bool.true => return BinaryTree.Leaf
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            ])
    fun size => aux_arb size size in1_1 in2_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (t : BinaryTree) => GoodTree in1 in2 t)


/-- `SameHead xs ys` means the lists `xs` and `ys` have the same head
     - This is an example relation with a non-linear pattern
      (`x` appears twice in the conclusion of `HeadMatch`) -/
inductive SameHead : List Nat → List Nat → Prop where
| HeadMatch : ∀ x xs ys, SameHead (x::xs) (x::ys)

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List Nat) (fun xs_1 => SameHead xs_1 ys_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ys_1 : List Nat) : Plausible.Gen (List Nat) :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match ys_1 with
              | List.cons x ys => do
                let xs ← Plausible.Arbitrary.arbitrary;
                return List.cons x xs
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match ys_1 with
              | List.cons x ys => do
                let xs ← Plausible.Arbitrary.arbitrary;
                return List.cons x xs
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            ])
    fun size => aux_arb size size ys_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (xs : List Nat) => SameHead xs ys)
