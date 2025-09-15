import Plausible.Chamelean.Examples.ExampleInductiveRelations
import Plausible.Chamelean.OptionTGen
import Plausible.Arbitrary
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DecOpt

import Plausible.Gen
open Plausible
open OptionTGen

open ArbitrarySizedSuchThat

set_option linter.missingDocs false

--------------------------------------------------------------------------
-- Some example `OptionT Gen α` generators
--------------------------------------------------------------------------

/-- `arbitrarySizedST` contains a handwritten generator for BSTs
    (modelled after the automatically derived generator produced by QuickChick).
    Note that:
    - We use the `OptionT` monad transformer to add the possibility of failure to the `Gen` monad
    - All the generators supplied to the `backtrack` combinator are thunked, to avoid unnecessary
      computation (since Lean is strict) -/
def genBST (lo : Nat) (hi : Nat) : Nat → OptionT Gen Tree :=
  let rec aux_arb (initSize : Nat) (size : Nat) (lo_0 : Nat) (hi_0 : Nat) : OptionT Gen Tree :=
    match size with
    | .zero =>
      backtrack [
        (1, thunkGen $ fun _ => pure .Leaf),
        (1, thunkGen $ fun _ => OptionT.fail)
      ]
    | .succ size' =>
      backtrack [
        (1, thunkGen $ fun _ => pure .Leaf),
        (.succ size', thunkGen $ fun _ => do
          let x ← Arbitrary.arbitrary
          if (lo_0 < x && x < hi_0) then
            let l ← aux_arb initSize size' lo_0 x
            let r ← aux_arb initSize size' x hi_0
            pure (.Node x l r)
          else OptionT.fail)
      ]
  fun size => aux_arb size size lo hi

/- Instance of the `ArbitrarySizedSuchThat` typeclass for generators of BSTs -/
instance : ArbitrarySizedSuchThat Tree (fun t => bst lo hi t) where
  arbitrarySizedST := genBST lo hi

/-- A handwritten generator for balanced trees of height `n`
    (modelled after the automatically derived generator produced by QuickChick) -/
def genBalancedTree (n : Nat) : Nat → OptionT Gen Tree :=
  let rec aux_arb (initSize : Nat) (size : Nat) (n_0 : Nat) : OptionT Gen Tree :=
      match size with
      | .zero =>
        backtrack [
          (1, thunkGen $ fun _ =>
              match n_0 with
              | .zero => pure .Leaf
              | .succ _ => OptionT.fail),
          (1, thunkGen $ fun _ =>
              match n_0 with
              | 1 => pure .Leaf
              | _ => OptionT.fail),
          (1, thunkGen $ fun _ => OptionT.fail)
        ]
      | .succ size' =>
        backtrack [
          (1, thunkGen $ fun _ =>
              match n_0 with
              | .zero => pure .Leaf
              | _ => OptionT.fail),
          (1, thunkGen $ fun _ =>
              match n_0 with
              | 1 => pure .Leaf
              | _ => OptionT.fail),
          (.succ size', thunkGen $ fun _ =>
            match n_0 with
            | .zero => OptionT.fail
            | .succ n => do
              let l ← aux_arb initSize size' n
              let r ← aux_arb initSize size' n
              let x ← Arbitrary.arbitrary
              pure (.Node x l r))
        ]
  fun size => aux_arb size size n

/- Instance of the `ArbitrarySizedSuchThat` typeclass for generators of balanced trees
   of height `n` -/
-- instance : ArbitrarySizedSuchThat Tree (fun t => balanced n t) where
--   arbitrarySizedST := genBalancedTree n


/-
Example usage:

To sample from the derived generator, we apply the `arbitrarySizedST` function
(from the `ArbitrarySizedSuchThat` typeclass) onto the proposition that constrains
the generated values (e.g. `fun t => balanced 5 t` for balanced trees of height 5).
We then invoke `runSizedGen` to display the generated value in the `IO` monad.

For example:
```
def tempSize := 10
#eval runSizedGen (arbitrarySizedST (fun t => balanced 5 t)) tempSize
```
-/

/-- Hand-written `DecOpt` instance for the inductive relation `between lo x hi`, which means `lo < x < hi` -/
instance : DecOpt (between lo_1 x_1 hi_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (lo_1 : Nat) (x_1 : Nat) (hi_1 : Nat) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match hi_1 with
            | Nat.succ (Nat.succ m) =>
              match x_1 with
              | Nat.succ u_3 =>
                DecOpt.andOpt (DecOpt.decOpt (BEq.beq u_3 lo_1) initSize) (DecOpt.decOpt (LE.le lo_1 m) initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match hi_1 with
            | Nat.succ (Nat.succ m) =>
              match x_1 with
              | Nat.succ u_3 =>
                match DecOpt.decOpt (BEq.beq u_3 lo_1) initSize with
                | Option.some Bool.true =>
                  match DecOpt.decOpt (LE.le lo_1 m) initSize with
                  | Option.some Bool.true => Option.some Bool.true
                  | _ => Option.some Bool.false
                | _ => Option.some Bool.false
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match hi_1 with
            | Nat.succ o =>
              match x_1 with
              | Nat.succ m =>
                match aux_dec initSize size' lo_1 m o with
                | Option.some Bool.true => Option.some Bool.true
                | _ => Option.some Bool.false
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
    fun size => aux_dec size size lo_1 x_1 hi_1


/-- Handwritten `DecOpt` instance for the proposition `bst lo hi t` -/
instance : DecOpt (bst lo hi t) where
  decOpt :=
    let rec aux_arb (initSize : Nat) (size : Nat) (lo_0 : Nat) (hi_0 : Nat) (t_0 : Tree) : Option Bool :=
      match size with
      | .zero =>
        DecOpt.checkerBacktrack [
          fun _ =>
            match t_0 with
            | .Leaf => some true
            | .Node _ _ _ => some false,
          fun _ => none
        ]
      | .succ size' =>
        DecOpt.checkerBacktrack [
          fun _ =>
            match t_0 with
            | .Leaf => some true
            | .Node _ _ _ => some false,
          fun _ =>
            match t_0 with
            | .Leaf => some false
            | .Node x l r =>
              DecOpt.andOptList [
                DecOpt.decOpt (lo_0 < x && x < hi_0) initSize,
                aux_arb initSize size' lo_0 x l,
                aux_arb initSize size' x hi_0 r
              ]
        ]
    fun size => aux_arb size size lo hi t

/-- Handwritten `DecOpt` instance for the proposition `balanced n t` -/
instance : DecOpt (balanced n t) where
  decOpt :=
    let rec aux_arb (initSize : Nat) (size : Nat) (n_0 : Nat) (t_0 : Tree) : Option Bool :=
      match size with
      | .zero =>
        DecOpt.checkerBacktrack [
          (fun _ =>
            match t_0 with
            | .Leaf => match n_0 with
                      | 0 => some true
                      | _ => some false
            | _ => some false),
          (fun _ =>
            match t_0 with
            | .Leaf => match n_0 with
                      | 1 => some true
                      | _ => some false
            | _ => some false),
          (fun _ => none)
        ]
      | .succ size' =>
        DecOpt.checkerBacktrack [
          (fun _ =>
            match t_0 with
            | .Leaf => match n_0 with
                      | 0 => some true
                      | _ => some false
            | _ => some false),
          (fun _ =>
            match t_0 with
            | .Leaf => match n_0 with
                      | 1 => some true
                      | _ => some false
            | _ => some false),
          (fun _ =>
            match t_0 with
            | .Leaf => some false
            | .Node _ l r =>
              match n_0 with
              | .succ n =>
                DecOpt.andOptList [
                  aux_arb initSize size' n l,
                  aux_arb initSize size' n r
                ]
              | _ => some false)
        ]
    fun size => aux_arb size size n t
