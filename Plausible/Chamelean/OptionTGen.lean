import Plausible.Chamelean.GeneratorCombinators

import Plausible.Gen
import Plausible.Sampleable
open Plausible

namespace OptionTGen

----------------------------------------------------------------------------------
-- Combinators for generators that may fail (adapted from QuickChick sourcecode)
-- https://github.com/QuickChick/QuickChick/blob/master/src/Generators.v
----------------------------------------------------------------------------------

/-- `pick default xs n` chooses a weight & a generator `(k, gen)` from the list `xs` such that `n < k`.
    If `xs` is empty, the `default` generator with weight 0 is returned.  -/
def pick (default : OptionT Gen α) (xs : List (Nat × OptionT Gen α)) (n : Nat) : Nat × OptionT Gen α :=
  match xs with
  | [] => (0, default)
  | (k, x) :: xs =>
    if n < k then
      (k, x)
    else
      pick default xs (n - k)

/-- `pickDrop xs n` returns a weight & its generator `(k, gen)` from the list `xs`
     such that `n < k`, and also returns the tail of the list after `(k, gen)` -/
def pickDrop (xs : List (Nat × OptionT Gen α)) (n : Nat) : Nat × OptionT Gen α × List (Nat × OptionT Gen α) :=
  match xs with
  | [] => (0, OptionT.fail, [])
  | (k, x) :: xs =>
    if n < k then
      (k, x, xs)
    else
      let (k', x', xs') := pickDrop xs (n - k)
      (k', x', (k, x)::xs')

/-- Sums all the weights in an association list containing `Nat`s and `α`s -/
def sumFst (gs : List (Nat × α)) : Nat :=
  List.foldl (fun acc p => acc + p.fst) 0 gs

/-- Helper function for `backtrack` which picks one out of `total` generators with some initial amount of `fuel` -/
def backtrackFuel (fuel : Nat) (total : Nat) (gs : List (Nat × OptionT Gen α)) : OptionT Gen α :=
  match fuel with
  | .zero => OptionT.fail
  | .succ fuel' => do
    let n ← Gen.choose Nat 0 (total - 1) (by omega)
    let (k, g, gs') := pickDrop gs n
    -- Try to generate a value using `g`, if it fails, backtrack with `fuel'`
    -- and pick one out of the `total - k` remaining generators
    OptionT.tryCatch g (fun () => backtrackFuel fuel' (total - k) gs')

/-- Tries all generators until one returns a `Some` value or all the generators failed once with `None`.
   The generators are picked at random according to their weights (like `frequency` in Haskell QuickCheck),
   and each generator is run at most once. -/
def backtrack (gs : List (Nat × OptionT Gen α)) : OptionT Gen α :=
  backtrackFuel (gs.length) (sumFst gs) gs

/-- Delays the evaluation of a generator by taking in a function `f : Unit → OptionT Gen α` -/
def thunkGen (f : Unit → OptionT Gen α) : OptionT Gen α :=
  f ()

/-- `frequency` picks a generator from the list `gs` according to the weights in `gs`.
    If `gs` is empty, `OptionT.fail` is returned to indicate failure.  -/
def frequency (gs : List (Nat × OptionT Gen α)) : OptionT Gen α := do
  let total := sumFst gs
  let n ← Gen.choose Nat 0 (total - 1) (by omega)
  .snd (pick OptionT.fail gs n)

/-- `sized f` constructs a generator that depends on its `size` parameter -/
def sized (f : Nat → OptionT Gen α) : OptionT Gen α :=
  Gen.getSize >>= f

/-- Samples from an `OptionT Gen` generator that is parameterized by its `size`,
    printing out 1 sample using the `Repr` instance for `α` -/
def runSizedGen {α} [Repr α] (sizedGen : Nat → OptionT Gen α) (size : Nat) : IO PUnit :=
  printNSamples (OptionT.run (sizedGen size)) 1

/-- Samples from an `OptionT Gen` generator that is parameterized by its `size`,
    printing out 10 samples using the `Repr` instance for `α` -/
def runSizedGenPrintOutput [Repr α] (sizedGen : Nat → OptionT Gen α) (size : Nat) : IO PUnit :=
  printSamples (OptionT.run (sizedGen size))

end OptionTGen
