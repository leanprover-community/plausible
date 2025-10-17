/-
Copyright (c) 2021 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
import Plausible.Random

/-!
# `Gen` Monad

This monad is used to formulate randomized computations with a parameter
to specify the desired size of the result.

## Main definitions

* `Gen` monad

## References

* https://hackage.haskell.org/package/QuickCheck
-/

universe u v

namespace Plausible

open Random

/-- Error thrown on generation failure, e.g. because you've run out of resources. -/
inductive GenError : Type where
| genError : String → GenError
deriving Inhabited, Repr, BEq

/-- A non-descript generation failure. -/
def Gen.genericFailure : GenError := .genError "Generation failure."

/-- Monad to generate random examples to test properties with.
It has a `Nat` parameter so that the caller can decide on the
size of the examples. It allows failure to generate via the `Except` monad -/
abbrev Gen (α : Type u) := RandT (ReaderT (ULift Nat) (Except GenError)) α

instance instMonadLiftGen [MonadLiftT m (ReaderT (ULift Nat) (Except GenError))] : MonadLiftT (RandGT StdGen m) Gen where
  monadLift := fun m => liftM ∘ m.run

instance instMonadErrorGen : MonadExcept GenError Gen := by infer_instance

/-- Lift a `GenError` to `IO.Error`. -/
def Gen.genFailure (e : GenError) : IO.Error :=
  let .genError mes := e
  IO.userError s!"generation failure: {mes}"

namespace Gen

@[inline]
def up (x : Gen.{u} α) : Gen (ULift.{v} α) :=
  RandT.up
    (λ m size ↦
      match m.run ⟨size.down⟩ with
      | .error (.genError s) => .error (.genError s)
      | .ok a => .ok ⟨a⟩) x


@[inline]
def down (x : Gen (ULift.{v} α)) : Gen α :=
  RandT.down (λ m size ↦
      match m.run ⟨size.down⟩ with
      | .error e => .error e
      | .ok a => .ok a.down) x

/-- Lift `Random.random` to the `Gen` monad. -/
def chooseAny (α : Type u) [Random Id α] : Gen α :=
  rand (g := StdGen) α (m := Id) |> liftM

/-- Lift `BoundedRandom.randomR` to the `Gen` monad. -/
def choose (α : Type u) [LE α] [BoundedRandom Id α] (lo hi : α) (h : lo ≤ hi) :
    Gen {a // lo ≤ a ∧ a ≤ hi} :=
  randBound (g := StdGen) α (m := Id) lo hi h |> liftM


/-- Generate a `Nat` example between `lo` and `hi` (exclusively). -/
def chooseNatLt (lo hi : Nat) (h : lo < hi) : Gen {a // lo ≤ a ∧ a < hi} := do
  let ⟨val, h⟩ ← choose Nat (lo + 1) hi (by omega)
  return ⟨val - 1, by omega⟩

/-- Get access to the size parameter of the `Gen` monad. -/
def getSize : Gen Nat :=
  return (← read).down

/-- Apply a function to the size parameter. -/
def resize {α : Type _} (f : Nat → Nat) (x : Gen α) : Gen α :=
  withReader (ULift.up ∘ f ∘ ULift.down) x

/--
Choose a `Nat` between `0` and `getSize`.
-/
def chooseNat : Gen Nat := do choose Nat 0 (← getSize) (by omega)

/-!
The following section defines various combinators for generators, which are used
in the body of derived generators (for derived `Arbitrary` instances).

The code for these combinators closely mirrors those used in Rocq/Coq QuickChick
(see link in the **References** section below).

## References
* https://github.com/QuickChick/QuickChick/blob/master/src/Generators.v

-/

/-- `pick default xs n` chooses a weight & a generator `(k, gen)` from the list `xs` such that `n < k`.
    If `xs` is empty, the `default` generator with weight 0 is returned.  -/
private def pick (default : Gen α) (xs : List (Nat × Gen α)) (n : Nat) : Nat × Gen α :=
  match xs with
  | [] => (0, default)
  | (k, x) :: xs =>
    if n < k then
      (k, x)
    else
      pick default xs (n - k)

/-- Picks one of the generators in `gs` at random, returning the `default` generator
    if `gs` is empty.

    (This is a more ergonomic version of Plausible's `Gen.oneOf` which doesn't
    require the caller to supply a proof that the list index is in bounds.) -/
def oneOfWithDefault (default : Gen α) (gs : List (Gen α)) : Gen α :=
  match gs with
  | [] => default
  | _ => do
    let idx ← Gen.choose Nat 0 (gs.length - 1) (by omega)
    List.getD gs idx.val default

/-- `frequency` picks a generator from the list `gs` according to the weights in `gs`.
    If `gs` is empty, the `default` generator is returned.  -/
def frequency (default : Gen α) (gs : List (Nat × Gen α)) : Gen α := do
  let total := List.sum <| List.map Prod.fst gs
  let n ← Gen.choose Nat 0 (total - 1) (by omega)
  (pick default gs n).snd

/-- `sized f` constructs a generator that depends on its `size` parameter -/
def sized (f : Nat → Gen α) : Gen α :=
  Gen.getSize >>= f

variable {α : Type u}

/-- Create an `Array` of examples using `x`. The size is controlled
by the size parameter of `Gen`. -/
def arrayOf (x : Gen α) : Gen (Array α) := do
  let ⟨sz⟩ ← up chooseNat
  let mut res := Array.mkEmpty sz
  for _ in [0:sz] do
    res := res.push (← x)
  return res

/-- Create a `List` of examples using `x`. The size is controlled
by the size parameter of `Gen`. -/
def listOf (x : Gen α) : Gen (List α) := do
  return (← arrayOf x).toList

/-- Given a list of example generators, choose one to create an example. -/
def oneOf (xs : Array (Gen α)) (pos : 0 < xs.size := by decide) : Gen α := do
  let ⟨x, _, h2⟩ ← up <| chooseNatLt 0 xs.size pos
  xs[x]

/-- Given a list of examples, choose one to create an example. -/
def elements (xs : List α) (pos : 0 < xs.length) : Gen α := do
  let ⟨x, _, h2⟩ ← up <| chooseNatLt 0 xs.length pos
  return xs[x]


open List in
/-- Generate a random permutation of a given list. -/
def permutationOf : (xs : List α) → Gen { ys // xs ~ ys }
  | [] => pure ⟨[], Perm.nil⟩
  | x::xs => do
    let ⟨ys, h1⟩ ← permutationOf xs
    let ⟨n, _, h3⟩ ← up <| choose Nat 0 ys.length (by omega)
    return ⟨ys.insertIdx n x, Perm.trans (Perm.cons _ h1) (List.perm_insertIdx _ _ h3).symm⟩

/-- Given two generators produces a tuple consisting out of the result of both -/
def prodOf {α : Type u} {β : Type v} (x : Gen α) (y : Gen β) : Gen (α × β) := do
  let ⟨a⟩ ← up x
  let ⟨b⟩ ← up y
  return (a, b)

end Gen

private def errorOfGenError {α} (m : Except GenError α) : IO α :=
  match m with
  | .ok a => pure a
  | .error (.genError msg) => throw <| .userError ("Generation failure:" ++ msg)

-- Instance that just sets the size to zero (it will be reset later)
instance instMonadLiftStateIOGen : MonadLift (ReaderT (ULift Nat) (Except GenError)) IO where
  monadLift m := errorOfGenError <| ReaderT.run m ⟨0⟩

/-- Execute a `Gen` inside the `IO` monad using `size` as the example size -/
def Gen.run {α : Type} (x : Gen α) (size : Nat) : IO α :=
  letI : MonadLift (ReaderT (ULift Nat) (Except GenError)) IO := ⟨fun m => errorOfGenError <| ReaderT.run m ⟨size⟩⟩
  runRand x

/--
Print (at most) 10 samples of a given type to stdout for debugging. Sadly specialized to `Type 0`
-/
def Gen.printSamples {t : Type} [Repr t] (g : Gen t) : IO PUnit := do
  let xs : List t ← (List.range 10).mapM (Gen.run g)
  let xs := xs.map repr
  for x in xs do
    IO.println s!"{x}\n"

/-- Execute a `Gen` until it actually produces an output. May diverge for bad generators! -/
partial def Gen.runUntil {α : Type} (attempts : Option Nat := .none) (x : Gen α) (size : Nat) : IO α :=
  Gen.run (repeatGen attempts x) size
  where
  repeatGen (attempts : Option Nat) (x : Gen α) : Gen α :=
  match attempts with
  | .some 0 => throw <| GenError.genError "Gen.runUtil: Out of attempts"
  | _ =>
  try x catch
  | GenError.genError _ => do
    let _ ← Rand.next
    repeatGen (decr attempts) x
  decr : Option Nat → Option Nat
  | .some n => .some (n-1)
  | .none => .none


private def test : Gen Nat :=
  do
    let x : Nat ← Gen.choose Nat 0 (← Gen.getSize) (Nat.zero_le _)
    if x % 10 == 0
    then
      return x
    else
      throw <| .genError "uh oh"

-- This fails 9/10 times
-- #eval Gen.run test 9

-- This succeeds almost always.
-- #eval Gen.runUntil (attempts := .some 1000) test 9

end Plausible
