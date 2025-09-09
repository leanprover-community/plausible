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

/-- Monad to generate random examples to test properties with.
It has a `Nat` parameter so that the caller can decide on the
size of the examples. It allows failure to generate via the `OptionT` transformer -/
abbrev Gen (α : Type u) := RandT (ReaderT (ULift Nat) (OptionT Id)) α

instance instMonadLiftGen [MonadLift m (ReaderT (ULift Nat) (OptionT Id))] : MonadLift (RandGT StdGen m) Gen where
  monadLift := λ m ↦ liftM ∘ (m.run)

-- We get the wrong instance by default
instance instMonadReaderGen : MonadReader (ULift Nat) Gen where
  read g :=
  do
    let size ← read
    return ⟨size, g⟩

-- We get the wrong instance by default
instance instMonadWithReaderGen : MonadWithReader (ULift Nat) Gen where
  withReader f g := withReader f g

instance instMonadErrorGen : MonadExcept Unit Gen := by infer_instance

def Gen.genFailure {α : Type} : IO α := throw <| IO.userError "generation failure"

-- Instance that just sets the size to zero (it will be reset later)
instance instMonadIOGenState : MonadLift (ReaderT (ULift Nat) (OptionT Id)) IO where
  monadLift m :=
    match ReaderT.run m ⟨0⟩ with
    | .some a => return a
    | .none => Gen.genFailure

namespace Gen

@[inline]
def up (x : Gen.{u} α) : Gen (ULift.{v} α) :=
  RandT.up
    (λ m size ↦
      match m.run ⟨size.down⟩ with
      | .none => .none
      | .some a => .some ⟨a⟩) x


@[inline]
def down (x : Gen (ULift.{v} α)) : Gen α :=
  RandT.down (λ m size ↦
      match m.run ⟨size.down⟩ with
      | .none => .none
      | .some a => .some a.down) x

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
  let arr ← arrayOf x
  return arr.toList

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

/-- Execute a `Gen` inside the `IO` monad using `size` as the example size -/
def Gen.run {α : Type} (x : Gen α) (size : Nat) : IO α :=
  let errOfOpt {α} : OptionT Id α → IO α := λ m ↦
    match m with
    | .some a => pure a
    | .none => genFailure
  letI : MonadLift (ReaderT (ULift Nat) (OptionT Id)) IO := ⟨fun m => errOfOpt <| ReaderT.run m ⟨size⟩⟩
  runRand x

/-- Execute a `Gen` until it actually produces an output. May diverge for bad generators! -/
partial def Gen.runUntil {α : Type} (attempts : Option Nat := .none) (x : Gen α) (size : Nat) : IO α :=
  match attempts with
  | .some 0 => genFailure
  | _ =>
  try
    Gen.run x size
  catch
    | .userError "generation failure" =>
      Gen.runUntil (decr attempts) x size
    | e => throw e
  where decr : Option Nat → Option Nat
  | .some n => .some (n-1)
  | .none => .none

end Plausible
