/-
Copyright (c) 2021 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
module

public meta import Plausible.Random

public meta section

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
deriving Inhabited

/-- Monad to generate random examples to test properties with.
It has a `Nat` parameter so that the caller can decide on the
size of the examples. It allows failure to generate via the `ExceptT` transformer -/
abbrev Gen (α : Type u) := RandT (ReaderT (ULift Nat) (Except GenError)) α

instance instMonadLiftGen [MonadLiftT m (ReaderT (ULift Nat) (Except GenError))] : MonadLiftT (RandGT StdGen m) Gen where
  monadLift := fun m => liftM ∘ m.run

instance instMonadErrorGen : MonadExcept GenError Gen := by infer_instance

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

private def errorOfGenError {α} (m : ExceptT GenError Id α) : IO α :=
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
    IO.println s!"{x}"

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


def test : Gen Nat :=
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
