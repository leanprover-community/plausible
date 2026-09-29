/-
Copyright (c) 2024 Plausible Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Plausible.Sampleable

/-!
# Binary Search Shrinking

Provides `shrinkToMinimal` for numeric types, finding the smallest failing value
via binary search in O(log n) test evaluations.

## Motivation

The standard `Shrinkable.shrink` generates candidates by halving:
```
Nat.shrink 4096 = [2048, 1024, 512, ..., 1, 0]
```

For a test `n ≥ 50`, this finds 64 (first power of 2 ≥ 50). But the true minimal
counterexample is 50. Binary search finds it directly.

## Usage

```lean
-- Find minimal n where test fails
let minimal := Nat.shrinkToMinimal (fun n => n < 50) 4096
-- Returns 50
```
-/

namespace Plausible

/-- Binary search for the smallest `n ∈ [lo, hi)` where `test n = false`.
    Returns `lo` if all values pass, or the minimal failing value. -/
def Nat.binarySearch (test : Nat → Bool) (lo hi : Nat) : Nat :=
  if lo >= hi then lo
  else
    let mid := (lo + hi) / 2
    if test mid then Nat.binarySearch test (mid + 1) hi
    else Nat.binarySearch test lo mid
termination_by hi - lo

/-- Find the minimal failing `Nat` via binary search.
    If `test n = false`, returns the smallest `m ≤ n` where `test m = false`. -/
def Nat.shrinkToMinimal (test : Nat → Bool) (n : Nat) : Nat :=
  if test n then n  -- n passes, nothing to shrink
  else Nat.binarySearch test 0 n

/-- Binary search for `Int`. Searches toward 0 from either direction. -/
def Int.shrinkToMinimal (test : Int → Bool) (n : Int) : Int :=
  if test n then n
  else if n >= 0 then
    Nat.binarySearch (fun k => test k) 0 n.toNat
  else
    let absN := n.natAbs
    let minimal := Nat.binarySearch (fun k => test (-Int.ofNat k)) 0 absN
    (-Int.ofNat minimal)

/-- Binary search for `Fin n`. -/
def Fin.shrinkToMinimal {n : Nat} (test : Fin n.succ → Bool) (x : Fin n.succ) : Fin n.succ :=
  if test x then x
  else
    let minimal := Nat.binarySearch (fun k => if h : k < n.succ then test ⟨k, h⟩ else true) 0 x.val
    if h : minimal < n.succ then ⟨minimal, h⟩ else x

/-- Binary search for `UInt8`. -/
def UInt8.shrinkToMinimal (test : UInt8 → Bool) (n : UInt8) : UInt8 :=
  if test n then n
  else (Nat.binarySearch (fun k => test k.toUInt8) 0 n.toNat).toUInt8

/-- Binary search for `UInt16`. -/
def UInt16.shrinkToMinimal (test : UInt16 → Bool) (n : UInt16) : UInt16 :=
  if test n then n
  else (Nat.binarySearch (fun k => test k.toUInt16) 0 n.toNat).toUInt16

/-- Binary search for `UInt32`. -/
def UInt32.shrinkToMinimal (test : UInt32 → Bool) (n : UInt32) : UInt32 :=
  if test n then n
  else (Nat.binarySearch (fun k => test k.toUInt32) 0 n.toNat).toUInt32

/-- Binary search for `UInt64`. -/
def UInt64.shrinkToMinimal (test : UInt64 → Bool) (n : UInt64) : UInt64 :=
  if test n then n
  else (Nat.binarySearch (fun k => test k.toUInt64) 0 n.toNat).toUInt64

end Plausible
