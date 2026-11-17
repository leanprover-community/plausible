/-
Copyright (c) 2024 Plausible Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Plausible.ShrinkSearch

/-! # Tests for Binary Search Shrinking -/

open Plausible

/-- Test that binary search finds exact boundary -/
def testNatBoundary : IO Unit := do
  -- Test: n < 50 (fails for n ≥ 50)
  let test := fun n : Nat => n < 50
  let result := Nat.shrinkToMinimal test 4096
  assert! result == 50
  IO.println s!"✓ Nat.shrinkToMinimal: 4096 → {result} (expected 50)"

/-- Test edge cases -/
def testNatEdgeCases : IO Unit := do
  -- Already passing
  let result1 := Nat.shrinkToMinimal (fun n => n < 100) 50
  assert! result1 == 50  -- unchanged, passes
  IO.println s!"✓ Already passing: 50 → {result1}"

  -- Fails at 0
  let result2 := Nat.shrinkToMinimal (fun _ => false) 1000
  assert! result2 == 0
  IO.println s!"✓ Fails at 0: 1000 → {result2}"

  -- Fails only at max
  let result3 := Nat.shrinkToMinimal (fun n => n < 1000) 1000
  assert! result3 == 1000
  IO.println s!"✓ Fails only at max: 1000 → {result3}"

/-- Test Int shrinking (toward 0) -/
def testIntShrink : IO Unit := do
  -- Positive: n ≥ 50
  let result1 := Int.shrinkToMinimal (fun n => n < 50) 4096
  assert! result1 == 50
  IO.println s!"✓ Int positive: 4096 → {result1}"

  -- Negative: n ≤ -50
  let result2 := Int.shrinkToMinimal (fun n => n > -50) (-4096)
  assert! result2 == -50
  IO.println s!"✓ Int negative: -4096 → {result2}"

/-- Test UInt8 shrinking -/
def testUInt8Shrink : IO Unit := do
  let result := UInt8.shrinkToMinimal (fun n => n < 100) 255
  assert! result == 100
  IO.println s!"✓ UInt8: 255 → {result}"

/-- Compare with standard shrink -/
def testCompareWithStandard : IO Unit := do
  IO.println "\nComparison with Nat.shrink:"

  let test := fun n : Nat => n < 50

  -- Standard shrink: try candidates in order (manual iteration with fuel)
  let rec go (n : Nat) : (fuel : Nat) → Nat
    | 0 => n
    | fuel + 1 =>
      let candidates := Nat.shrink n
      match candidates.find? (fun c => !test c) with
      | some smaller => go smaller fuel
      | none => n
  let standardResult := go 4096 100
  IO.println s!"  Nat.shrink (iterative): 4096 → {standardResult}"

  -- Binary search
  let binaryResult := Nat.shrinkToMinimal test 4096
  IO.println s!"  Nat.shrinkToMinimal:   4096 → {binaryResult}"

  IO.println s!"  Improvement: {standardResult} → {binaryResult}"

def main : IO Unit := do
  IO.println "=== Binary Search Shrinking Tests ===\n"
  testNatBoundary
  testNatEdgeCases
  testIntShrink
  testUInt8Shrink
  testCompareWithStandard
  IO.println "\n✓ All tests passed"
