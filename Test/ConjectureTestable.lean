/-
Copyright (c) 2024 Plausible Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Plausible.ConjectureTestable

/-!
# Tests for ConjectureTestable Integration

This file tests the integration between the Conjecture engine and Plausible's Testable framework.
-/

namespace ConjectureTestableTest

open Plausible.Conjecture

/-- Test a property that should always pass -/
def testPassingProperty : IO Unit := do
  IO.println "Testing: ∀ n : Nat, n + 0 = n"
  let result ← checkResult (p := ∀ n : Nat, n + 0 = n) "test_add_zero"
    { numTests := 50, quiet := false, healthChecks := false }
  match result with
  | .success n => IO.println s!"  ✓ Passed {n} tests"
  | .failure ce _ _ => throw <| IO.userError s!"  ✗ Unexpected failure: {ce}"
  | .gaveUp n => throw <| IO.userError s!"  ⚠ Gave up after {n} invalid examples"
  | .error msg => throw <| IO.userError s!"  Error: {msg}"

/-- Test a property that should fail -/
def testFailingProperty : IO Unit := do
  IO.println "Testing: ∀ n : Nat, n < 50 (should fail)"
  let result ← checkResult (p := ∀ n : Nat, n < 50) "test_lt_50"
    { numTests := 100, quiet := true, shrink := true, healthChecks := false }
  match result with
  | .success _ => throw <| IO.userError "  ✗ Expected failure but test passed"
  | .failure ce shrinks _ =>
    IO.println s!"  ✓ Correctly found counterexample: {ce} (after {shrinks} shrinks)"
  | .gaveUp n => throw <| IO.userError s!"  ⚠ Gave up after {n} invalid examples"
  | .error msg => throw <| IO.userError s!"  Error: {msg}"

/-- Test commutativity of addition -/
def testCommutativity : IO Unit := do
  IO.println "Testing: ∀ n m : Nat, n + m = m + n"
  let result ← checkResult (p := ∀ n m : Nat, n + m = m + n) "test_add_comm"
    { numTests := 50, quiet := false, healthChecks := false }
  match result with
  | .success n => IO.println s!"  ✓ Passed {n} tests"
  | .failure ce _ _ => throw <| IO.userError s!"  ✗ Unexpected failure: {ce}"
  | .gaveUp n => throw <| IO.userError s!"  ⚠ Gave up after {n} invalid examples"
  | .error msg => throw <| IO.userError s!"  Error: {msg}"

/-- Test a failing property about pairs -/
def testFailingPairProperty : IO Unit := do
  IO.println "Testing: ∀ n m : Nat, n ≤ m (should fail)"
  let result ← checkResult (p := ∀ n m : Nat, n ≤ m) "test_le"
    { numTests := 100, quiet := true, shrink := true, healthChecks := false }
  match result with
  | .success _ => throw <| IO.userError "  ✗ Expected failure but test passed"
  | .failure ce shrinks _ =>
    IO.println s!"  ✓ Correctly found counterexample: {ce} (after {shrinks} shrinks)"
  | .gaveUp n => throw <| IO.userError s!"  ⚠ Gave up after {n} invalid examples"
  | .error msg => throw <| IO.userError s!"  Error: {msg}"

/-- Test example database persistence -/
def testExampleDb : IO Unit := do
  IO.println "Testing: Example database persistence"

  -- First run: find a counterexample
  let result1 ← checkResult (p := ∀ n : Nat, n < 100) "test_persistence"
    { numTests := 200, quiet := true, shrink := true, useExampleDb := true, healthChecks := false }

  match result1 with
  | .failure ce1 _ _ =>
    IO.println s!"  First run found: {ce1}"

    -- Second run: should replay the saved example
    let result2 ← checkResult (p := ∀ n : Nat, n < 100) "test_persistence"
      { numTests := 1, quiet := false, useExampleDb := true, healthChecks := false }

    match result2 with
    | .failure ce2 _ _ =>
      IO.println s!"  Second run replayed: {ce2}"
      IO.println s!"  ✓ Example database working"
    | _ => throw <| IO.userError "  ✗ Failed to replay saved example"
  | _ => throw <| IO.userError "  ✗ First run didn't find counterexample"

/-- Test Bool property -/
def testBoolProperty : IO Unit := do
  IO.println "Testing: ∀ b : Bool, b || !b = true"
  let result ← checkResult (p := ∀ b : Bool, b || !b = true) "test_bool_or_not"
    { numTests := 20, quiet := false, healthChecks := false }
  match result with
  | .success n => IO.println s!"  ✓ Passed {n} tests"
  | .failure ce _ _ => throw <| IO.userError s!"  ✗ Unexpected failure: {ce}"
  | .gaveUp n => throw <| IO.userError s!"  ⚠ Gave up after {n} invalid examples"
  | .error msg => throw <| IO.userError s!"  Error: {msg}"

/-- Test health checks are triggered -/
def testHealthChecks : IO Unit := do
  IO.println "Testing: Health check warnings (expect 'data too large' warning)"
  -- This should trigger the "data too large" warning since we're using 64KB buffers
  let _ ← checkResult (p := ∀ n : Nat, n + 0 = n) "test_health"
    { numTests := 10, quiet := false, maxBytes := 64 * 1024, healthChecks := true }
  IO.println "  ✓ Health checks ran"

/-- Main test runner -/
def main : IO Unit := do
  IO.println "=== ConjectureTestable Integration Tests ===\n"

  IO.println "--- Basic Property Tests ---"
  testPassingProperty
  testFailingProperty

  IO.println "\n--- Pair Property Tests ---"
  testCommutativity
  testFailingPairProperty

  IO.println "\n--- Bool Property Tests ---"
  testBoolProperty

  IO.println "\n--- Example Database Tests ---"
  testExampleDb

  IO.println "\n--- Health Check Tests ---"
  testHealthChecks

  IO.println "\n=== All integration tests passed! ==="

end ConjectureTestableTest

def main : IO Unit := ConjectureTestableTest.main
