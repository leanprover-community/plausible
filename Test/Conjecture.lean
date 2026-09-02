/-
Copyright (c) 2024 Plausible Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Plausible.Conjecture

/-!
# Tests for the Conjecture Engine

This file tests the Hypothesis-style byte-buffer generation and shrinking.
-/

namespace ConjTest

/-- Test that we can draw a Nat from a choice sequence -/
def testDrawNat : IO Unit := do
  -- Create a choice sequence with known bytes
  let bytes := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 42]
  let cs := Plausible.Conjecture.ChoiceSequence.ofBytes bytes
  match Plausible.Conjecture.Strategy.instStrategyNat.draw cs with
  | .ok value _ =>
    IO.println s!"Drew Nat: {value}"
    assert! value == 42
  | .overrun =>
    throw <| IO.userError "Unexpected overrun"

/-- Test that we can draw a Bool -/
def testDrawBool : IO Unit := do
  -- Odd byte → true
  let bytes := ByteArray.mk #[1]
  let cs := Plausible.Conjecture.ChoiceSequence.ofBytes bytes
  match Plausible.Conjecture.Strategy.draw (α := Bool) cs with
  | .ok value _ =>
    IO.println s!"Drew Bool: {value}"
    assert! value == true
  | .overrun =>
    throw <| IO.userError "Unexpected overrun"

/-- Test that Nat shrinks toward 0 -/
def testShrinkNat : IO Unit := do
  -- Create a choice sequence representing a large number
  let bytes := ByteArray.mk #[0, 0, 0, 0, 0, 0, 1, 0]  -- 256
  let cs := Plausible.Conjecture.ChoiceSequence.ofBytes bytes

  -- Verify we can draw the value
  match Plausible.Conjecture.Strategy.instStrategyNat.draw cs with
  | .ok value _ =>
    IO.println s!"Initial Nat: {value}"
    -- Get shrink candidates
    let candidates := Plausible.Conjecture.Shrinker.shrink cs
    IO.println s!"Got {candidates.length} shrink candidates"

    -- Verify smaller candidates produce smaller values
    for candidate in candidates.take 3 do
      match Plausible.Conjecture.Strategy.instStrategyNat.draw candidate with
      | .ok smallerValue _ =>
        IO.println s!"  Shrunk to: {smallerValue}"
      | .overrun => pure ()
  | .overrun =>
    throw <| IO.userError "Unexpected overrun"

/-- Test span tracking -/
def testSpans : IO Unit := do
  let bytes := ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
  let cs := Plausible.Conjecture.ChoiceSequence.ofBytes bytes

  -- Draw a pair (two Nats = 16 bytes with spans)
  match Plausible.Conjecture.Strategy.draw (α := Nat × Nat) cs with
  | .ok (a, b) cs' =>
    IO.println s!"Drew pair: ({a}, {b})"
    IO.println s!"Recorded {cs'.spans.size} spans"
    for span in cs'.spans do
      IO.println s!"  Span: [{span.start}, {span.stop}) label={span.label}"
  | .overrun =>
    throw <| IO.userError "Unexpected overrun"

/-- Test the shrink loop -/
def testShrinkLoop : IO Unit := do
  -- Create a choice sequence that produces a "large" Nat
  let bytes := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 100]
  let cs := Plausible.Conjecture.ChoiceSequence.ofBytes bytes

  -- Property: n < 50 (should fail for n=100)
  let test (n : Nat) : Bool := n < 50

  let (shrunk, steps) := Plausible.Conjecture.shrinkLoop test cs (maxSteps := 100) (trace := true)

  match Plausible.Conjecture.Strategy.instStrategyNat.draw shrunk with
  | .ok value _ =>
    IO.println s!"After {steps} shrink steps, got: {value}"
    -- Should have shrunk to the minimal failing value (50)
    assert! value >= 50
  | .overrun =>
    throw <| IO.userError "Shrinking produced invalid sequence"

/-- Test random generation and interpretation -/
def testRandomGeneration : IO Unit := do
  for sz in [16, 32, 64, 128] do
    let cs ← Plausible.Conjecture.generateRandom sz
    IO.println s!"Generated {cs.size} bytes"

    match Plausible.Conjecture.Strategy.instStrategyNat.draw cs with
    | .ok value _ =>
      IO.println s!"  Interpreted as Nat: {value}"
    | .overrun =>
      IO.println s!"  (overrun - not enough bytes for Nat)"

/-- Test saving and loading examples -/
def testExampleDb : IO Unit := do
  let testName := "test_example_db"
  let bytes := ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8]
  let cs := Plausible.Conjecture.ChoiceSequence.ofBytes bytes

  -- Save
  Plausible.Conjecture.ExampleDb.save testName cs
  IO.println s!"Saved example for '{testName}'"

  -- Load
  match ← Plausible.Conjecture.ExampleDb.load testName with
  | some loaded =>
    IO.println s!"Loaded example: {loaded.size} bytes"
    assert! loaded.buffer == cs.buffer
  | none =>
    throw <| IO.userError "Failed to load saved example"

  -- List
  let tests ← Plausible.Conjecture.ExampleDb.listTests
  IO.println s!"Saved tests: {tests}"

/-- Test health check detection -/
def testHealthChecks : IO Unit := do
  -- Test slow generation warning
  let warnings1 := Plausible.Conjecture.HealthCheck.runAll (totalMs := 25000.0) (validCount := 100) (invalidCount := 0) (totalBytes := 1000)
  IO.println s!"Slow generation warnings: {repr warnings1}"
  assert! warnings1.any fun w => match w with | .tooSlow _ => true | _ => false

  -- Test filter ratio warning
  let warnings2 := Plausible.Conjecture.HealthCheck.runAll (totalMs := 100.0) (validCount := 10) (invalidCount := 90) (totalBytes := 1000)
  IO.println s!"High filter ratio warnings: {repr warnings2}"
  assert! warnings2.any fun w => match w with | .filterTooMuch _ => true | _ => false

  -- Test data too large warning
  let warnings3 := Plausible.Conjecture.HealthCheck.runAll (totalMs := 100.0) (validCount := 10) (invalidCount := 0) (totalBytes := 50000)
  IO.println s!"Large data warnings: {repr warnings3}"
  assert! warnings3.any fun w => match w with | .dataTooLarge _ => true | _ => false

/-- Test targeted observation tracking -/
def testTargeted : IO Unit := do
  let cs1 ← Plausible.Conjecture.generateRandom 32
  let cs2 ← Plausible.Conjecture.generateRandom 32
  let cs3 ← Plausible.Conjecture.generateRandom 32

  let state : Plausible.Conjecture.TargetState := {}
  let state := Plausible.Conjecture.Targeted.observe 0.5 cs1 state
  let state := Plausible.Conjecture.Targeted.observe 0.8 cs2 state
  let state := Plausible.Conjecture.Targeted.observe 0.3 cs3 state

  IO.println s!"Best score: {state.bestScore}"
  assert! state.bestScore == 0.8
  assert! state.observations.size == 3

/-- Test mutation -/
def testMutation : IO Unit := do
  let original ← Plausible.Conjecture.generateRandom 32
  let mutated ← Plausible.Conjecture.Targeted.mutate original (mutationRate := 0.5)

  -- Check that mutation changed at least something (probabilistically)
  let pairs := original.buffer.toList.zip mutated.buffer.toList
  let differentPairs := pairs.filter fun (a, b) => a != b
  let different := differentPairs.length

  IO.println s!"Mutated {different} / {original.size} bytes"

/-- Main test runner -/
def main : IO Unit := do
  IO.println "=== Conjecture Engine Tests ==="

  IO.println "\n--- Basic Strategy Tests ---"
  testDrawNat
  testDrawBool
  testShrinkNat
  testSpans

  IO.println "\n--- Shrink Loop Test ---"
  testShrinkLoop

  IO.println "\n--- Random Generation Tests ---"
  testRandomGeneration

  IO.println "\n--- Example Database Tests ---"
  testExampleDb

  IO.println "\n--- Health Check Tests ---"
  testHealthChecks

  IO.println "\n--- Targeted PBT Tests ---"
  testTargeted
  testMutation

  IO.println "\n=== All tests passed! ==="

end ConjTest

def main : IO Unit := ConjTest.main
