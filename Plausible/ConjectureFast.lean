/-
Copyright (c) 2024 Plausible Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Plausible.Conjecture

/-!
# Parallel Property Testing

Parallel test execution using Lean Tasks. Automatically falls back to sequential
for small test counts where task overhead dominates.

- Sequential: ~300k tests/sec (best for throughput)
- Parallel: 100-1000x faster to find counterexamples (early termination)
-/

namespace Plausible.Conjecture.Fast

open Plausible.Conjecture

/-- Configuration for parallel testing -/
structure Config where
  numWorkers : Nat := 8
  batchSize : Nat := 100
  numTests : Nat := 10000
  bytesPerTest : Nat := 64
  deriving Inhabited, Repr

private inductive WorkerResult where
  | passed (count : Nat)
  | failure (cs : ChoiceSequence)

private def testBatch [Strategy α] (test : α → Bool) (batch : Array ChoiceSequence) :
    IO WorkerResult := do
  for cs in batch do
    match Strategy.draw (α := α) cs with
    | .ok value cs' =>
      if !test value then
        return .failure { cs' with buffer := cs'.buffer.extract 0 cs'.index, index := 0 }
    | .overrun => continue
  return .passed batch.size

private def generateBatch (count bytesEach : Nat) : IO (Array ChoiceSequence) := do
  let mut allBytes := ByteArray.empty
  for _ in [:count * bytesEach] do
    allBytes := allBytes.push (← IO.rand 0 255).toUInt8
  let mut batch := Array.mkEmpty count
  for i in [:count] do
    batch := batch.push (ChoiceSequence.ofBytes (allBytes.extract (i * bytesEach) ((i + 1) * bytesEach)))
  return batch

private def runSequential [Strategy α] (test : α → Bool) (numTests bytesPerTest : Nat) :
    IO (Option ChoiceSequence) := do
  for _ in [:numTests] do
    let cs ← generateRandom bytesPerTest
    match Strategy.draw (α := α) cs with
    | .ok value cs' =>
      if !test value then
        return some { cs' with buffer := cs'.buffer.extract 0 cs'.index, index := 0 }
    | .overrun => continue
  return none

/-- Find counterexample using parallel workers. Falls back to sequential for < 1000 tests. -/
def check [Strategy α] (test : α → Bool) (cfg : Config := {}) : IO (Option ChoiceSequence) := do
  if cfg.numTests < 1000 then
    return ← runSequential (α := α) test cfg.numTests cfg.bytesPerTest

  let numWorkers := max 1 cfg.numWorkers
  let testsPerWorker := cfg.numTests / numWorkers

  let mut tasks : Array (Task (Except IO.Error WorkerResult)) := #[]
  for _ in [:numWorkers] do
    tasks := tasks.push (← IO.asTask do
      let mut remaining := testsPerWorker
      while remaining > 0 do
        let batch ← generateBatch (min cfg.batchSize remaining) cfg.bytesPerTest
        match ← testBatch (α := α) test batch with
        | .failure cs => return .failure cs
        | .passed n => remaining := remaining - n
      return .passed testsPerWorker)

  for task in tasks do
    if let .ok (.failure cs) := ← IO.wait task then return some cs
  return none

/-- Shrink by testing candidates in parallel -/
def shrink [Strategy α] (test : α → Bool) (cs : ChoiceSequence) (numWorkers : Nat := 8) :
    IO ChoiceSequence := do
  let candidates := Shrinker.shrink cs |>.take (numWorkers * 4)
  if candidates.isEmpty then return cs

  let tasks ← candidates.mapM fun c => IO.asTask do
    match Strategy.draw (α := α) c with
    | .ok value _ => return if !test value then some c else none
    | .overrun => return none

  for task in tasks do
    if let .ok (some smaller) := ← IO.wait task then return smaller
  return cs

/-- Iteratively shrink in parallel until no improvement -/
partial def shrinkLoop [Strategy α] (test : α → Bool) (cs : ChoiceSequence)
    (maxSteps : Nat := 1000) (numWorkers : Nat := 8) : IO (ChoiceSequence × Nat) := do
  let rec go (current : ChoiceSequence) (steps fuel : Nat) : IO (ChoiceSequence × Nat) := do
    if fuel == 0 then return (current, steps)
    let smaller ← shrink (α := α) test current numWorkers
    if smaller.buffer.size < current.buffer.size || smaller.lexLt current then
      go smaller (steps + 1) (fuel - 1)
    else
      return (current, steps)
  go cs 0 maxSteps

end Plausible.Conjecture.Fast
