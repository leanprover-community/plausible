/-
Copyright (c) 2024 Plausible Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Plausible.Conjecture
import Plausible.ConjectureFast
import Plausible.ShrinkSearch

/-! # Conjecture Engine Benchmarks -/

namespace ConjectureBench

open Plausible.Conjecture
open Plausible.Conjecture.Fast

def timeMs (action : IO α) : IO (α × Float) := do
  let start ← IO.monoMsNow
  let result ← action
  return (result, (← IO.monoMsNow) - start |>.toFloat)

def fmt (n : Float) : String := s!"{n.round}"

def benchSeq (numTests bytes : Nat) : IO Float := do
  let (_, ms) ← timeMs do
    for _ in [:numTests] do
      let _ ← generateRandom bytes
  return ms

def benchPar (numTests workers bytes : Nat) (test : Nat → Bool) : IO Float := do
  let (_, ms) ← timeMs <| check (α := Nat) test { numTests, numWorkers := workers, bytesPerTest := bytes }
  return ms

def main : IO Unit := do
  IO.println "=== Conjecture Benchmarks ===\n"
  let bytes := 64

  IO.println "Throughput:"
  for n in [100000, 1000000] do
    let ms ← benchSeq n bytes
    IO.println s!"  {n}: {fmt ms}ms ({fmt (n.toFloat / ms * 1000)}/s)"

  IO.println "\nBug finding (n < 1000, fails ~100%):"
  for n in [100000, 1000000] do
    let seqMs ← benchSeq n bytes
    for w in [2, 8] do
      let parMs ← benchPar n w bytes (· < 1000)
      IO.println s!"  {n} ({w}w): {fmt parMs}ms ({fmt (seqMs / parMs)}x)"

  IO.println "\nRare bugs (top byte = 0, ~0.4%):"
  for n in [100000, 500000] do
    let seqMs ← benchSeq n bytes
    for w in [2, 8] do
      let parMs ← benchPar n w bytes (fun x => (x >>> 56) != 0)
      IO.println s!"  {n} ({w}w): {fmt parMs}ms ({fmt (seqMs / parMs)}x)"

  IO.println "\nShrinking (4096 with test n < 50):"
  let cs := ChoiceSequence.ofBytes (ByteArray.mk #[0, 0, 0, 0, 0, 0, 0x10, 0x00])
  let test := fun n : Nat => decide (n < 50)

  let (shrunk, steps) := Plausible.Conjecture.shrinkLoop test cs
  if let .ok n _ := Strategy.draw (α := Nat) shrunk then
    IO.println s!"  Byte-halving: → {n} ({steps} steps)"

  let minimal := Plausible.Nat.shrinkToMinimal test 4096
  IO.println s!"  Binary search: → {minimal}"

end ConjectureBench

def main : IO Unit := ConjectureBench.main
