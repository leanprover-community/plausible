/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Plausible

/-!
Demonstrate that Plausible can handle the basic types from core:
- Sum
- Sigma
- Unit
- Prod
- Bool
- Nat
- Fin
- UIntX
- BitVec
- Char
- Option
- List
- String
- Array
-/


/-- error: Counterexample identified -/
#guard_msgs in
example (a b : Sum Nat Nat) : a = b := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (a b : Σ n : Nat, Nat) : a.fst = b.snd := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (a b : Unit) : a ≠ b := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (x y : Nat × Unit) : x = y := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (a b : Bool) : a = b :=  by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (a b c : Nat) : a + (b - c) = (a + b) - c := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (a : Fin (n + 1)) : a + 1 > a := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (a : BitVec n) : a + 1 > a := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (a : UInt8) : a - 1 < a := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (a : UInt16) : a - 1 < a := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (a : UInt32) : a - 1 < a := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (a : UInt64) : a - 1 < a := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (a : USize) : a - 1 < a := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (a : Char) : a ≠ a := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (a : Option Char) : a ≠ a := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (xs ys : List Nat) : xs.length = ys.length → xs = ys := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (xs ys : String) : xs.length = ys.length → xs = ys := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (xs ys : Array Nat) : xs.size = ys.size → xs = ys := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
example (xs : List Int) (f : Int → Int) : xs.map f = xs := by
  plausible (config := {quiet := true})

/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a : Sum Nat Nat) : a = a := by
  plausible

/--
warning: Gave up after failing to generate values that fulfill the preconditions 100 times.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a b : Sum Nat Nat) : a ≠ a → a = b := by
  plausible (config := {numInst := 100})

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/slim_check.20giving.20wrong.20counterexamples.3F/near/420008365
open Nat in
/--
info: Unable to find a counter-example
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
theorem testBit_pred :
    testBit (pred x) i = (decide (0 < x) &&
      (Bool.xor ((List.range i).all fun j => ! testBit x j) (testBit x i))) := by
  plausible

/-- error: Counterexample identified -/
#guard_msgs in
theorem ulift_nat (f : ULift.{1} Nat) : f = ⟨0⟩ := by
  plausible (config := {quiet := true})

/-- error: Counterexample identified -/
#guard_msgs in
theorem type_u (α : Type u) (l : List α) : l = l ++ l := by
  plausible (config := {quiet := true})
