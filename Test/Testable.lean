/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Plausible.Testable
import Plausible.MetaTestable

open Plausible

structure MyType where
  x : Nat
  y : Nat
  h : x ≤ y
  deriving Repr

instance : Shrinkable MyType where
  shrink := fun ⟨x, y, _⟩ =>
    let proxy := Shrinkable.shrink (x, y - x)
    proxy.map (fun (fst, snd) => ⟨fst, fst + snd, by omega⟩)

instance : SampleableExt MyType :=
  SampleableExt.mkSelfContainedSimple do
    let x ← SampleableExt.interpSample Nat
    let xyDiff ← SampleableExt.interpSample Nat
    return ⟨x, x + xyDiff, by omega⟩

#eval Testable.check <| ∀ a b : MyType, a.y ≤ b.x → a.x ≤ b.y

set_option trace.profiler true in
#eval MetaTestable.check <| ∀ a b : MyType, a.y ≤ b.x → a.x ≤ b.y
