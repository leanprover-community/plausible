# Plausible
A property testing framework for Lean 4 that integrates into the tactic framework.

## Usage
If you are using built in types Plausible is usually able to handle them already:
```lean
import Plausible

example (xs ys : Array Nat) : xs.size = ys.size → xs = ys := by
  /--
  ===================
  Found a counter-example!
  xs := #[0]
  ys := #[1]
  guard: 1 = 1
  issue: #[0] = #[1] does not hold
  (0 shrinks)
  -------------------
  -/
  plausible

#eval Plausible.Testable.check <| ∀ (xs ys : Array Nat), xs.size = ys.size → xs = ys
```

If you are defining your own type it needs instances of `Repr`, `Plausible.Shrinkable` and
`Plausible.SampleableExt` (or `Plausible.Arbitrary`):
```lean
import Plausible

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
  SampleableExt.mkSelfContained do
    let x ← SampleableExt.interpSample Nat
    let xyDiff ← SampleableExt.interpSample Nat
    return ⟨x, x + xyDiff, by omega⟩

-- No counter example found
#eval Testable.check <| ∀ a b : MyType, a.y ≤ b.x → a.x ≤ b.y
```
For more documentation refer to the module docs.

**Deriving Instance for `Arbitrary`** (for algebraic data types)              
Users can write `deriving Arbitrary` after an inductive type definition, i.e.
```lean 
inductive Foo where
  ...
  deriving Arbitrary
```

Alternatively, users can also write `deriving instance Arbitrary for T1, ..., Tn` as a top-level command to derive `Arbitrary` instances for types `T1, ..., Tn` simultaneously.

