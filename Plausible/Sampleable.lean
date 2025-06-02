/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
import Lean.Elab.Command
import Lean.Meta.Eval
import Plausible.Gen

/-!
# `SampleableExt` Class

This class permits the creation samples of a given type
controlling the size of those values using the `Gen` monad.

# `Shrinkable` Class

This class helps minimize examples by creating smaller versions of
given values.

When testing a proposition like `∀ n : Nat, Prime n → n ≤ 100`,
`Plausible` requires that `Nat` have an instance of `SampleableExt` and for
`Prime n` to be decidable.  `Plausible` will then use the instance of
`SampleableExt` to generate small examples of Nat and progressively increase
in size. For each example `n`, `Prime n` is tested. If it is false,
the example will be rejected (not a test success nor a failure) and
`Plausible` will move on to other examples. If `Prime n` is true,
`n ≤ 100` will be tested. If it is false, `n` is a counter-example of
`∀ n : Nat, Prime n → n ≤ 100` and the test fails. If `n ≤ 100` is true,
the test passes and `Plausible` moves on to trying more examples.

## Main definitions

* `SampleableExt` class
* `Shrinkable` class

### `SampleableExt`

`SampleableExt` can be used in two ways. The first (and most common)
is to simply generate values of a type directly using the `Gen` monad,
if this is what you want to do then `SampleableExt.mkSelfContained` is
the way to go.

Furthermore it makes it possible to express generators for types that
do not lend themselves to introspection, such as `Nat → Nat`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.
For that purpose, `SampleableExt` provides a proxy representation
`proxy` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type. If you
are using it in the first way, this proxy type will simply be the type
itself and the `interp` function `id`.

### `Shrinkable`

Given an example `x : α`, `Shrinkable α` gives us a way to shrink it
and suggest simpler examples.

## Shrinking

Shrinking happens when `Plausible` finds a counter-example to a
property.  It is likely that the example will be more complicated than
necessary so `Plausible` proceeds to shrink it as much as
possible. Although equally valid, a smaller counter-example is easier
for a user to understand and use.

The `Shrinkable` class, , has a `shrink` function so that we can use
specialized knowledge while shrinking a value. It is not responsible
for the whole shrinking process however. It only has to take one step
in the shrinking process. `Plausible` will repeatedly call `shrink`
until no more steps can be taken. Because `shrink` guarantees that the
size of the candidates it produces is strictly smaller than the
argument, we know that `Plausible` is guaranteed to terminate.

## Tags

random testing

## References

* https://hackage.haskell.org/package/QuickCheck

-/

namespace Plausible

open Random Gen

universe u v
variable {α β : Type _}

/-- Given an example `x : α`, `Shrinkable α` gives us a way to shrink it
and suggest simpler examples. -/
class Shrinkable (α : Type u) where
  shrink : (x : α) → List α := fun _ => []

/-- `SampleableExt` can be used in two ways. The first (and most common)
is to simply generate values of a type directly using the `Gen` monad,
if this is what you want to do then `SampleableExt.mkSelfContained` is
the way to go.

Furthermore it makes it possible to express generators for types that
do not lend themselves to introspection, such as `Nat → Nat`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.
For that purpose, `SampleableExt` provides a proxy representation
`proxy` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type. -/
class SampleableExt (α : Sort u) where
  proxy : Type v
  [proxyRepr : Repr proxy]
  [shrink : Shrinkable proxy]
  sample : Gen proxy
  interp : proxy → α

attribute [instance] SampleableExt.proxyRepr
attribute [instance] SampleableExt.shrink

namespace SampleableExt

/-- Use to generate instance whose purpose is to simply generate values
of a type directly using the `Gen` monad -/
def mkSelfContained [Repr α] [Shrinkable α] (sample : Gen α) : SampleableExt α where
  proxy := α
  proxyRepr := inferInstance
  shrink := inferInstance
  sample := sample
  interp := id

/-- First samples a proxy value and interprets it. Especially useful if
the proxy and target type are the same. -/
def interpSample (α : Type u) [SampleableExt α] : Gen α :=
  SampleableExt.interp <$> SampleableExt.sample

end SampleableExt

section Shrinkers

instance [Shrinkable α] [Shrinkable β] : Shrinkable (Sum α β) where
  shrink s :=
    match s with
    | .inl l => Shrinkable.shrink l |>.map .inl
    | .inr r => Shrinkable.shrink r |>.map .inr

instance Unit.shrinkable : Shrinkable Unit where
  shrink _ := []

/-- `Nat.shrink' n` creates a list of smaller natural numbers by
successively dividing `n` by 2 . For example, `Nat.shrink 5 = [2, 1, 0]`. -/
def Nat.shrink (n : Nat) : List Nat :=
  if h : 0 < n then
    let m := n/2
    m :: shrink m
  else
    []

instance Nat.shrinkable : Shrinkable Nat where
  shrink := Nat.shrink

instance Fin.shrinkable {n : Nat} : Shrinkable (Fin n.succ) where
  shrink m := Nat.shrink m |>.map (Fin.ofNat _)

instance BitVec.shrinkable {n : Nat} : Shrinkable (BitVec n) where
  shrink m := Nat.shrink m.toNat |>.map (BitVec.ofNat n)

instance UInt8.shrinkable : Shrinkable UInt8 where
  shrink m := Nat.shrink m.toNat |>.map UInt8.ofNat

instance UInt16.shrinkable : Shrinkable UInt16 where
  shrink m := Nat.shrink m.toNat |>.map UInt16.ofNat

instance UInt32.shrinkable : Shrinkable UInt32 where
  shrink m := Nat.shrink m.toNat |>.map UInt32.ofNat

instance UInt64.shrinkable : Shrinkable UInt64 where
  shrink m := Nat.shrink m.toNat |>.map UInt64.ofNat

instance USize.shrinkable : Shrinkable USize where
  shrink m := Nat.shrink m.toNat |>.map USize.ofNat

/-- `Int.shrinkable` operates like `Nat.shrinkable` but also includes the negative variants. -/
instance Int.shrinkable : Shrinkable Int where
  shrink n :=
    let converter n :=
      let int := Int.ofNat n
      [int, -int]
    Nat.shrink n.natAbs |>.flatMap converter

instance Bool.shrinkable : Shrinkable Bool := {}
instance Char.shrinkable : Shrinkable Char := {}

instance Option.shrinkable [Shrinkable α] : Shrinkable (Option α) where
  shrink o :=
    match o with
    | some x => Shrinkable.shrink x |>.map .some
    | none => []

instance Prod.shrinkable [shrA : Shrinkable α] [shrB : Shrinkable β] :
    Shrinkable (Prod α β) where
  shrink := fun (fst,snd) =>
    let shrink1 := shrA.shrink fst |>.map fun x => (x, snd)
    let shrink2 := shrB.shrink snd |>.map fun x => (fst, x)
    shrink1 ++ shrink2

instance Sigma.shrinkable [shrA : Shrinkable α] [shrB : Shrinkable β] :
    Shrinkable ((_ : α) × β) where
  shrink := fun ⟨fst,snd⟩ =>
    let shrink1 := shrA.shrink fst |>.map fun x => ⟨x, snd⟩
    let shrink2 := shrB.shrink snd |>.map fun x => ⟨fst, x⟩
    shrink1 ++ shrink2

open Shrinkable

/-- Shrink a list of a shrinkable type, either by discarding an element or shrinking an element. -/
instance List.shrinkable [Shrinkable α] : Shrinkable (List α) where
  shrink := fun L =>
    (L.mapIdx fun i _ => L.eraseIdx i) ++
    (L.mapIdx fun i a => (shrink a).map fun a' => L.modify i fun _ => a').flatten

instance ULift.shrinkable [Shrinkable α] : Shrinkable (ULift α) where
  shrink u := (shrink u.down).map ULift.up

instance String.shrinkable : Shrinkable String where
  shrink s := (shrink s.toList).map String.mk

instance Array.shrinkable [Shrinkable α] : Shrinkable (Array α) where
  shrink xs := (shrink xs.toList).map Array.mk

instance Subtype.shrinkable {α : Type u} {β : α → Prop} [Shrinkable α] [∀ x, Decidable (β x)] : Shrinkable {x : α // β x} where
  shrink x :=
    let val := x.val
    let candidates := shrink val
    let filter x := do
      if h : β x then
        some ⟨x, h⟩
      else
        none
    candidates.filterMap filter

end Shrinkers

section Samplers

open SampleableExt

instance Sum.SampleableExt [SampleableExt α] [SampleableExt β] : SampleableExt (Sum α β) where
  proxy := Sum (proxy α) (proxy β)
  sample := do
    match ← chooseAny Bool with
    | true => return .inl (← sample)
    | false => return .inr (← sample)
  interp s :=
    match s with
    | .inl l => .inl (interp l)
    | .inr r => .inr (interp r)

instance Unit.sampleableExt : SampleableExt Unit :=
  mkSelfContained (return ())

instance [SampleableExt α] [SampleableExt β] : SampleableExt ((_ : α) × β) where
  proxy := (_ : proxy α) × proxy β
  sample := do
    let p ← prodOf sample sample
    return ⟨p.fst, p.snd⟩
  interp s := ⟨interp s.fst, interp s.snd⟩

instance Nat.sampleableExt : SampleableExt Nat :=
  mkSelfContained (do choose Nat 0 (← getSize) (Nat.zero_le _))

instance Fin.sampleableExt {n : Nat} : SampleableExt (Fin (n.succ)) :=
  mkSelfContained do
    let m ← choose Nat 0 (min (← getSize) n) (Nat.zero_le _)
    return (Fin.ofNat _ m)

instance BitVec.sampleableExt {n : Nat} : SampleableExt (BitVec n) :=
  mkSelfContained do
    let m ← choose Nat 0 (min (← getSize) (2^n)) (Nat.zero_le _)
    return BitVec.ofNat _ m

instance UInt8.SampleableExt : SampleableExt UInt8 :=
  mkSelfContained do
    let n ← choose Nat 0 (min (← getSize) UInt8.size) (Nat.zero_le _)
    return UInt8.ofNat n

instance UInt16.SampleableExt : SampleableExt UInt16 :=
  mkSelfContained do
    let n ← choose Nat 0 (min (← getSize) UInt16.size) (Nat.zero_le _)
    return UInt16.ofNat n

instance UInt32.SampleableExt : SampleableExt UInt32 :=
  mkSelfContained do
    let n ← choose Nat 0 (min (← getSize) UInt32.size) (Nat.zero_le _)
    return UInt32.ofNat n

instance UInt64.SampleableExt : SampleableExt UInt64 :=
  mkSelfContained do
    let n ← choose Nat 0 (min (← getSize) UInt64.size) (Nat.zero_le _)
    return UInt64.ofNat n

instance USize.SampleableExt : SampleableExt USize :=
  mkSelfContained do
    let n ← choose Nat 0 (min (← getSize) USize.size) (Nat.zero_le _)
    return USize.ofNat n

instance Int.sampleableExt : SampleableExt Int :=
  mkSelfContained do
    choose Int (-(← getSize)) (← getSize) (by omega)

instance Bool.sampleableExt : SampleableExt Bool :=
  mkSelfContained <| chooseAny Bool

/-- This can be specialized into customized `SampleableExt Char` instances.
The resulting instance has `1 / length` chances of making an unrestricted choice of characters
and it otherwise chooses a character from `chars` with uniform probabilities. -/
def Char.sampleable (length : Nat) (chars : List Char) (pos : 0 < chars.length) :
    SampleableExt Char :=
  mkSelfContained do
    let x ← choose Nat 0 length (Nat.zero_le _)
    if x.val == 0 then
      let n ← interpSample Nat
      pure <| Char.ofNat n
    else
      elements chars pos

instance Char.sampleableDefault : SampleableExt Char :=
  Char.sampleable 3 " 0123abcABC:,;`\\/".toList (by decide)

instance Option.sampleableExt [SampleableExt α] : SampleableExt (Option α) where
  proxy := Option (proxy α)
  sample := do
    match ← chooseAny Bool with
    | true => return none
    | false => return some (← sample)
  interp o := o.map interp

instance Prod.sampleableExt {α : Type u} {β : Type v} [SampleableExt α] [SampleableExt β] :
    SampleableExt (α × β) where
  proxy := Prod (proxy α) (proxy β)
  proxyRepr := inferInstance
  shrink := inferInstance
  sample := prodOf sample sample
  interp := Prod.map interp interp

instance Prop.sampleableExt : SampleableExt Prop where
  proxy := Bool
  proxyRepr := inferInstance
  sample := interpSample Bool
  shrink := inferInstance
  interp := Coe.coe

instance List.sampleableExt [SampleableExt α] : SampleableExt (List α) where
  proxy := List (proxy α)
  sample := Gen.listOf sample
  interp := List.map interp

instance ULift.sampleableExt [SampleableExt α] : SampleableExt (ULift α) where
  proxy := proxy α
  sample := sample
  interp a := ⟨interp a⟩

instance String.sampleableExt : SampleableExt String :=
  mkSelfContained do return String.mk (← Gen.listOf (Char.sampleableDefault.sample))

instance Array.sampleableExt [SampleableExt α] : SampleableExt (Array α) where
  proxy := Array (proxy α)
  sample := Gen.arrayOf sample
  interp := Array.map interp

end Samplers

/-- An annotation for values that should never get shrunk. -/
def NoShrink (α : Type u) := α

namespace NoShrink

def mk (x : α) : NoShrink α := x
def get (x : NoShrink α) : α := x

instance inhabited [inst : Inhabited α] : Inhabited (NoShrink α) := inst
instance repr [inst : Repr α] : Repr (NoShrink α) := inst

instance shrinkable : Shrinkable (NoShrink α) where
  shrink := fun _ => []

instance sampleableExt [SampleableExt α] [Repr α] : SampleableExt (NoShrink α) :=
  SampleableExt.mkSelfContained <| (NoShrink.mk ∘ SampleableExt.interp) <$> SampleableExt.sample

end NoShrink

/--
Print (at most) 10 samples of a given type to stdout for debugging.
-/
def printSamples {t : Type u} [Repr t] (g : Gen t) : IO PUnit := do
-- TODO: this should be a global instance
  letI : MonadLift Id IO := ⟨fun f => pure <| Id.run f⟩
  do
    -- we can't convert directly from `Rand (List t)` to `RandT IO (List Std.Format)`
    -- (and `RandT IO (List t)` isn't type-correct without
    -- https://github.com/leanprover/lean4/issues/3011), so go via an intermediate
    let xs : List Std.Format ← Plausible.runRand <| Rand.down <| do
      let xs : List t ← (List.range 10).mapM (ReaderT.run g ∘ ULift.up)
      pure <| ULift.up (xs.map repr)
    for x in xs do
      IO.println s!"{x}"

open Lean Meta Elab

/--
`e` is a type to sample from, this can either be a type that implements `SampleableExt` or `Gen α`
directly. For this return:
- the universe level of the `Type u` that the relevant type to sample lives in.
- the actual type `α` to sample from
- a `Repr α` instance
- a `Gen α` generator to run in order to sample
-/
private def mkGenerator (e : Expr) : MetaM (Level × Expr × Expr × Expr) := do
  let exprTyp ← inferType e
  let .sort u ← whnf (← inferType exprTyp) | throwError m!"{exprTyp} is not a type"
  let .succ u := u | throwError m!"{exprTyp} is not a type with computational content"
  match_expr exprTyp with
  | Gen α =>
    let reprInst ← synthInstance (mkApp (mkConst ``Repr [u]) α)
    return ⟨u, α, reprInst, e⟩
  | _ =>
    let v ← mkFreshLevelMVar
    let sampleableExtInst ← synthInstance (mkApp (mkConst ``SampleableExt [u, v]) e)
    let v ← instantiateLevelMVars v
    let reprInst := mkApp2 (mkConst ``SampleableExt.proxyRepr [u, v]) e sampleableExtInst
    let gen := mkApp2 (mkConst ``SampleableExt.sample [u, v]) e sampleableExtInst
    let typ := mkApp2 (mkConst ``SampleableExt.proxy [u, v]) e sampleableExtInst
    return ⟨v, typ, reprInst, gen⟩

/--
`#sample type`, where `type` has an instance of `SampleableExt`, prints ten random
values of type `type` using an increasing size parameter.

```lean
#sample Nat
-- prints
-- 0
-- 0
-- 2
-- 24
-- 64
-- 76
-- 5
-- 132
-- 8
-- 449
-- or some other sequence of numbers

#sample List Int
-- prints
-- []
-- [1, 1]
-- [-7, 9, -6]
-- [36]
-- [-500, 105, 260]
-- [-290]
-- [17, 156]
-- [-2364, -7599, 661, -2411, -3576, 5517, -3823, -968]
-- [-643]
-- [11892, 16329, -15095, -15461]
-- or whatever
```
-/
elab "#sample " e:term : command =>
  Command.runTermElabM fun _ => do
    let e ← Elab.Term.elabTermAndSynthesize e none
    let ⟨u, α, repr, gen⟩ ← mkGenerator e
    let printSamples := mkApp3 (mkConst ``printSamples [u]) α repr gen
    let code ← unsafe evalExpr (IO PUnit) (mkApp (mkConst ``IO) (mkConst ``PUnit [1])) printSamples
    _ ← code

end Plausible
