/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
module

namespace Plausible

universe u v
variable {α β : Type _}

/-- Given an example `x : α`, `Shrinkable α` gives us a way to shrink it
and suggest simpler examples. -/
public class Shrinkable (α : Type u) where
  shrink : (x : α) → List α := fun _ => []

section Shrinkers

public instance [Shrinkable α] [Shrinkable β] : Shrinkable (Sum α β) where
  shrink s :=
    match s with
    | .inl l => Shrinkable.shrink l |>.map .inl
    | .inr r => Shrinkable.shrink r |>.map .inr

public instance Unit.shrinkable : Shrinkable Unit where
  shrink _ := []

/-- `Nat.shrink' n` creates a list of smaller natural numbers by
successively dividing `n` by 2 . For example, `Nat.shrink 5 = [2, 1, 0]`. -/
public def Nat.shrink (n : Nat) : List Nat :=
  if 0 < n then
    let m := n/2
    m :: shrink m
  else
    []

public instance Nat.shrinkable : Shrinkable Nat where
  shrink := Nat.shrink

public instance Fin.shrinkable {n : Nat} : Shrinkable (Fin n.succ) where
  shrink m := Nat.shrink m |>.map (Fin.ofNat _)

public instance BitVec.shrinkable {n : Nat} : Shrinkable (BitVec n) where
  shrink m := Nat.shrink m.toNat |>.map (BitVec.ofNat n)

public instance UInt8.shrinkable : Shrinkable UInt8 where
  shrink m := Nat.shrink m.toNat |>.map UInt8.ofNat

public instance UInt16.shrinkable : Shrinkable UInt16 where
  shrink m := Nat.shrink m.toNat |>.map UInt16.ofNat

public instance UInt32.shrinkable : Shrinkable UInt32 where
  shrink m := Nat.shrink m.toNat |>.map UInt32.ofNat

public instance UInt64.shrinkable : Shrinkable UInt64 where
  shrink m := Nat.shrink m.toNat |>.map UInt64.ofNat

public instance USize.shrinkable : Shrinkable USize where
  shrink m := Nat.shrink m.toNat |>.map USize.ofNat

/-- `Int.shrinkable` operates like `Nat.shrinkable` but also includes the negative variants. -/
public instance Int.shrinkable : Shrinkable Int where
  shrink n :=
    let converter n :=
      let int := Int.ofNat n
      [int, -int]
    Nat.shrink n.natAbs |>.flatMap converter

public instance Bool.shrinkable : Shrinkable Bool := {}
public instance Char.shrinkable : Shrinkable Char := {}

public instance Option.shrinkable [Shrinkable α] : Shrinkable (Option α) where
  shrink o :=
    match o with
    | some x => Shrinkable.shrink x |>.map .some
    | none => []

public instance Prod.shrinkable [shrA : Shrinkable α] [shrB : Shrinkable β] :
    Shrinkable (Prod α β) where
  shrink := fun (fst,snd) =>
    let shrink1 := shrA.shrink fst |>.map fun x => (x, snd)
    let shrink2 := shrB.shrink snd |>.map fun x => (fst, x)
    shrink1 ++ shrink2

public instance Sigma.shrinkable [shrA : Shrinkable α] [shrB : Shrinkable β] :
    Shrinkable ((_ : α) × β) where
  shrink := fun ⟨fst,snd⟩ =>
    let shrink1 := shrA.shrink fst |>.map fun x => ⟨x, snd⟩
    let shrink2 := shrB.shrink snd |>.map fun x => ⟨fst, x⟩
    shrink1 ++ shrink2

open Shrinkable

/-- Shrink a list of a shrinkable type, either by discarding an element or shrinking an element. -/
public instance List.shrinkable [Shrinkable α] : Shrinkable (List α) where
  shrink := fun L =>
    (L.mapIdx fun i _ => L.eraseIdx i) ++
    (L.mapIdx fun i a => (shrink a).map fun a' => L.modify i fun _ => a').flatten

public instance ULift.shrinkable [Shrinkable α] : Shrinkable (ULift α) where
  shrink u := (shrink u.down).map ULift.up

public instance String.shrinkable : Shrinkable String where
  shrink s := (shrink s.toList).map String.ofList

public instance Array.shrinkable [Shrinkable α] : Shrinkable (Array α) where
  shrink xs := (shrink xs.toList).map Array.mk

public instance Subtype.shrinkable {α : Type u} {β : α → Prop} [Shrinkable α] [∀ x, Decidable (β x)] : Shrinkable {x : α // β x} where
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

end Plausible
