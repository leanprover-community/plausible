/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
import Plausible.Gen
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.DeriveChecker
import Test.CommonDefinitions.BinaryTree
import Plausible.Attr

open Plausible
open ArbitrarySizedSuchThat

def ConstTrue (_ : Prop) := True

inductive usesNeq : Nat → Prop where
| c : a ≠ b → usesNeq a

#guard_msgs(drop info) in
derive_generator ∃ a, usesNeq a

inductive usesConstTrue : Nat → Prop where
| c : ConstTrue (a = b) → usesConstTrue a

/--error: failed to synthesize instance of type class
  DecOpt (ConstTrue (a_1 = b))

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: failed to synthesize instance of type class
  DecOpt (ConstTrue (a_1 = b))

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs(error, drop info, whitespace := lax) in
derive_generator ∃ a, usesConstTrue a


inductive usesNeq' : Nat × Nat → Prop where
| c : a ≠ b → usesNeq' (a, b)

#guard_msgs(error, drop info, whitespace := lax) in
derive_generator ∃ a, usesNeq' a

inductive Diag : (α : Type u) → α → α × α → Prop where
| c : Diag α a (b, b)

-- set_option trace.plausible.deriving.arbitrary true

/--
error: Redundant alternative: Any expression matching
  _
will match one of the preceding alternatives
---
error: Redundant alternative: Any expression matching
  _
will match one of the preceding alternatives-/
#guard_msgs(error, drop info, whitespace := lax) in
derive_generator fun γ p => ∃ g, Diag γ g p

/-- error: Redundant alternative: Any expression matching
  _
will match one of the preceding alternatives

---

error: Redundant alternative: Any expression matching
  _
will match one of the preceding alternatives -/
#guard_msgs(error, drop info, whitespace := lax) in
derive_checker fun γ g p => Diag γ g p

inductive usesVec : _ → Prop where
| c {a b : Nat} : usesVec #v[a,b,a]

#guard_msgs(drop error, drop info, whitespace := lax) in
derive_generator ∃ a, usesVec a

inductive TypeChange : Type u → Nat → Prop where
| ennd : TypeChange (((α × α) × (α × α)) × (((α × α) × (α × α)))) 3
| change : TypeChange (α × α) (n + 1) → TypeChange α n

example : TypeChange (Nat × Nat) 1 := .ennd |>.change.change

example : TypeChange Nat 0 := .ennd |>.change.change.change

#guard_msgs(drop error, drop info) in
derive_generator fun α => ∃ n, TypeChange α n

abbrev Map α β := List (α × β)
abbrev Maps α β := List (Map α β)

inductive MapFind₂ {α β : Type} : Map α β → α × β → Prop where
| hd : MapFind₂ ((x, y) :: m) (x, y)
| tl : MapFind₂ m (x, y) → MapFind₂ (p :: m) (x, y)

inductive MapsFind₂ : Maps α β → α × β → Prop where
| hd : MapFind₂ m (x, y) → MapsFind₂ (m :: ms) (x, y)
| tl : MapsFind₂ ms (x, y) → MapsFind₂ (m :: ms) (x, y)

/--error: Redundant alternative: Any expression matching
  _
will match one of the preceding alternatives-/
#guard_msgs(error, drop info) in
derive_generator fun α β m => ∃ pa, @MapFind₂ α β m pa

/--error: Redundant alternative: Any expression matching
  _
will match one of the preceding alternatives
---
error: Redundant alternative: Any expression matching
  _
will match one of the preceding alternatives
---
error: Redundant alternative: Any expression matching
  _
will match one of the preceding alternatives-/
#guard_msgs(error, drop info) in
derive_generator fun α β m => ∃ pa, @MapsFind₂ α β m pa

-- Simple polymorphic list membership
inductive Contains {α : Type} : List α → α → Prop where
| head : Contains (x :: xs) x
| tail : Contains xs x → Contains (y :: xs) x

#guard_msgs(drop info) in
derive_generator fun α xs => ∃ x, @Contains α xs x

-- Polymorphic option wrapping
inductive IsWrapped {α : Type} : α → Option α → Prop where
| some : IsWrapped x (some x)

#guard_msgs(drop info) in
derive_generator fun α x => ∃ opt, @IsWrapped α x opt

-- Simple type equality
inductive SameType {α : Type} : α → α → Prop where
| refl : SameType (x : α) (x : α)

#guard_msgs(drop info) in
derive_generator fun α x => ∃ y, @SameType α x y
#guard_msgs(drop info) in
derive_checker fun α x y => @SameType α x y

-- Polymorphic pair components
inductive FirstOf {α β : Type} : α × β → α → Prop where
| mk : FirstOf (x, y) x

/--error: Redundant alternative: Any expression matching
  _
will match one of the preceding alternatives
---
error: Redundant alternative: Any expression matching
  _
will match one of the preceding alternatives-/
#guard_msgs(error, drop info) in
derive_generator fun α β p => ∃ x, @FirstOf α β p x
#guard_msgs(drop info) in
derive_generator fun α β x => ∃ p, @FirstOf α β p x

-- List length relation
inductive HasLen {α : Type} : List α → Nat → Prop where
| nil : HasLen [] 0
| cons : HasLen xs n → HasLen (x :: xs) (n + 1)

#guard_msgs(drop info) in
derive_generator fun α xs => ∃ n, @HasLen α xs n

/--info: 3-/
#guard_msgs() in
#eval Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun n => @HasLen Nat [1,2,3] n) 100) 0

-- Complex list relation: Interleaving with type constraints
inductive Interleaves {α β : Type} : List α → List β → List (α ⊕ β) → Prop where
| nil_nil : Interleaves [] [] []
| left_cons : Interleaves xs ys zs → Interleaves (x :: xs) ys (Sum.inl x :: zs)
| right_cons : Interleaves xs ys zs → Interleaves xs (y :: ys) (Sum.inr y :: zs)

#guard_msgs(drop info) in
derive_generator fun α β xs ys => ∃ zs, @Interleaves α β xs ys zs

-- Relation with negated hypothesis containing type variable
inductive NotContains {α : Type} : List α → α → Prop where
| empty : NotContains [] x
| cons : x ≠ y → NotContains xs x → NotContains (y :: xs) x

#guard_msgs(drop info) in
derive_generator fun α xs => ∃ x, @NotContains α xs x
