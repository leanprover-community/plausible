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

/--error: failed to synthesize
  DecOpt (ConstTrue (a_1 = b))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
error: failed to synthesize
  DecOpt (ConstTrue (a_1 = b))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
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
