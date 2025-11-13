import Plausible.Gen
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
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
| c : Diag α a (a, a)

/--  error: Application type mismatch: The argument
  a_1
 has type
   α
but is expected to have type
  α_1
   in the application
   Diag α_1 a_1
 ---
 error: unknown universe level `u`
 ---
 error: Redundant alternative: Any expression matching
   _
 will match one of the preceding alternatives
 ---
 error: Redundant alternative: Any expression matching
   _
 will match one of the preceding alternatives
 ---
 error: (kernel) declaration has metavariables 'inst.aux_arb✝'-/
#guard_msgs(error, drop info, whitespace := lax) in
derive_generator fun α b => ∃ a, Diag α a b


inductive usesVec : _ → Prop where
| c {a b : Nat} : usesVec #v[a,b,a]

#guard_msgs(drop error, drop info, whitespace := lax) in
derive_generator ∃ a, usesVec a
