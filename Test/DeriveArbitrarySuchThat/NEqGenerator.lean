import Plausible.Gen
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Test.CommonDefinitions.BinaryTree
import Plausible.Attr

open Plausible
open ArbitrarySizedSuchThat

set_option guard_msgs.diff true

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
