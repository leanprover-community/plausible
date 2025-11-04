import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Attr

set_option guard_msgs.diff true


inductive HasDep {α : Type} (_ : List α) : Nat → Prop where
| foo (a b : α) : a = b → HasDep _ 0

/--
error: unable to find unknown x._@.Test.DeriveArbitrarySuchThat.DependentArgs.1339814650._hygCtx._hyg.3 in UnknownMap [(n_1,
  Undef Nat),
 (α_1, Fixed),
 (l_1, Fixed),
 (a, Undef α),
 (u_2, Unknown n_1),
 (b, Undef α),
 (u_1, Unknown l_1),
 (α, Unknown u_0),
 (u_0, Unknown α_1)]
-/
#guard_msgs(error) in
derive_generator (fun α l => ∃ n, @HasDep α l n)

inductive HasClassDep {α : Type} [h : DecidableEq α] : Nat → Prop where
| foo (a b : α) : a = b → HasClassDep 0

/--
error: exprToHypothesisExpr: unable to convert α to a HypothesisExpr, must be a constructor or an inductive applied to arguments.
-/
#guard_msgs(error) in
derive_generator (fun α inst => ∃ n, @HasClassDep α inst n)


def f : Nat → Nat := fun _ => 0

inductive HasCall : Nat → Prop where
| foo (n : Nat) : f n = 0 → HasCall n

/--
error: failed to synthesize
  ArbitrarySizedSuchThat (?m.64 size') fun vn => vn = OfNat.ofNat 0
(deterministic) timeout at `typeclass`, maximum number of heartbeats (20000) has been reached
Note: Use `set_option synthInstance.maxHeartbeats <num>` to set the limit.
Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
error: Invalid pattern: Expected a constructor or constant marked with `[match_pattern]`
Hint: `Lean.Lsp.RefIdent.RefIdentJsonRepr.f` is similar
---
error: Invalid pattern: Expected a constructor or constant marked with `[match_pattern]`
Hint: `Lean.Lsp.RefIdent.RefIdentJsonRepr.f` is similar
-/
#guard_msgs(error, whitespace:=lax, drop info) in
derive_generator ∃ n, HasCall n
