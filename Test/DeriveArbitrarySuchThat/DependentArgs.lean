/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveChecker
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
 (unk_0, Undef Nat),
 (u_0, Unknown α_1)]
-/
#guard_msgs(error, ordering:=sorted) in
derive_generator (fun α l => ∃ n, @HasDep α l n)

inductive HasClassDep {α : Type} [h : DecidableEq α] : Nat → Prop where
| foo (a b : α) : a = b → HasClassDep 0

#guard_msgs(drop info, error) in
derive_generator (fun α inst => ∃ n, @HasClassDep α inst n)

#guard_msgs(error, drop warning, drop info) in
derive_checker fun α inst n => @HasClassDep α inst n

#guard_msgs(drop info, error) in
derive_enumerator (fun α inst => ∃ n, @HasClassDep α inst n)

def f : Nat → Nat := fun _ => 0

inductive HasCall : Nat → Prop where
| foo (n : Nat) : f n = 0 → HasCall n

#guard_msgs(error, whitespace:=lax, drop info) in
derive_generator ∃ n, HasCall n

#guard_msgs(error, whitespace:=lax, drop info) in
derive_enumerator ∃ n, HasCall n
