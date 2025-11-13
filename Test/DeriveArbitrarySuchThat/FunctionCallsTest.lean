import Plausible.Arbitrary
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Test.CommonDefinitions.FunctionCallInConclusion
import Plausible.Attr

open Plausible
open DecOpt

set_option guard_msgs.diff true

inductive square_of' : Nat → _ → Prop where
  | sq : forall x, square_of' x (x * x)

inductive square_of'' : Nat → _ → Prop where
  | sq : forall x, square_of'' x (x, x)

inductive square_of''' : Nat → _ → Prop where
  | sq : forall x, square_of''' x (fun (_ : Unit) => x)

/--error: Redundant alternative: Any expression matching
  _
will match one of the preceding alternatives
---
error: Redundant alternative: Any expression matching
  _
will match one of the preceding alternatives
-/
#guard_msgs(error, drop info) in
derive_generator (fun n => ∃ (m : Nat), square_of'' m n)

#guard_msgs(drop info, drop warning) in
derive_generator (fun n => ∃ (m : Nat), square_of' m n)

/--error: exprToConstructorExpr can only handle free variables, constants, and applications. Attempted to convert: Unit → Nat-/
#guard_msgs(error, drop warning) in
derive_generator (fun n => ∃ (m : Nat), square_of''' m n)

example : Function.Injective (fun a => a * 1) := fun _ _ h => by exact Nat.add_left_cancel h
