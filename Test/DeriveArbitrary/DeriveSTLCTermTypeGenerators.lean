import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Attr
import Plausible.Testable
import Test.CommonDefinitions.STLCDefinitions

open Plausible Gen

set_option guard_msgs.diff true

-- Invoke deriving instance handler for the `Arbitrary` typeclass on `type` and `term`
#guard_msgs(drop info, drop warning) in
deriving instance Arbitrary for type, term

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitraryFueled`
-- for both `type` & `term`

#guard_msgs(drop info, drop warning) in
#synth ArbitraryFueled type

#guard_msgs(drop info, drop warning) in
#synth ArbitraryFueled term

#guard_msgs(drop info, drop warning) in
#synth Arbitrary type

#guard_msgs(drop info, drop warning) in
#synth Arbitrary term


/-!
Test that we can use the derived generator to find counterexamples.

We construct two faulty properties:
1. `∀ (term : term), isValue term = true`
2. `∀ (ty : type), isFunctionType ty = true`

Both of these properties are false, since there exist terms in the STLC
which are not values (e.g. function applications), and there are
types which are not function types (e.g. `Nat`).

We then test that the respective derived generators for `term`s and `type`s
generate counterexamples which refute the aforementioned properties.
-/

/-- Determines whether a `term` is a value.
    (Note that only constant `Nat`s and lambda abstractions are considered values in the STLC.) -/
def isValue (tm : term) : Bool :=
  match tm with
  | .Const _ | .Abs _ _ => true
  | _ => false

/-- Determines whether a `type` is a function type -/
def isFunctionType (ty : type) : Bool :=
  match ty with
  | .Nat => false
  | .Fun _ _ => true

/-- `Shrinkable` instance for `type` -/
instance : Shrinkable type where
  shrink (ty : type) :=
    match ty with
    | .Nat => []
    | .Fun t1 t2 => [.Nat, t1, t2]

/-- `Shrinkable` instance for `term` -/
instance : Shrinkable term where
  shrink := shrinkTerm
    where
      shrinkTerm (tm : term) : List term :=
        match tm with
        | .Const _ | .Var _ => []
        | .App e1 e2 | .Add e1 e2 => shrinkTerm e1 ++ shrinkTerm e2
        | .Abs _ e => shrinkTerm e

/-- `SampleableExt` instance for `type` -/
instance : SampleableExt type :=
  SampleableExt.mkSelfContained Arbitrary.arbitrary

/-- `SampleableExt` instance for `term` -/
instance : SampleableExt term :=
   SampleableExt.mkSelfContained Arbitrary.arbitrary

/-- error: Found a counter-example! -/
#guard_msgs in
#eval Testable.check (∀ (term : term), isValue term)
  (cfg := {numInst := 10, maxSize := 5, quiet := true})

/-- error: Found a counter-example! -/
#guard_msgs in
#eval Testable.check (∀ (ty : type), isFunctionType ty)
  (cfg := {numInst := 10, maxSize := 5, quiet := true})
