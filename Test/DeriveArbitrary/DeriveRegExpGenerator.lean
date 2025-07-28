import Plausible.Gen
import Plausible.Arbitrary
import Plausible.Gen
import Plausible.DeriveArbitrary

open Plausible Gen

set_option guard_msgs.diff true

/-- An inductive datatype representing regular expressions (where "characters" are `Nat`s).
   Slightly modified from Software Foundations
   See https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html
   and search for "Case Study: Regular Expressions".
   The `RegExp`s below are non-polymorphic in the character type. -/
inductive RegExp : Type where
  | EmptySet : RegExp
  | EmptyStr : RegExp
  | Char : Nat → RegExp -- using Nat instead of Char
  | App : RegExp → RegExp → RegExp
  | Union : RegExp → RegExp → RegExp
  | Star : RegExp → RegExp
  deriving Repr, Arbitrary

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instArbitrarySizedRegExp -/
#guard_msgs in
#synth ArbitrarySized RegExp

/-- info: instArbitraryOfArbitrarySized -/
#guard_msgs in
#synth Arbitrary RegExp

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this generator: instance : Plausible.ArbitrarySized RegExp where
  arbitrarySized :=
    let rec aux_arb (size : Nat) : Plausible.Gen RegExp :=
      match size with
      | Nat.zero =>
        Plausible.Gen.oneOfWithDefault (pure RegExp.EmptySet)
          [Plausible.Gen.thunkGen (fun _ => pure RegExp.EmptySet),
            Plausible.Gen.thunkGen (fun _ => pure RegExp.EmptyStr),
            Plausible.Gen.thunkGen
              (fun _ => do
                let a_0 ← Plausible.Arbitrary.arbitrary
                return RegExp.Char a_0)]
      | Nat.succ size' =>
        Plausible.Gen.frequency (pure RegExp.EmptySet)
          [(1, Plausible.Gen.thunkGen (fun _ => pure RegExp.EmptySet)),
            (1, Plausible.Gen.thunkGen (fun _ => pure RegExp.EmptyStr)),
            (1,
              Plausible.Gen.thunkGen
                (fun _ => do
                  let a_0 ← Plausible.Arbitrary.arbitrary
                  return RegExp.Char a_0)),
            (Nat.succ size',
              Plausible.Gen.thunkGen
                (fun _ => do
                  let a_0 ← aux_arb size'
                  let a_1 ← aux_arb size'
                  return RegExp.App a_0 a_1)),
            (Nat.succ size',
              Plausible.Gen.thunkGen
                (fun _ => do
                  let a_0 ← aux_arb size'
                  let a_1 ← aux_arb size'
                  return RegExp.Union a_0 a_1)),
            (Nat.succ size',
              Plausible.Gen.thunkGen
                (fun _ => do
                  let a_0 ← aux_arb size'
                  return RegExp.Star a_0))]
    fun size => aux_arb size
-/
#guard_msgs(info, drop warning) in
#derive_arbitrary RegExp

end CommandElaboratorTest
