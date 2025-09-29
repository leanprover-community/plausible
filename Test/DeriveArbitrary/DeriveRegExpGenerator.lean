import Plausible.Attr
import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Testable

open Plausible Gen

set_option guard_msgs.diff true

/-- An inductive datatype representing regular expressions (where "characters" are `Nat`s).
   Adapted from the Inductive Propositions chapter of Software Foundations, volume 1:
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
  deriving Repr, BEq

#guard_msgs(drop info, drop warning) in
deriving instance Arbitrary for RegExp

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitraryFueled`

#guard_msgs(drop info, drop warning) in
#synth ArbitraryFueled RegExp

#guard_msgs(drop info, drop warning) in
#synth Arbitrary RegExp

/-!
Test that we can use the derived generator to find counterexamples.

We construct a faulty property, which (erroneously) states that
all regular expressions never accept any string. (Example taken from
UPenn CIS 5520 https://www.seas.upenn.edu/~cis5520/current/hw/hw04/RegExp.html)

```lean
∀ r : RegExp, neverMatchesAnyString r == True
```

(This property is faulty, since there exist regular expressions, e.g. `EmptyString`
which do match some string!)

We then test that the derived generator for `Tree`s succesfully
generates a counterexample (e.g. `EmptyString`) which refutes the property.
-/

/-- Determines whether a regular expression *never* matches any string -/
def neverMatchesAnyString (r : RegExp) : Bool :=
  match r with
  | .EmptySet => true
  | .EmptyStr | .Char _ | .Star _ => false       -- Note that `Star` can always match the empty string
  | .App r1 r2 => neverMatchesAnyString r1 || neverMatchesAnyString r2
  | .Union r1 r2 => neverMatchesAnyString r1 && neverMatchesAnyString r2

/-- A shrinker for regular expressions -/
def shrinkRegExp (r : RegExp) : List RegExp :=
  match r with
  | .EmptySet | .EmptyStr => []
  | .Char _ => [.EmptyStr]
  | .Star r' => .Star <$> shrinkRegExp r'
  | .App r1 r2 | .Union r1 r2 => shrinkRegExp r1 ++ shrinkRegExp r2

/-- `Shrinkable` instance for `RegExp` -/
instance : Shrinkable RegExp where
  shrink := shrinkRegExp

/-- `SampleableExt` instance for `RegExp` -/
instance : SampleableExt RegExp :=
  SampleableExt.mkSelfContained Arbitrary.arbitrary

/-- error: Found a counter-example! -/
#guard_msgs in
#eval Testable.check (∀ r : RegExp, neverMatchesAnyString r == True)
  (cfg := {numInst := 10, maxSize := 5, quiet := true})
