
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveConstrainedProducer
import Test.DeriveArbitrarySuchThat.SimultaneousMatchingTests

open DecOpt

set_option guard_msgs.diff true

/-- `LessThanEq n m` is an inductive relation that means `n <= m`.
    Adapted from https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html -/
inductive LessThanEq : Nat → Nat → Prop where
  | Refl : ∀ n, LessThanEq n n
  | Succ : ∀ n m, LessThanEq n m → LessThanEq n (.succ m)

/-- `NatChain a b` means there is an ascending chain of `Nat`s under the usual `<=` order,
    where `a` and `b` are the start and end of the chain respectively.
    This is an inductive relation with multiple existentially quantified variables
    (note how `x` and `y` don't appear in the conclusion of the `ChainExists` constructor).

    We use `LessThanEq` (defined above) instead of the `LE.le` operator from the Lean standard library,
    since `LE` is defined as a typeclass and not as an inductive relation. -/
inductive NatChain (a b : Nat) : Prop where
| ChainExists : ∀ (x y : Nat),
    (LessThanEq a x) →
    (LessThanEq x y) ->
    (LessThanEq y b) →
    NatChain a b

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun x => ∃ (a : Nat), LessThanEq a x)

#guard_msgs(drop info, drop warning) in
derive_enumerator (fun x => ∃ (y : Nat), LessThanEq x y)

#guard_msgs(drop info, drop warning) in
derive_checker (fun n m => LessThanEq n m)

#guard_msgs(drop info, drop warning) in
derive_checker (fun a b => NatChain a b)
