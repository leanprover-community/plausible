import Plausible.Attr
import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Testable

open Plausible Gen

set_option guard_msgs.diff true

/-- Binary operators for the NKI language,
    adapted from https://github.com/leanprover/KLR/blob/main/KLR/NKI/Basic.lean -/
inductive BinOp where
  -- logical
  | land | lor
  -- comparison
  | eq | ne | lt | le | gt | ge
  -- arithmetic
  | add | sub | mul | div | mod | pow | floor
  -- bitwise
  | lshift | rshift | or | xor | and
  deriving Repr

#guard_msgs(drop info, drop warning) in
deriving instance Arbitrary for BinOp

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitraryFueled`

#guard_msgs(drop info, drop warning) in
#synth ArbitraryFueled BinOp

#guard_msgs(drop info, drop warning) in
#synth Arbitrary BinOp

/-- Trivial `Shrinkable` instance for `BinOp`s -/
instance : Shrinkable BinOp where
  shrink := fun _ => []

/-- `SampleableExt` instance for `BinOp` -/
instance : SampleableExt BinOp :=
  SampleableExt.mkSelfContained Arbitrary.arbitrary

-- To test whether the derived generator can generate counterexamples,
-- we state an (erroneous) property that states that all binary operators
-- are logical operators, and see if the generator can refute this property.

/-- Determines whether a `BinOp` is a logical operation -/
def isLogicalOp (op : BinOp) : Bool :=
  match op with
  | .land | .lor => true
  | _ => false

/-- error: Found a counter-example! -/
#guard_msgs in
#eval Testable.check (∀ op : BinOp, isLogicalOp op)
  (cfg := {numInst := 10, maxSize := 5, quiet := true})
