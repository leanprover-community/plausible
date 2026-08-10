import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Attr

open Plausible

/-- A variant of a binary tree datatype where the
    non-recursive `Leaf` constructor is missing.

    We are unable to derive a generator for this type,
    since it is impossible to construct an inhabitant of this type.

    The test below checks that an appropriate error message is emitted
    by the deriving handler. -/
inductive TreeNoLeaf where
  | Node : Nat → TreeNoLeaf → TreeNoLeaf → TreeNoLeaf

set_option trace.plausible.deriving.arbitrary true in
/-- error: derive Arbitrary failed, TreeNoLeaf has no non-recursive constructors -/
#guard_msgs in
deriving instance Arbitrary for TreeNoLeaf
