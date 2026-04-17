import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Attr

open Plausible

set_option guard_msgs.diff true

/-! ## Structure parameter with Type-valued fields -/

structure Params where
  Meta : Type
  IDMeta : Type

inductive Bar (T : Params) where
  | mk : T.Meta → T.IDMeta → Bar T

instance [Repr T.Meta] [Repr T.IDMeta] : Repr (Bar T) where
  reprPrec b _ := match b with
    | .mk m i => f!"Bar.mk {repr m} {repr i}"

deriving instance Arbitrary for Bar

#guard_msgs(drop info, drop warning) in
#synth Arbitrary (Bar ⟨Bool, Nat⟩)

#guard_msgs(drop info, drop warning) in
#eval Arbitrary.runArbitrary (α := Bar ⟨Bool, Nat⟩) 5

/-! ## Mixed: normal type parameter + structure parameter -/

structure Config where
  Tag : Type

inductive Mixed (α : Type) (C : Config) where
  | leaf : α → Mixed α C
  | tagged : C.Tag → α → Mixed α C

instance [Repr α] [Repr C.Tag] : Repr (Mixed α C) where
  reprPrec m _ := match m with
    | .leaf a => f!"Mixed.leaf {repr a}"
    | .tagged t a => f!"Mixed.tagged {repr t} {repr a}"

deriving instance Arbitrary for Mixed

#guard_msgs(drop info, drop warning) in
#synth Arbitrary (Mixed Nat ⟨Bool⟩)

#guard_msgs(drop info, drop warning) in
#eval Arbitrary.runArbitrary (α := Mixed Nat ⟨Bool⟩) 5

/-! ## Nested structure parameter -/

structure Inner where
  Meta : Type
  IDMeta : Type

structure Outer where
  base : Inner
  Extra : Type

inductive Nested (T : Outer) where
  | mk : T.base.Meta → T.base.IDMeta → T.Extra → Nested T

instance [Repr T.base.Meta] [Repr T.base.IDMeta] [Repr T.Extra] : Repr (Nested T) where
  reprPrec n _ := match n with
    | .mk m i e => f!"Nested.mk {repr m} {repr i} {repr e}"

deriving instance Arbitrary for Nested

#guard_msgs(drop info, drop warning) in
#synth Arbitrary (Nested ⟨⟨Bool, Nat⟩, String⟩)

#guard_msgs(drop info, drop warning) in
#eval Arbitrary.runArbitrary (α := Nested ⟨⟨Bool, Nat⟩, String⟩) 5

/-! ## Rejection of structures with non-Type fields -/

structure BadParams where
  n : Nat
  Meta : Type

inductive Baz (T : BadParams) where
  | mk : T.Meta → BitVec T.n → Baz T

/--
error: Cannot derive Plausible.Arbitrary for 'Baz': structure parameter 'T✝' has a field of type 'Nat', which is not a Type or structure of Types. This makes the type effectively indexed.
-/
#guard_msgs(error) in
deriving instance Arbitrary for Baz
