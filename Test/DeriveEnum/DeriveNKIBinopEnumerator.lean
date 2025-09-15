import Plausible.Arbitrary
import Plausible.Chamelean.DeriveEnum
import Plausible.Chamelean.EnumeratorCombinators
import Test.DeriveArbitrary.DeriveNKIBinopGenerator

set_option guard_msgs.diff true

deriving instance Enum for BinOp

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instEnumSizedBinOp -/
#guard_msgs in
#synth EnumSized BinOp

/-- info: instEnumOfEnumSized -/
#guard_msgs in
#synth Enum BinOp

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this enumerator: instance : EnumSized BinOp where
  enumSized :=
    let rec aux_enum (size : Nat) : Enumerator BinOp :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.oneOfWithDefault (pure BinOp.land)
          [pure BinOp.land, pure BinOp.lor, pure BinOp.eq, pure BinOp.ne, pure BinOp.lt, pure BinOp.le, pure BinOp.gt,
            pure BinOp.ge, pure BinOp.add, pure BinOp.sub, pure BinOp.mul, pure BinOp.div, pure BinOp.mod,
            pure BinOp.pow, pure BinOp.floor, pure BinOp.lshift, pure BinOp.rshift, pure BinOp.or, pure BinOp.xor,
            pure BinOp.and]
      | Nat.succ size' =>
        EnumeratorCombinators.oneOfWithDefault (pure BinOp.land)
          [pure BinOp.land, pure BinOp.lor, pure BinOp.eq, pure BinOp.ne, pure BinOp.lt, pure BinOp.le, pure BinOp.gt,
            pure BinOp.ge, pure BinOp.add, pure BinOp.sub, pure BinOp.mul, pure BinOp.div, pure BinOp.mod,
            pure BinOp.pow, pure BinOp.floor, pure BinOp.lshift, pure BinOp.rshift, pure BinOp.or, pure BinOp.xor,
            pure BinOp.and, ]
    fun size => aux_enum size
-/
#guard_msgs(info, drop warning) in
#derive_enum BinOp

end CommandElaboratorTest
