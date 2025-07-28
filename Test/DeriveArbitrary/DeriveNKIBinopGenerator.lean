import Plausible.Gen
import Plausible.Arbitrary
import Plausible.Gen
import Plausible.DeriveArbitrary

open Plausible Gen

set_option guard_msgs.diff true

inductive BinOp where
  -- logical
  | land | lor
  -- comparison
  | eq | ne | lt | le | gt | ge
  -- arithmetic
  | add | sub | mul | div | mod | pow | floor
  -- bitwise
  | lshift | rshift | or | xor | and
  deriving Repr, Arbitrary

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

/-- info: instArbitrarySizedBinOp -/
#guard_msgs in
#synth ArbitrarySized BinOp

/-- info: instArbitraryOfArbitrarySized -/
#guard_msgs in
#synth Arbitrary BinOp

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

/--
info: Try this generator: instance : Plausible.ArbitrarySized BinOp where
  arbitrarySized :=
    let rec aux_arb (size : Nat) : Plausible.Gen BinOp :=
      match size with
      | Nat.zero =>
        Plausible.Gen.oneOfWithDefault (pure BinOp.land)
          [Plausible.Gen.thunkGen (fun _ => pure BinOp.land), Plausible.Gen.thunkGen (fun _ => pure BinOp.lor),
            Plausible.Gen.thunkGen (fun _ => pure BinOp.eq), Plausible.Gen.thunkGen (fun _ => pure BinOp.ne),
            Plausible.Gen.thunkGen (fun _ => pure BinOp.lt), Plausible.Gen.thunkGen (fun _ => pure BinOp.le),
            Plausible.Gen.thunkGen (fun _ => pure BinOp.gt), Plausible.Gen.thunkGen (fun _ => pure BinOp.ge),
            Plausible.Gen.thunkGen (fun _ => pure BinOp.add), Plausible.Gen.thunkGen (fun _ => pure BinOp.sub),
            Plausible.Gen.thunkGen (fun _ => pure BinOp.mul), Plausible.Gen.thunkGen (fun _ => pure BinOp.div),
            Plausible.Gen.thunkGen (fun _ => pure BinOp.mod), Plausible.Gen.thunkGen (fun _ => pure BinOp.pow),
            Plausible.Gen.thunkGen (fun _ => pure BinOp.floor), Plausible.Gen.thunkGen (fun _ => pure BinOp.lshift),
            Plausible.Gen.thunkGen (fun _ => pure BinOp.rshift), Plausible.Gen.thunkGen (fun _ => pure BinOp.or),
            Plausible.Gen.thunkGen (fun _ => pure BinOp.xor), Plausible.Gen.thunkGen (fun _ => pure BinOp.and)]
      | Nat.succ size' =>
        Plausible.Gen.frequency (pure BinOp.land)
          [(1, Plausible.Gen.thunkGen (fun _ => pure BinOp.land)),
            (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.lor)), (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.eq)),
            (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.ne)), (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.lt)),
            (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.le)), (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.gt)),
            (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.ge)), (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.add)),
            (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.sub)),
            (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.mul)),
            (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.div)),
            (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.mod)),
            (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.pow)),
            (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.floor)),
            (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.lshift)),
            (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.rshift)),
            (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.or)), (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.xor)),
            (1, Plausible.Gen.thunkGen (fun _ => pure BinOp.and)), ]
    fun size => aux_arb size
-/
#guard_msgs(info, drop warning) in
#derive_arbitrary BinOp

end CommandElaboratorTest
