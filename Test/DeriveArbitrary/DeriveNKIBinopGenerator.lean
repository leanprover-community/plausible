import Plausible.Gen
import Plausible.New.Arbitrary
import Plausible.New.GeneratorCombinators
import Plausible.New.DeriveArbitrary

open Arbitrary GeneratorCombinators

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
info: Try this generator: instance : ArbitrarySized BinOp where
  arbitrarySized :=
    let rec aux_arb (size : Nat) : Plausible.Gen BinOp :=
      match size with
      | Nat.zero =>
        GeneratorCombinators.oneOfWithDefault (pure BinOp.land)
          [GeneratorCombinators.thunkGen (fun _ => pure BinOp.land),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.lor),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.eq),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.ne),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.lt),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.le),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.gt),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.ge),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.add),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.sub),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.mul),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.div),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.mod),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.pow),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.floor),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.lshift),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.rshift),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.or),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.xor),
            GeneratorCombinators.thunkGen (fun _ => pure BinOp.and)]
      | Nat.succ size' =>
        GeneratorCombinators.frequency (pure BinOp.land)
          [(1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.land)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.lor)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.eq)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.ne)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.lt)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.le)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.gt)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.ge)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.add)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.sub)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.mul)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.div)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.mod)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.pow)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.floor)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.lshift)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.rshift)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.or)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.xor)),
            (1, GeneratorCombinators.thunkGen (fun _ => pure BinOp.and)), ]
    fun size => aux_arb size
-/
#guard_msgs(info, drop warning) in
#derive_arbitrary BinOp

end CommandElaboratorTest
