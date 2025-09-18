import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Test.DeriveEnumSuchThat.DeriveBSTEnumerator

-- See `Test/DeriveArbitrarySuchThat/NonLinearPatternsTest.lean` for the definition of the inductive relations
import Test.DeriveArbitrarySuchThat.NonLinearPatternsTest

set_option guard_msgs.diff true

/--
info: Try this enumerator: instance : EnumSizedSuchThat BinaryTree (fun t_1 => GoodTree in1_1 in2_1 t_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (in1_1 : Nat) (in2_1 : Nat) :
      ExceptT Plausible.GenError Enumerator BinaryTree :=
      (match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match DecOpt.decOpt (BEq.beq in1_1 in2_1) initSize with
            | Except.ok Bool.true => return BinaryTree.Leaf
            | _ => MonadExcept.throw Plausible.Gen.genericFailure]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match DecOpt.decOpt (BEq.beq in1_1 in2_1) initSize with
            | Except.ok Bool.true => return BinaryTree.Leaf
            | _ => MonadExcept.throw Plausible.Gen.genericFailure,
            ])
    fun size => aux_enum size size in1_1 in2_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (t : BinaryTree) => GoodTree in1 in2 t)
