import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Test.DeriveArbitrarySuchThat.DeriveBSTGenerator

set_option guard_msgs.diff true

/--
info: Try this enumerator: instance : EnumSizedSuchThat Nat (fun x_1 => Between lo_1 x_1 hi_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (lo_1 : Nat) (hi_1 : Nat) : OptionT Enumerator Nat :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match hi_1 with
            | Nat.succ (Nat.succ m) =>
              match DecOpt.decOpt (LE.le lo_1 m) initSize with
              | Option.some Bool.true => return Nat.succ lo_1
              | _ => OptionT.fail
            | _ => OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match hi_1 with
            | Nat.succ (Nat.succ m) =>
              match DecOpt.decOpt (LE.le lo_1 m) initSize with
              | Option.some Bool.true => return Nat.succ lo_1
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match hi_1 with
            | Nat.succ o => do
              let m ← aux_enum initSize size' lo_1 o;
              return Nat.succ m
            | _ => OptionT.fail]
    fun size => aux_enum size size lo_1 hi_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (x : Nat) => Between lo x hi)

/--
info: Try this enumerator: instance : EnumSizedSuchThat BinaryTree (fun t_1 => BST lo_1 hi_1 t_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (lo_1 : Nat) (hi_1 : Nat) : OptionT Enumerator BinaryTree :=
      match size with
      | Nat.zero => EnumeratorCombinators.enumerate [return BinaryTree.Leaf]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [return BinaryTree.Leaf, do
            let x ← EnumSizedSuchThat.enumSizedST (fun x => Between lo_1 x hi_1) initSize;
            do
              let l ← aux_enum initSize size' lo_1 x;
              do
                let r ← aux_enum initSize size' x hi_1;
                return BinaryTree.Node x l r]
    fun size => aux_enum size size lo_1 hi_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (t : BinaryTree) => BST lo hi t)
