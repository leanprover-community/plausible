import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Test.DeriveDecOpt.SimultaneousMatchingTests

-- See `Test/CommonDefinitions/ListRelations.lean` for the definition of the inductive relations
import Test.CommonDefinitions.ListRelations

set_option guard_msgs.diff true

/--
info: Try this enumerator: instance : EnumSizedSuchThat (List Nat) (fun l_1 => InList x_1 l_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (x_1 : Nat) : OptionT Enumerator (List Nat) :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [do
            let l ← Enum.enum;
            return List.cons x_1 l]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [do
            let l ← Enum.enum;
            return List.cons x_1 l, do
            let l ← aux_enum initSize size' x_1;
            do
              let y ← Enum.enum;
              return List.cons y l]
    fun size => aux_enum size size x_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (l : List Nat) => InList x l)

/--
info: Try this enumerator: instance : EnumSizedSuchThat (List Nat) (fun l_1 => MinOk l_1 a_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (a_1 : List Nat) : OptionT Enumerator (List Nat) :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match a_1 with
            | List.nil => return List.nil
            | _ => OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match a_1 with
            | List.nil => return List.nil
            | _ => OptionT.fail,
            match a_1 with
            | List.cons x l' => do
              let l_1 ← aux_enum initSize size' l';
              match DecOpt.decOpt (InList x l_1) initSize with
                | Option.some Bool.true => return l_1
                | _ => OptionT.fail
            | _ => OptionT.fail]
    fun size => aux_enum size size a_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (l: List Nat) => MinOk l a)

/--
info: Try this enumerator: instance : EnumSizedSuchThat (List Nat) (fun l_1 => MinEx n_1 l_1 a_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (n_1 : Nat) (a_1 : List Nat) : OptionT Enumerator (List Nat) :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match a_1 with
            | List.nil =>
              match n_1 with
              | Nat.zero => return List.nil
              | _ => OptionT.fail
            | _ => OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match a_1 with
            | List.nil =>
              match n_1 with
              | Nat.zero => return List.nil
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match a_1 with
            | List.cons x l' =>
              match n_1 with
              | Nat.succ n => do
                let l_1 ← EnumSizedSuchThat.enumSizedST (fun l_1 => InList x l_1) initSize;
                match DecOpt.decOpt (MinEx n l_1 l') initSize with
                  | Option.some Bool.true => return l_1
                  | _ => OptionT.fail
              | _ => OptionT.fail
            | _ => OptionT.fail]
    fun size => aux_enum size size n_1 a_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (l: List Nat) => MinEx n l a)
