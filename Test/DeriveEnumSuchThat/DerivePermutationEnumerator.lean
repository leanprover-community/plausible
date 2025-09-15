import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Test.CommonDefinitions.Permutation


/--
info: Try this enumerator: instance : EnumSizedSuchThat (List Nat) (fun l_1 => Permutation l_1 l'_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (l'_1 : List Nat) : OptionT Enumerator (List Nat) :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match l'_1 with
            | List.nil => return List.nil
            | _ => OptionT.fail,
            match l'_1 with
            | List.cons x (List.cons y l) => return List.cons y (List.cons x l)
            | _ => OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match l'_1 with
            | List.nil => return List.nil
            | _ => OptionT.fail,
            match l'_1 with
            | List.cons x (List.cons y l) => return List.cons y (List.cons x l)
            | _ => OptionT.fail,
            match l'_1 with
            | List.cons x l' => do
              let l ← aux_enum initSize size' l';
              return List.cons x l
            | _ => OptionT.fail,
            do
            let l' ← aux_enum initSize size' l'_1;
            do
              let l_1 ← aux_enum initSize size' l';
              return l_1]
    fun size => aux_enum size size l'_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (l : List Nat) => Permutation l l')

/--
info: Try this enumerator: instance : EnumSizedSuchThat (List Nat) (fun l_1 => Permutation l'_1 l_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (l'_1 : List Nat) : OptionT Enumerator (List Nat) :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match l'_1 with
            | List.nil => return List.nil
            | _ => OptionT.fail,
            match l'_1 with
            | List.cons y (List.cons x l) => return List.cons x (List.cons y l)
            | _ => OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match l'_1 with
            | List.nil => return List.nil
            | _ => OptionT.fail,
            match l'_1 with
            | List.cons y (List.cons x l) => return List.cons x (List.cons y l)
            | _ => OptionT.fail,
            match l'_1 with
            | List.cons x l => do
              let l' ← aux_enum initSize size' l;
              return List.cons x l'
            | _ => OptionT.fail,
            do
            let l' ← aux_enum initSize size' l'_1;
            do
              let l_1 ← aux_enum initSize size' l';
              return l_1]
    fun size => aux_enum size size l'_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (l : List Nat) => Permutation l' l)
