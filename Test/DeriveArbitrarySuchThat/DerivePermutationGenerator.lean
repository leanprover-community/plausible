import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Test.CommonDefinitions.Permutation

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List Nat) (fun l_1 => Permutation l_1 l'_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (l'_1 : List Nat) : OptionT Plausible.Gen (List Nat) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match l'_1 with
              | List.nil => return List.nil
              | _ => OptionT.fail),
            (1,
              match l'_1 with
              | List.cons x (List.cons y l) => return List.cons y (List.cons x l)
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match l'_1 with
              | List.nil => return List.nil
              | _ => OptionT.fail),
            (1,
              match l'_1 with
              | List.cons x (List.cons y l) => return List.cons y (List.cons x l)
              | _ => OptionT.fail),
            (Nat.succ size',
              match l'_1 with
              | List.cons x l' => do
                let l ← aux_arb initSize size' l';
                return List.cons x l
              | _ => OptionT.fail),
            (Nat.succ size', do
              let l' ← aux_arb initSize size' l'_1;
              do
                let l_1 ← aux_arb initSize size' l';
                return l_1)]
    fun size => aux_arb size size l'_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (l : List Nat) => Permutation l l')

/--
info: Try this generator: instance : ArbitrarySizedSuchThat (List Nat) (fun l_1 => Permutation l'_1 l_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (l'_1 : List Nat) : OptionT Plausible.Gen (List Nat) :=
      match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match l'_1 with
              | List.nil => return List.nil
              | _ => OptionT.fail),
            (1,
              match l'_1 with
              | List.cons y (List.cons x l) => return List.cons x (List.cons y l)
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match l'_1 with
              | List.nil => return List.nil
              | _ => OptionT.fail),
            (1,
              match l'_1 with
              | List.cons y (List.cons x l) => return List.cons x (List.cons y l)
              | _ => OptionT.fail),
            (Nat.succ size',
              match l'_1 with
              | List.cons x l => do
                let l' ← aux_arb initSize size' l;
                return List.cons x l'
              | _ => OptionT.fail),
            (Nat.succ size', do
              let l' ← aux_arb initSize size' l'_1;
              do
                let l_1 ← aux_arb initSize size' l';
                return l_1)]
    fun size => aux_arb size size l'_1
-/
#guard_msgs(info, drop warning) in
#derive_generator (fun (l : List Nat) => Permutation l' l)
