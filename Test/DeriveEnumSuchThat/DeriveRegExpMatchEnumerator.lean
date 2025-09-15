import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Test.DeriveArbitrarySuchThat.DeriveRegExpMatchGenerator

set_option guard_msgs.diff true

/--
info: Try this enumerator: instance : EnumSizedSuchThat (List Nat) (fun s_1 => ExpMatch s_1 r0_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (r0_1 : RegExp) : OptionT Enumerator (List Nat) :=
      match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match r0_1 with
            | RegExp.EmptyStr => return List.nil
            | _ => OptionT.fail,
            match r0_1 with
            | RegExp.Char x => return List.cons x (List.nil)
            | _ => OptionT.fail,
            match r0_1 with
            | RegExp.Star re => return List.nil
            | _ => OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match r0_1 with
            | RegExp.EmptyStr => return List.nil
            | _ => OptionT.fail,
            match r0_1 with
            | RegExp.Char x => return List.cons x (List.nil)
            | _ => OptionT.fail,
            match r0_1 with
            | RegExp.Star re => return List.nil
            | _ => OptionT.fail,
            match r0_1 with
            | RegExp.App re1 re2 => do
              let s1 ← aux_enum initSize size' re1;
              do
                let s2 ← aux_enum initSize size' re2;
                return HAppend.hAppend s1 s2
            | _ => OptionT.fail,
            match r0_1 with
            | RegExp.Union re1 re2 => do
              let s_1 ← aux_enum initSize size' re1;
              return s_1
            | _ => OptionT.fail,
            match r0_1 with
            | RegExp.Union re1 re2 => do
              let s_1 ← aux_enum initSize size' re2;
              return s_1
            | _ => OptionT.fail,
            match r0_1 with
            | RegExp.Star re => do
              let s1 ← aux_enum initSize size' re;
              do
                let s2 ← aux_enum initSize size' (RegExp.Star re);
                return HAppend.hAppend s1 s2
            | _ => OptionT.fail]
    fun size => aux_enum size size r0_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (s : List Nat) => ExpMatch s r0)

-- To sample from this enumerator, we can run the following:
-- #eval runSizedEnum (EnumSizedSuchThat.enumSizedST (fun s => ExpMatch s r0)) 3
