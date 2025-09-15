import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveChecker
import Test.DeriveArbitrary.DeriveRegExpGenerator
import Test.DeriveArbitrarySuchThat.DeriveRegExpMatchGenerator

open DecOpt

set_option guard_msgs.diff true

-- TODO: re-enable these failing tests after checker/enumerator deriver has been updated to use schedules

/-
info: Try this checker: instance : DecOpt (ExpMatch s r0) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (s_1 : List Nat) (r0_1 : RegExp) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match s_1, r0_1 with
            | [], RegExp.EmptyStr => Option.some Bool.true
            | _, _ => Option.some Bool.false,
            fun _ =>
            match s_1, r0_1 with
            | [x], RegExp.Char x_0 => Option.some Bool.true
            | _, _ => Option.some Bool.false,
            fun _ =>
            match s_1, r0_1 with
            | [], RegExp.Star re => Option.some Bool.true
            | _, _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match s_1, r0_1 with
            | [], RegExp.EmptyStr => Option.some Bool.true
            | _, _ => Option.some Bool.false,
            fun _ =>
            match s_1, r0_1 with
            | [x], RegExp.Char x_0 => Option.some Bool.true
            | _, _ => Option.some Bool.false,
            fun _ =>
            match s_1, r0_1 with
            | s1 ++ s2, RegExp.App re1 re2 =>
              DecOpt.andOptList [aux_dec initSize size' s1 re1, aux_dec initSize size' s2 re2]
            | _, _ => Option.some Bool.false,
            fun _ =>
            match r0_1 with
            | RegExp.Union re1 re2 => aux_dec initSize size' s_1 re1
            | _ => Option.some Bool.false,
            fun _ =>
            match r0_1 with
            | RegExp.Union re1 re2 => aux_dec initSize size' s_1 re2
            | _ => Option.some Bool.false,
            fun _ =>
            match s_1, r0_1 with
            | [], RegExp.Star re => Option.some Bool.true
            | _, _ => Option.some Bool.false,
            fun _ =>
            match s_1, r0_1 with
            | s1 ++ s2, RegExp.Star re =>
              DecOpt.andOptList [aux_dec initSize size' s1 re, aux_dec initSize size' s2 (RegExp.Star re)]
            | _, _ => Option.some Bool.false]
    fun size => aux_dec size size s r0
-/
-- #guard_msgs(info, drop warning) in
-- #derive_checker (ExpMatch s r0)
