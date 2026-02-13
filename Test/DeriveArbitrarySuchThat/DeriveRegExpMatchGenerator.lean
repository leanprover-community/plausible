/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
import Plausible.Gen
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Test.DeriveArbitrary.DeriveRegExpGenerator

open Plausible
open ArbitrarySizedSuchThat

set_option guard_msgs.diff true

/-- `ExpMatch s r` holds if `s` is a string contained in the language defined by `RegExp r`,
    i.e., it "matches" `r` (a string is represented here as a `NatString`) -/
inductive ExpMatch : List Nat → RegExp → Prop where
| MEmpty : ExpMatch [] RegExp.EmptyStr
| MChar : ∀ x, ExpMatch [x] (RegExp.Char x)
| MApp : ∀ s1 re1 s2 re2,
  ExpMatch s1 re1 →
  ExpMatch s2 re2 →
  ExpMatch (s1 ++ s2) (RegExp.App re1 re2)
| MUnionL : ∀ s1 re1 re2,
  ExpMatch s1 re1 →
  ExpMatch s1 (RegExp.Union re1 re2)
| MUnionR : ∀ re1 s2 re2,
  ExpMatch s2 re2 →
  ExpMatch s2 (RegExp.Union re1 re2)
| MStar0 : ∀ re, ExpMatch [] (RegExp.Star re)
| MStarApp : ∀ s1 s2 re,
  ExpMatch s1 re →
  ExpMatch s2 (RegExp.Star re) →
  ExpMatch (s1 ++ s2) (RegExp.Star re)

-- Creates a string (sequential `App` of `Char`s) -/
def reStr (l : List Nat) (ign : RegExp) : RegExp :=
  match l with
  | [] => ign
  | [x] => RegExp.Char x
  | x :: xs => RegExp.App (RegExp.Char x) (reStr xs ign)

/-- Creates a character class regexp -/
def reCls (l : List Nat) (ign : RegExp) : RegExp :=
  match l with
  | [] => ign
  | [x] => RegExp.Char x
  | x :: xs => RegExp.Union (RegExp.Char x) (reCls xs ign)

/-- reg_exp is `[123]*` -/
def r : RegExp :=
  RegExp.Star
    (RegExp.Union
        (RegExp.Char 1)
        (RegExp.Union (RegExp.Char 2) (RegExp.Char 3)))

/-- reg_exp is `1230*[456]*` -/
def r0 : RegExp :=
  RegExp.App
    (RegExp.App (reStr [1, 2, 3] (RegExp.Char 0)) (RegExp.Star (RegExp.Char 0)))
    (RegExp.Star (reCls [4, 5, 6] (RegExp.Char 0)))

-- Generator for strings that match the regexp `re`

#guard_msgs(drop info, drop warning) in
derive_generator (fun re => ∃ (s : List Nat), ExpMatch s re)

-- To sample from this generator and print out 10 successful examples using the `Repr`
-- instance for `List Nat`, we can run the following:
#guard_msgs(drop info) in
#eval Gen.printSamples (arbitrarySizedST (fun s => ExpMatch s r) 13)
