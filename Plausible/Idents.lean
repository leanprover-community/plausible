/-
Copyright (c) 2025 Ernest Ng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ernest Ng
-/
import Lean
import Plausible.Gen

import Plausible.Arbitrary
import Plausible.Gen

/-!
# Idents for derived generators

This file defines `Ident`s for commonly-called functions & commonly-referenced types --
these are used in the body of derived generators (when deriving `Arbitrary` instances).

-/

open Lean Meta Std
open Plausible


namespace Idents

/-- Ident for the `Gen.thunkGen` function -/
def thunkGenFn : Ident := mkIdent ``Gen.thunkGen

/-- Ident for the `Gen.frequency` function -/
def frequencyFn : Ident := mkIdent ``Gen.frequency

/-- Ident for the `Gen.oneOfWithDefault` function -/
def oneOfWithDefaultGenCombinatorFn : Ident := mkIdent ``Gen.oneOfWithDefault

/-- Ident for the inner `aux_arb` function that appears in derived generators -/
def auxArbFn : Ident := mkIdent `aux_arb

/-- Ident for the `pure` function -/
def pureFn : Ident := mkIdent `pure

/-- Ident for the `some` `Option` constructor -/
def someFn : Ident := mkIdent ``some

/-- Ident for the `true` boolean literal -/
def trueIdent : Ident := mkIdent ``true

/-- Ident for the `false` boolean literal -/
def falseIdent : Ident := mkIdent ``false

-- Idents for size arguments to generators
/-- Ident for the `initSize` parameter used in generators -/
def initSizeIdent : Ident := mkIdent `initSize

/-- Ident for the `size` parameter used in generators -/
def sizeIdent : Ident := mkIdent `size

/-- Ident for the `ArbitrarySized` typeclass -/
def arbitrarySizedTypeclass : Ident := mkIdent ``ArbitrarySized

-- Idents for typeclass functions
/-- Ident for the `Arbitrary.arbitrary` function -/
def arbitraryFn : Ident := mkIdent ``Arbitrary.arbitrary

/-- Ident for the `ArbitrarySized.arbitrarySized` function -/
def arbitrarySizedFn : Ident := mkIdent ``ArbitrarySized.arbitrarySized

/-- Ident for the unqualified `arbitrarySized` function -/
def unqualifiedArbitrarySizedFn : Ident := mkIdent `arbitrarySized

-- Idents for commonly-used types / constructors / type constructors
/-- Ident for the `Bool` type -/
def boolIdent : Ident := mkIdent ``Bool

/-- Ident for the `Nat` type -/
def natIdent : Ident := mkIdent ``Nat

/-- Ident for the `Nat.zero` constructor -/
def zeroIdent : Ident := mkIdent ``Nat.zero

/-- Ident for the `Nat.succ` constructor -/
def succIdent : Ident := mkIdent ``Nat.succ

/-- Ident for the `Option` type constructor -/
def optionTypeConstructor : Ident := mkIdent `Option

/-- Ident for the `Plausible.Gen` type constructor -/
def genTypeConstructor : Ident := mkIdent ``Plausible.Gen

/-- Produces a fresh user-facing & *accessible* identifier with respect to the local context
    - Note: prefer using this function over `Core.mkFreshUserName`, which is meant
      to create fresh names that are *inaccessible* to the user (i.e. `mkFreshUserName` will
      add daggers (`†`) to the name to make them inaccessible).
    - This function ensures that the identifier is fresh
      by adding suffixes containing underscores/numbers when necessary (in lieu of adding daggers). -/
def mkFreshAccessibleIdent (localCtx : LocalContext) (name : Name) : Ident :=
  mkIdent $ LocalContext.getUnusedName localCtx name

/-- `genFreshName existingNames namePrefix` produces a fresh name with the prefix `namePrefix`
     that is guaranteed to be not within `existingNames`.
    - Note: the body of this function operates in the identity monad since
      we want local mutable state and access to the syntactic sugar
      provided by `while` loops -/
def genFreshName (existingNames : Array Name) (namePrefix : Name) : Name :=
  Id.run do
    let mut count := 0
    let mut freshName := Name.appendAfter namePrefix s!"_{count}"
    while (existingNames.contains freshName) do
      count := count + 1
      freshName := Name.appendAfter namePrefix s!"_{count}"
    return freshName

/-- `genFreshNames existingNames namePrefixes` produces an array of fresh names, all of them
    guaranteed to be not in `existingNames`, where the `i`-th fresh name produced has prefix `namePrefixes[i]`.

    This function is implemented using a fold: when producing the `i`-th fresh name,
    we ensure that it does not clash with `existingNames` *and* the previous `i-1` fresh names produced. -/
def genFreshNames (existingNames : Array Name) (namePrefixes : Array Name) : Array Name :=
  Array.foldl (fun acc name => Array.push acc (genFreshName (acc ++ existingNames) name)) #[] namePrefixes

end Idents
