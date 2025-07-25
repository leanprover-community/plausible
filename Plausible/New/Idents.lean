import Lean
import Plausible.Gen
open Lean Meta Std

-- Create idents for commonly-called functions & commonly-referenced types

namespace Idents

-- Idents for commonly-called functions
def generatorCombinatorsThunkGenFn : Ident := mkIdent $ Name.mkStr2 "GeneratorCombinators" "thunkGen"
def frequencyFn : Ident := mkIdent $ Name.mkStr2 "GeneratorCombinators" "frequency"
def oneOfWithDefaultGenCombinatorFn : Ident := mkIdent $ Name.mkStr2 "GeneratorCombinators" "oneOfWithDefault"
def oneOfWithDefaultEnumCombinatorFn : Ident := mkIdent $ Name.mkStr2 "EnumeratorCombinators" "oneOfWithDefault"

/-- Ident for the inner `aux_arb` function that appears in derived generators -/
def auxArbFn : Ident := mkIdent $ Name.mkStr1 "aux_arb"

def pureFn : Ident := mkIdent $ Name.mkStr1 "pure"
def someFn : Ident := mkIdent ``some
def trueIdent : Ident := mkIdent ``true
def falseIdent : Ident := mkIdent ``false

-- Idents for size arguments to generators
def initSizeIdent : Ident := mkIdent $ Name.mkStr1 "initSize"
def sizeIdent : Ident := mkIdent $ Name.mkStr1 "size"

def arbitrarySizedTypeclass : Ident := mkIdent $ Name.mkStr1 "ArbitrarySized"

-- Idents for typeclass functions
def arbitraryFn : Ident := mkIdent $ Name.mkStr2 "Arbitrary" "arbitrary"
def arbitrarySizedFn : Ident := mkIdent $ Name.mkStr2 "ArbitrarySized" "arbitrarySized"
def unqualifiedArbitrarySizedFn : Ident := mkIdent $ Name.mkStr1 "arbitrarySized"


-- Idents for commonly-used types / constructors / type constructors
def boolIdent : Ident := mkIdent ``Bool
def natIdent : Ident := mkIdent ``Nat
def zeroIdent : Ident := mkIdent ``Nat.zero
def succIdent : Ident := mkIdent ``Nat.succ
def optionTypeConstructor : Ident := mkIdent `Option
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
