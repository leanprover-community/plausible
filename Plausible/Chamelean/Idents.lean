/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/

module

public import Lean
import Plausible.Gen
open Lean Meta Std

-- Create idents for commonly-called functions & commonly-referenced types

namespace Idents

public section

-- Idents for commonly-called functions
def generatorCombinatorsThunkGenFn : Ident := mkIdent $ Name.mkStr2 "GeneratorCombinators" "thunkGen"
def frequencyFn : Ident := mkIdent $ Name.mkStr2 "GeneratorCombinators" "frequency"
def oneOfWithDefaultGenCombinatorFn : Ident := mkIdent $ Name.mkStr2 "GeneratorCombinators" "oneOfWithDefault"
def oneOfWithDefaultEnumCombinatorFn : Ident := mkIdent $ Name.mkStr2 "EnumeratorCombinators" "oneOfWithDefault"
def interpSampleFn : Ident := mkIdent $ Name.mkStr3 "Plausible" "SampleableExt" "interpSample"

/-- Ident for the inner `aux_arb` function that appears in derived generators -/
def auxArbFn : Ident := mkIdent $ Name.mkStr1 "aux_arb"

/-- Ident for the inner `aux_enum` function that appears in derived enumerators -/
def auxEnumFn : Ident := mkIdent $ Name.mkStr1 "aux_enum"

/-- Ident for the inner `aux_dec` function that appears in derived checkers -/
def auxDecFn : Ident := mkIdent $ Name.mkStr1 "aux_dec"

/-- Ident for the `DecOpt.andOptList` checker combinator (see `DecOpt.lean`) -/
def andOptListFn : Ident := mkIdent $ Name.mkStr2 "DecOpt" "andOptList"

/-- Ident for `GeneratorCombinators.backtrack`. -/
def genBacktrackFn : Ident := mkIdent $ Name.mkStr2 "GeneratorCombinators" "backtrack"

/-- Ident for the `DecOpt.checkerBacktrack` checker combinator (see `DecOpt.lean`) -/
def checkerBacktrackFn : Ident := mkIdent $ Name.mkStr2 "DecOpt" "checkerBacktrack"

/-- Ident for the `EnumeratorCombinators.enumerate` combinator (see `EnumeratorCombinators.lean`) -/
def enumerateFn : Ident := mkIdent $ Name.mkStr2 "EnumeratorCombinators" "enumerate"

/-- Ident for the `EnumeratorCombinators.enumerating` combinator (see `EnumeratorCombinators.lean`) -/
def enumeratingFn : Ident := mkIdent $ Name.mkStr2 "EnumeratorCombinators" "enumerating"

/-- Ident for the `EnumeratorCombinators.enumeratingOpt` combinator (see `EnumeratorCombinators.lean`) -/
def enumeratingOptFn : Ident := mkIdent $ Name.mkStr2 "EnumeratorCombinators" "enumeratingOpt"

/-- Ident for `pure`. -/
def pureFn : Ident := mkIdent $ Name.mkStr1 "pure"

/-- Idents for boolean literals. -/
def trueIdent : Ident := mkIdent ``true
def falseIdent : Ident := mkIdent ``false

-- Idents for size arguments to generators
def initSizeIdent : Ident := mkIdent $ Name.mkStr1 "initSize"
def sizeIdent : Ident := mkIdent $ Name.mkStr1 "size"

/-- `Ident` representing `MonadExcept.throw`-/
def failFn : Ident := mkIdent ``MonadExcept.throw
def genericFailure : Ident := mkIdent ``Plausible.Gen.genericFailure

-- Idents for typeclasses
def arbitrarySizedSuchThatTypeclass : Ident := mkIdent $ Name.mkStr1 "ArbitrarySizedSuchThat"
def enumSizedSuchThatTypeclass : Ident := mkIdent $ Name.mkStr1 "EnumSizedSuchThat"
def arbitrarySizedTypeclass : Ident := mkIdent $ Name.mkStr1 "ArbitrarySized"
def enumSizedTypeclass : Ident := mkIdent $ Name.mkStr1 "EnumSized"
def decOptTypeclass : Ident := mkIdent $ Name.mkStr1 "DecOpt"

-- Idents for typeclass functions
def arbitraryFn : Ident := mkIdent $ Name.mkStr2 "Arbitrary" "arbitrary"
def enumFn : Ident := mkIdent $ Name.mkStr2 "Enum" "enum"
def enumSTFn : Ident := mkIdent $ Name.mkStr2 "EnumSuchThat" "enumST"
def arbitrarySizedFn : Ident := mkIdent $ Name.mkStr2 "ArbitrarySized" "arbitrarySized"
def unqualifiedArbitrarySizedFn : Ident := mkIdent $ Name.mkStr1 "arbitrarySized"
def unqualifiedEnumSizedFn : Ident := mkIdent $ Name.mkStr1 "enumSized"
def arbitrarySTFn : Ident := mkIdent $ Name.mkStr2 "ArbitrarySuchThat" "arbitraryST"
def unqualifiedArbitrarySizedSTFn : Ident := mkIdent $ Name.mkStr1 "arbitrarySizedST"
def unqualifiedEnumSizedSTFn : Ident := mkIdent $ Name.mkStr1 "enumSizedST"
def unqualifiedDecOptFn : Ident := mkIdent $ Name.mkStr1 "decOpt"
def decOptFn : Ident := mkIdent $ Name.mkStr2 "DecOpt" "decOpt"


-- Idents for commonly-used types / constructors / type constructors
def boolIdent : Ident := mkIdent ``Bool
def natIdent : Ident := mkIdent ``Nat
def zeroIdent : Ident := mkIdent ``Nat.zero
def succIdent : Ident := mkIdent ``Nat.succ
def exceptTTypeConstructor : Ident := mkIdent ``ExceptT
def exceptTypeConstructor : Ident := mkIdent ``Except
def genErrorType : Ident := mkIdent ``Plausible.GenError
def genTypeConstructor : Ident := mkIdent ``Plausible.Gen
def enumTypeConstructor : Ident := mkIdent $ Name.mkStr1 "Enumerator"


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

/-- `lookupNameInNameMap nameMap existingNames name` returns the `Ident` for the freshened name associated with
     the key `name` in `nameMap`. If `name` doesn't appear as a key in `nameMap`, a fresh name
     that is guaranteed not to clash with `existingNames` is produced. -/
def lookupFreshenedNameInNameMap (nameMap : HashMap Name Name) (existingNames : Array Name) (name : Name) : Ident :=
  match nameMap[name]? with
  | some newName => Lean.mkIdent newName
  | none => Lean.mkIdent (genFreshName existingNames name)

/-- Extracts the name of a parameter from a corresponding `Term`.
    If this is not possible, a fresh user-facing name is produced. -/
def extractParamName (arg : Term) : MetaM Name :=
  match arg with
  | `($name:ident) => return name.getId
  | _ => return (genFreshName #[] `param)

end

end Idents
