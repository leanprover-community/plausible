/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
-- import Test.Tactic
-- import Test.Testable

-- Common definitions for snapshot tests
import Test.CommonDefinitions.BinaryTree
import Test.CommonDefinitions.FunctionCallInConclusion
import Test.CommonDefinitions.ListRelations
import Test.CommonDefinitions.Permutation
import Test.CommonDefinitions.STLCDefinitions

-- Tests for `#derive_generator` (derives `ArbitrarySuchThat`)
import Test.DeriveArbitrarySuchThat.DeriveBSTGenerator
import Test.DeriveArbitrarySuchThat.DeriveBalancedTreeGenerator
import Test.DeriveArbitrarySuchThat.DeriveRegExpMatchGenerator
import Test.DeriveArbitrarySuchThat.SimultaneousMatchingTests
import Test.DeriveArbitrarySuchThat.FunctionCallsTest
import Test.DeriveArbitrarySuchThat.DerivePermutationGenerator
import Test.DeriveArbitrarySuchThat.MutuallyRecursiveRelationsTest

-- Tests for `deriving Arbitrary`
import Test.DeriveArbitrary.DeriveTreeGenerator
import Test.DeriveArbitrary.DeriveSTLCTermTypeGenerators
import Test.DeriveArbitrary.DeriveNKIValueGenerator
import Test.DeriveArbitrary.DeriveNKIBinopGenerator
import Test.DeriveArbitrary.DeriveRegExpGenerator
import Test.DeriveArbitrary.StructureTest
import Test.DeriveArbitrary.BitVecStructureTest
import Test.DeriveArbitrarySuchThat.DeriveSTLCGenerator
import Test.DeriveArbitrarySuchThat.NonLinearPatternsTest
import Test.DeriveArbitrary.MissingNonRecursiveConstructorTest
import Test.DeriveArbitrary.ParameterizedTypeTest
import Test.DeriveArbitrary.MutuallyRecursiveTypeTest

-- Tests for instances of `Enum` for simple types and for correctness of enumerator combinators
import Test.Enum.EnumInstancesTest
import Test.Enum.EnumeratorSizeTest

-- Tests for `deriving Enum`
import Test.DeriveEnum.DeriveTreeEnumerator
import Test.DeriveEnum.DeriveSTLCTermTypeEnumerators
import Test.DeriveEnum.DeriveNKIValueEnumerator
import Test.DeriveEnum.DeriveNKIBinopEnumerator
import Test.DeriveEnum.DeriveRegExpEnumerator
import Test.DeriveEnum.StructureTest
import Test.DeriveEnum.BitVecStructureTest

-- Tests for `#derive_checker` (derives `DecOpt`)
import Test.DeriveDecOpt.DeriveBSTChecker
import Test.DeriveDecOpt.DeriveBalancedTreeChecker
import Test.DeriveDecOpt.DeriveRegExpMatchChecker
import Test.DeriveDecOpt.SimultaneousMatchingTests
import Test.DeriveDecOpt.ExistentialVariablesTest
import Test.DeriveDecOpt.FunctionCallsTest
import Test.DeriveDecOpt.DeriveSTLCChecker
import Test.DeriveDecOpt.NonLinearPatternsTest
import Test.DeriveDecOpt.DerivePermutationChecker

-- Tests for `#derive_enumerator` (derives `EnumSuchThat`)
import Test.DeriveEnumSuchThat.DeriveBSTEnumerator
import Test.DeriveEnumSuchThat.DeriveBalancedTreeEnumerator
import Test.DeriveEnumSuchThat.DeriveRegExpMatchEnumerator
import Test.DeriveEnumSuchThat.SimultaneousMatchingTests
import Test.DeriveEnumSuchThat.DeriveSTLCEnumerator
import Test.DeriveEnumSuchThat.NonLinearPatternsTest
import Test.DeriveEnumSuchThat.DerivePermutationEnumerator

-- Key Value Store Example
import Test.KeyValueStoreExample.KeyValueStore
import Test.KeyValueStoreExample.TestKeyValueStoreCheckerGenerators

-- Cedar Example
import Test.CedarExample.Cedar
import Test.CedarExample.CedarCheckerGenerators
import Test.CedarExample.CedarWellTypedTermGenerator
