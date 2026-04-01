/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import PlausibleTest.Tactic
import PlausibleTest.Testable

-- Tests for `deriving Arbitrary`
import PlausibleTest.DeriveArbitrary.DeriveTreeGenerator
import PlausibleTest.DeriveArbitrary.DeriveSTLCTermTypeGenerators
import PlausibleTest.DeriveArbitrary.DeriveNKIValueGenerator
import PlausibleTest.DeriveArbitrary.DeriveNKIBinopGenerator
import PlausibleTest.DeriveArbitrary.DeriveRegExpGenerator
import PlausibleTest.DeriveArbitrary.StructureTest
import PlausibleTest.DeriveArbitrary.BitVecStructureTest
import PlausibleTest.DeriveArbitrary.MissingNonRecursiveConstructorTest
import PlausibleTest.DeriveArbitrary.ParameterizedTypeTest
import PlausibleTest.DeriveArbitrary.MutuallyRecursiveTypeTest
