/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Test.Tactic
import Test.Testable

-- Tests for `deriving Arbitrary`
import Test.DeriveArbitrary.DeriveTreeGenerator
import Test.DeriveArbitrary.DeriveSTLCTermTypeGenerators
import Test.DeriveArbitrary.DeriveNKIValueGenerator
import Test.DeriveArbitrary.DeriveNKIBinopGenerator
import Test.DeriveArbitrary.DeriveRegExpGenerator
import Test.DeriveArbitrary.StructureTest
import Test.DeriveArbitrary.BitVecStructureTest
