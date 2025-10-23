/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Plausible.Random
import Plausible.Gen
import Plausible.Sampleable
import Plausible.Testable
import Plausible.Functions
import Plausible.Attr
import Plausible.Tactic
import Plausible.Arbitrary
import Plausible.DeriveArbitrary

-- Source files for Chamelean
-- (extension to Plausible for deriving generators, enumerators & checkers)
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.MakeConstrainedProducerInstance
import Plausible.Chamelean.Idents
import Plausible.Chamelean.TSyntaxCombinators
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.GeneratorCombinators
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.LazyList
import Plausible.Chamelean.DeriveEnum
import Plausible.Chamelean.Utils
import Plausible.Chamelean.Debug
import Plausible.Chamelean.UnificationMonad
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.Schedules
import Plausible.Chamelean.DeriveSchedules
import Plausible.Chamelean.MExp
