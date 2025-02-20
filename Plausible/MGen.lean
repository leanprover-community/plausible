/-
Copyright (c) 2025 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil
-/
import Plausible.Random
import Batteries.Data.List.Perm
import Plausible.Gen
import Lean
open Lean Meta

namespace Plausible

open Random

abbrev MRand := RandT MetaM

instance : MonadLift Rand MRand where
  monadLift := fun x s => return x.run s

abbrev MGen (α : Type) := ReaderT (ULift Nat) MRand α

instance : MonadLift Gen MGen where
  monadLift := fun x n => x.run n.down
