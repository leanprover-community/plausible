/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
-- Example taken from section 3.1 of "Computing Correctly with Inductive Relations"
-- Note how `n * n` is a function call that appears in the conclusion of a constructor
-- for an inductive relation
inductive square_of : Nat → Nat → Prop where
  | sq : forall n, square_of n (n * n)
