/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
----------------------------------------------------------------------------------
-- The `DecOpt` typeclass (adapted from QuickChick)
----------------------------------------------------------------------------------

import Plausible.Gen

open Plausible

/-- The `DecOpt` class encodes partial decidability:
     - It takes a `nat` argument as fuel
     - It fails, if it can't decide (e.g. because it runs out of fuel)
     - It returns `ok true/false` if it can.
     - These are intended to be monotonic, in the
       sense that if they ever return `ok b` for
       some fuel, they will also do so for higher
       fuel values.
-/
class DecOpt (P : Prop) where
  decOpt : Nat → Except GenError Bool

/-- All `Prop`s that have a `Decidable` instance (this includes `DecidableEq`)
    can be automatically given a `DecOpt` instance -/
instance [Decidable P] : DecOpt P where
  decOpt := fun _ => .ok (decide P)


----------------------------------------------------------------------------------
-- Combinators for checkers (adapted from QuickChick sourcecode)
-- https://github.com/QuickChick/QuickChick/blob/master/src/Decidability.v
----------------------------------------------------------------------------------

namespace DecOpt

/-- `checkerBacktrack` takes a list of (thunked) sub-checkers  and returns:
    - `ok true` if *any* sub-checker does so
    - `ok false` if *all* sub-checkers do so
    - `error` otherwise
    (see section 2 of "Computing Correctly with Inductive Relations") -/
def checkerBacktrack (checkers : List (Unit → Except GenError Bool)) : Except GenError Bool :=
  let rec aux (l : List (Unit → Except GenError Bool)) (b : Bool) : Except GenError Bool :=
    let err := .genError "DecOpt.checkerBacktrack failure."
    match l with
    | c :: cs =>
      match c () with
      | .ok true => .ok true
      | .ok false => aux cs b
      | .error _ => aux cs true
    | [] => if b then throw err else .ok false
  aux checkers false

/-- Conjunction lifted to work over `Option Bool`
    (corresponds to the `.&&` infix operator in section 2 of "Computing Correctly with Inductive Relations") -/
def andOpt (a : Except GenError Bool) (b : Except GenError Bool) : Except GenError Bool :=
  match a with
  | .ok true => b
  | _ => a

/-- Folds an optional conjunction operation `andOpt` over a list of `Except _ Bool`s,
    returning the resultant `Except _ Bool` -/
def andOptList (bs : List (Except GenError Bool)) : Except GenError Bool :=
  List.foldl andOpt (.ok true) bs

end DecOpt
