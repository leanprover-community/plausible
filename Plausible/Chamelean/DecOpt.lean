----------------------------------------------------------------------------------
-- The `DecOpt` typeclass (adapted from QuickChick)
----------------------------------------------------------------------------------

/-- The `DecOpt` class encodes partial decidability:
     - It takes a `nat` argument as fuel
     - It returns `none`, if it can't decide (e.g. because it runs out of fuel)
     - It returns `some true/some false` if it can.
     - These are supposed to be monotonic, in the
       sense that if they ever return `some b` for
       some fuel, they will also do so for higher
       fuel values.
-/
class DecOpt (P : Prop) where
  decOpt : Nat → Option Bool

/-- All `Prop`s that have a `Decidable` instance (this includes `DecidableEq`)
    can be automatically given a `DecOpt` instance -/
instance [Decidable P] : DecOpt P where
  decOpt := fun _ => some (decide P)


----------------------------------------------------------------------------------
-- Combinators for checkers (adapted from QuickChick sourcecode)
-- https://github.com/QuickChick/QuickChick/blob/master/src/Decidability.v
----------------------------------------------------------------------------------

namespace DecOpt

/-- `checkerBacktrack` takes a list of (thunked) sub-checkers  and returns:
    - `some true` if *any* sub-checker does so
    - `some false` if *all* sub-checkers do so
    - `none` otherwise
    (see section 2 of "Computing Correctly with Inductive Relations") -/
def checkerBacktrack (checkers : List (Unit → Option Bool)) : Option Bool :=
  let rec aux (l : List (Unit → Option Bool)) (b : Bool) : Option Bool :=
    match l with
    | c :: cs =>
      match c () with
      | some true => some true
      | some false => aux cs b
      | none => aux cs true
    | [] => if b then none else some false
  aux checkers false

/-- Conjunction lifted to work over `Option Bool`
    (corresponds to the `.&&` infix operator in section 2 of "Computing Correctly with Inductive Relations") -/
def andOpt (a : Option Bool) (b : Option Bool) : Option Bool :=
  match a with
  | some true => b
  | _ => a

/-- Folds an optional conjunction operation `andOpt` over a list of `Option Bool`s,
    returning the resultant `Option Bool` -/
def andOptList (bs : List (Option Bool)) : Option Bool :=
  List.foldl andOpt (some true) bs

end DecOpt
