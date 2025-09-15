import Plausible.Gen
open Plausible

-- TODO: figure out some way to avoid having two versions of `frequency, sized, thunkGen`
-- between `GeneratorCombinators.lean` and `OptionTGen.lean`
-- (one for `Gen α`, the other for `OptionT Gen α`)

namespace GeneratorCombinators

/-- `pick default xs n` chooses a weight & a generator `(k, gen)` from the list `xs` such that `n < k`.
    If `xs` is empty, the `default` generator with weight 0 is returned.  -/
def pick (default : Gen α) (xs : List (Nat × Gen α)) (n : Nat) : Nat × Gen α :=
  match xs with
  | [] => (0, default)
  | (k, x) :: xs =>
    if n < k then
      (k, x)
    else
      pick default xs (n - k)

/-- Sums all the weights in an association list containing `Nat`s and `α`s -/
def sumFst (gs : List (Nat × α)) : Nat :=
  List.foldl (fun acc p => acc + p.fst) 0 gs

/-- Picks one of the generators in `gs` at random, returning the `default` generator
    if `gs` is empty.

    (This is a more ergonomic version of Plausible's `Gen.oneOf` which doesn't
    require the caller to supply a proof that the list index is in bounds.) -/
def oneOfWithDefault (default : Gen α) (gs : List (Gen α)) : Gen α :=
  match gs with
  | [] => default
  | _ => do
    let idx ← Gen.choose Nat 0 (gs.length - 1) (by omega)
    List.getD gs idx.val default

/-- `frequency` picks a generator from the list `gs` according to the weights in `gs`.
    If `gs` is empty, the `default` generator is returned.  -/
def frequency (default : Gen α) (gs : List (Nat × Gen α)) : Gen α := do
  let total := sumFst gs
  let n ← Gen.choose Nat 0 (total - 1) (by omega)
  .snd (pick default gs n)

/-- `sized f` constructs a generator that depends on its `size` parameter -/
def sized (f : Nat → Gen α) : Gen α :=
  Gen.getSize >>= f

/-- Delays the evaluation of a generator by taking in a function `f : Unit → Gen α` -/
def thunkGen (f : Unit → Gen α) : Gen α :=
  f ()

/-- `elementsWithDefault` constructs a generator from a list `xs` and a `default` element.
    If `xs` is non-empty, the generator picks an element from `xs` uniformly; otherwise it returns the `default` element.

    Remarks:
    - this is a version of Plausible's `Gen.elements` where the caller doesn't have
      to supply a proof that the list index is in bounds
    - This is a version of QuickChick's `elems_` combinator -/
def elementsWithDefault [Inhabited α] (default : α) (xs : List α) : Gen α :=
  match xs with
  | [] => return default
  | _ => do
    let i ← Subtype.val <$> Gen.choose Nat 0 (xs.length - 1) (by omega)
    return xs[i]!

end GeneratorCombinators
