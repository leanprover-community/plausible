import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.LazyList

open LazyList

-- Adapted from QuickChick source code
-- https://github.com/QuickChick/QuickChick/blob/master/src/Enumerators.v

namespace EnumeratorCombinators

/-- `pickDrop xs n` and returns the `n`-th enumerator from the list `xs`,
    and returns the tail of the list from the `n+1`-th element onwards
    - Note: this is a variant of `OptionTGen.pickDrop` where the input list does not contain weights
      (enumerators don't have weights attached to them, unlike generators) -/
def pickDrop (xs : List (OptionT Enumerator α)) (n : Nat) : OptionT Enumerator α × List (OptionT Enumerator α) :=
  match xs with
  | [] => (OptionT.fail, [])
  | x :: xs =>
    match n with
    | .zero => (x, xs)
    | .succ n' =>
      let (x', xs') := pickDrop xs n'
      (x', x::xs')

/-- Helper function for `backtrack` which picks one out of `total` enumerators with some initial amount of `fuel` -/
def enumerateFuel (fuel : Nat) (total : Nat) (es : List (OptionT Enumerator α)) : OptionT Enumerator α :=
  match fuel with
  | .zero => OptionT.fail
  | .succ fuel' => do
    let n ← monadLift $ enumNatRange 0 (total - 1)
    let (e, es') := pickDrop es n
    -- Try to enumerate a value using `e`, if it fails, backtrack with `fuel'`
    -- and pick one out of the `total - k` remaining enumerators
    OptionT.tryCatch e (fun () => enumerateFuel fuel' (total - n) es')

/-- Tries all enumerators from a list until one returns a `Some` value or all the enumerators have
    failed once with `None`. -/
def enumerate (es : List (OptionT Enumerator α)) : OptionT Enumerator α :=
  enumerateFuel (fuel := min es.length 10) (total := es.length) es

/-- Applies the checker `f` to a `LazyList l` of values, returning the resultant `Option Bool`
    (the parameter `anyNone` is used to indicate whether any of the elements examined previously have been `none`) -/
def lazyListBacktrack (l : LazyList α) (f : α → Option Bool) (anyNone : Bool) : Option Bool :=
  match l with
  | .lnil => if anyNone then none else some false
  | .lcons x xs =>
    match f x with
    | some true => some true
    | some false => lazyListBacktrack xs.get f anyNone
    | none => lazyListBacktrack xs.get f true

/-- Variant of `lazyListBacktrack` where the input `LazyList` contains `Option α` values instead of `α` -/
def lazyListBacktrackOpt (l : LazyList (Option α)) (f : α → Option Bool) (anyNone : Bool) : Option Bool :=
  match l with
  | .lnil => if anyNone then none else some false
  | .lcons mx xs =>
    match mx with
    | some x =>
      match f x with
      | some true => some true
      | some false => lazyListBacktrackOpt xs.get f anyNone
      | none => lazyListBacktrackOpt xs.get f true
    | .none => lazyListBacktrackOpt xs.get f true

/-- Iterates through all the results of the enumerator `e`, applies the checker `f` to them,
    and returns the resultant `Option Bool`. -/
def enumerating (e : Enumerator α) (f : α → Option Bool) (size : Nat) : Option Bool :=
  lazyListBacktrack (e size) f false

/-- Variant of `enumerating`, except the input enumerator `e` may fail and has type `OptionT Enumerator α`
    - This corresponds to `bind_EC` in the Computing Correctly paper (section 4) -/
def enumeratingOpt (e : OptionT Enumerator α) (f : α → Option Bool) (size : Nat) : Option Bool :=
  lazyListBacktrackOpt (e size) f false

end EnumeratorCombinators
