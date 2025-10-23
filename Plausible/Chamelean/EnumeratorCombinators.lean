import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.LazyList
import Plausible.Gen
import Plausible.ArbitraryFueled

open LazyList Plausible

-- Adapted from QuickChick source code
-- https://github.com/QuickChick/QuickChick/blob/master/src/Enumerators.v

namespace EnumeratorCombinators

/-- `pickDrop xs n` and returns the `n`-th enumerator from the list `xs`,
    and returns the tail of the list from the `n+1`-th element onwards
    - Note: this is a variant of `Gen.pickDrop` where the input list does not contain weights
      (enumerators don't have weights attached to them, unlike generators) -/
def pickDrop (xs : List (ExceptT GenError Enumerator α)) (n : Nat) : ExceptT GenError Enumerator α × List (ExceptT GenError Enumerator α) :=
  match xs with
  | [] => (throw <| .genError "EnumeratorCombinators.pickDrop: Empty list", [])
  | x :: xs =>
    match n with
    | .zero => (x, xs)
    | .succ n' =>
      let (x', xs') := pickDrop xs n'
      (x', x::xs')

/-- Helper function for `backtrack` which picks one out of `total` enumerators with some initial amount of `fuel` -/
def enumerateFuel (fuel : Nat) (total : Nat) (es : List (ExceptT GenError Enumerator α)) : ExceptT GenError Enumerator α :=
  match fuel with
  | .zero => throw Gen.outOfFuel
  | .succ fuel' => do
    let n ← monadLift $ enumNatRange 0 (total - 1)
    let (e, es') := pickDrop es n
    -- Try to enumerate a value using `e`, if it fails, backtrack with `fuel'`
    -- and pick one out of the `total - k` remaining enumerators
    tryCatch e (fun _ => enumerateFuel fuel' (total - 1) es')

/-- Combines all enumerators, filtering out failed ones -/
def enumerateAll (es : List (ExceptT GenError Enumerator α)) (fuel : Nat) : LazyList (Except GenError α) :=
  es.foldl (fun acc e =>
    LazyList.append (LazyList.filter (fun | .ok _ => true | _ => false) (e fuel)) acc
  ) .lnil

/-- Tries all enumerators from a list until one returns a `pure` value or all the enumerators have
    failed once. -/
def enumerate (es : List (ExceptT GenError Enumerator α)) : ExceptT GenError Enumerator α :=
  enumerateAll es

/-- Applies the checker `f` to a `LazyList l` of values, returning the resultant `Except ε Bool`
    (the parameter `anyNone` is used to indicate whether any of the elements examined previously have been `none`) -/
def lazyListBacktrack (l : LazyList α) (f : α → Except GenError Bool) (anyNone : Bool) : Except GenError Bool :=
  let err := GenError.genError "EnumeratorCombinators.lazyListBackTrack: failure"
  match l with
  | .lnil => if anyNone then throw err else .ok false
  | .lcons x xs =>
    match f x with
    | .ok true => .ok true
    | .ok false => lazyListBacktrack xs.get f anyNone
    | .error _ => lazyListBacktrack xs.get f true

/-- Variant of `lazyListBacktrack` where the input `LazyList` contains `Except ε α` values instead of `α` -/
def lazyListBacktrackOpt (l : LazyList (Except GenError α)) (f : α → Except ε Bool) (anyNone : Bool) : Except GenError Bool :=
  let err := GenError.genError "EnumeratorCombinators.lazyListBackTrackOpt: failure"
  match l with
  | .lnil => if anyNone then throw err else .ok false
  | .lcons mx xs =>
    match mx with
    | .ok x =>
      match f x with
      | .ok true => .ok true
      | .ok false => lazyListBacktrackOpt xs.get f anyNone
      | .error _ => lazyListBacktrackOpt xs.get f true
    | .error _ => lazyListBacktrackOpt xs.get f true

/-- Iterates through all the results of the enumerator `e`, applies the checker `f` to them,
    and returns the resultant `Except GenError Bool`. -/
def enumerating (e : Enumerator α) (f : α → Except GenError Bool) (size : Nat) : Except GenError Bool :=
  lazyListBacktrack (e size) f false

/-- Variant of `enumerating`, except the input enumerator `e` may fail and has type `ExceptT GenError Enumerator α`
    - This corresponds to `bind_EC` in the Computing Correctly paper (section 4) -/
def enumeratingOpt (e : ExceptT GenError Enumerator α) (f : α → Except GenError Bool) (size : Nat) : Except GenError Bool :=
  lazyListBacktrackOpt (e size) f false

end EnumeratorCombinators
