
-- Adapted from QuickChick source code
-- https://github.com/QuickChick/QuickChick/blob/master/src/LazyList.v

/-- Lazy Lists are implemented by thunking the computation for the tail of a cons-cell. -/
inductive LazyList (α : Type u) where
  | lnil
  | lcons : α → Thunk (LazyList α) → LazyList α
deriving Inhabited

namespace LazyList

/-- Membership in a `LazyList`. -/
inductive InLazyList {α : Type u} (a : α) : LazyList α -> Prop where
| InLHead l : InLazyList a (lcons a l)
| InLNext b l : a ≠ b -> InLazyList a l.get -> InLazyList a (lcons b l)

/-- Convenience definition for inverted membership. -/
abbrev InLazyList' {α} l (a : α) := InLazyList a l

instance {α} : Membership α (LazyList α) :=
 Membership.mk InLazyList'

/-- Tail-recursive helper for converting `LazyList` to `List`, where `acc` is the list accumulated so far
    - The accumulation prevents stack overflow when converting large `LazyList`s to regular lists -/
def toListAux (acc : List α) : LazyList α → List α
  | .lnil => acc.reverse
  | .lcons x xs => toListAux (x :: acc) xs.get

/-- Converts a `LazyList` to an ordinary list by forcing all the embedded thunks -/
def toList (l : LazyList α) : List α :=
  toListAux [] l

/-- Converts a `List` into a `LazyList`-/
def fromList (l : List α) : LazyList α :=
  l.foldr (fun a acc => .lcons a ⟨fun _ => acc⟩) .lnil

/-- We pretty-print `LazyList`s by converting them to ordinary lists
    (forcing all the thunks) & pretty-printing the resultant list. -/
instance [Repr α] : Repr (LazyList α) where
  reprPrec l _ := repr l.toList

/-- Retrieves a prefix of the `LazyList` (only the thunks in the prefix are evaluated) -/
def take (n : Nat) (l : LazyList α) : List α := go n l []
  where
  go n l acc :=
  match n with
  | .zero => acc
  | .succ n' =>
    match l with
    | .lnil => acc
    | .lcons x xs => go n' xs.get (x :: acc)

/-- Get the first element of the list, if there is one. otherwise return `.none`. -/
def head? (l : LazyList α) : Option α :=
  match l with
  | lnil => none
  | lcons x _ => some x

/-- Appends two `LazyLists` together -/
def append (xs : LazyList α) (ys : LazyList α) : LazyList α :=
  match xs with
  | lnil => ys
  | lcons x xs => lcons x ⟨fun _ => append xs.get ys⟩

/-- `observe tag i` uses `dbg_trace` to emit a trace of the variable
    associated with `tag` -/
def observe (tag : String) (i : Fin n) : Nat :=
  dbg_trace "{tag}: {i.val}"
  i.val

/-- Maps a function over a LazyList -/
def mapLazyList (f : α → β) (l : LazyList α) : LazyList β :=
  match l with
  | .lnil => .lnil
  | .lcons x xs => .lcons (f x) ⟨fun _ => mapLazyList f xs.get⟩

/-- Length of a LazyList. Warning: this forces the whole list. -/
def length (l : LazyList α) : Nat :=
  let rec aux l n :=
    match l with
    | .lnil => n
    | .lcons _ xs => aux xs.get (1 + n)
  aux l 0

/-- `Functor` instance for `LazyList` -/
instance : Functor LazyList where
  map := mapLazyList

/-- Return the lazylist that contains the elements `x` of `l` such that `p x = .true`. -/
def filter {α} (p : α -> Bool) (l : LazyList α) : LazyList α :=
  match l with
  | lnil => lnil
  | lcons a as =>
    if p a then
      lcons a ⟨fun _ => filter p as.get⟩
    else
      filter p as.get

/-- Creates a singleton LazyList -/
def pureLazyList (x : α) : LazyList α :=
  LazyList.lcons x $ Thunk.mk (fun _ => .lnil)

/-- Alias for `pureLazyList` -/
def singleton (x : α) : LazyList α :=
  pureLazyList x

/-- Stack-safe flatten using continuation-passing style -/
def concatCPS (l : LazyList (LazyList α)) : LazyList α :=
  go l id
    where
      go (current : LazyList (LazyList α)) (cont : LazyList α → LazyList α) : LazyList α :=
        match current with
        | .lnil => cont .lnil
        | .lcons x l' =>
          appendToResult x (go l'.get cont)

      appendToResult (xs : LazyList α) (ys : LazyList α) : LazyList α :=
        match xs with
        | .lnil => ys
        | .lcons x xs' =>
          .lcons x (Thunk.mk fun _ => appendToResult xs'.get ys)

/-- Flattens a `LazyList (LazyList α)` into a `LazyList α`  -/
def concat (l : LazyList (LazyList α)) : LazyList α :=
  match l with
  | lnil => lnil
  | lcons lnil l' => concat l'.get
  | lcons (lcons a as) l' => lcons a ⟨ fun _ => (concat (lcons as.get l'))⟩

/-- Round-robin concatenation of lazy enumerations: lazily takes one element from the back of each lazy enumeration in turn
    until there are no more to go, then starts at the head of the enumeration of enumerations. -/
partial def roundRobinConcat (l : LazyList (LazyList α)) : LazyList α :=
  let rec go (current : LazyList (LazyList α)) (queue : List (LazyList α)) : LazyList α :=
    match current with
    | lnil =>
      match queue with
      | [] => lnil
      | q :: qs => go (lcons q ⟨fun _ => lnil⟩) qs
    | lcons lnil rest => go rest.get queue
    | lcons (lcons a as) rest =>
      lcons a ⟨fun _ => go rest.get (queue ++ [as.get])⟩
  go l []

/-- Bind for `LazyList`s is just `concatMap` (same as the list monad) -/
partial def bindLazyList (l : LazyList α) (f : α → LazyList β) : LazyList β :=
  roundRobinConcat (f <$> l)

/-- `Monad` instance for `LazyList` -/
instance : Monad LazyList where
  pure := pureLazyList
  bind := bindLazyList

/-- `Applicative` instance for `LazyList` -/
instance : Applicative LazyList where
  pure := pureLazyList

/-- `Alternative` instance for `LazyList`s, where `xs <|> ys` is just `LazyList` append -/
instance : Alternative LazyList where
  failure := .lnil
  orElse xs f := append xs (f ())

/-- Creates a lazy list by repeatedly applying a function `s` to generate a sequence of elements -/
def lazySeq (s : α → α) (lo : α) (len : Nat) : LazyList α :=
  let rec go (current : α) (numRemainingElements : Nat) : LazyList α :=
    match numRemainingElements with
    | .zero => .lnil
    | .succ remaining' => .lcons current (Thunk.mk $ fun _ => go (s current) remaining')
  go lo len

/-- Creates a lazy sequence from 0 to n built lazily. -/
def range (n : Nat) : LazyList Nat :=
  lazySeq .succ .zero n

end LazyList
