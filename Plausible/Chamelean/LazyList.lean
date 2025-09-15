
-- Adapted from QuickChick source code
-- https://github.com/QuickChick/QuickChick/blob/master/src/LazyList.v

/-- Lazy Lists are implemented by thunking the computation for the tail of a cons-cell. -/
inductive LazyList (α : Type u) where
  | lnil
  | lcons : α → Thunk (LazyList α) → LazyList α
deriving Inhabited

namespace LazyList

/-- Tail-recursive helper for converting `LazyList` to `List`, where `acc` is the list accumulated so far
    - The accumulation prevents stack overflow when converting large `LazyList`s to regular lists -/
def toListAux (acc : List α) : LazyList α → List α
  | .lnil => acc.reverse
  | .lcons x xs => toListAux (x :: acc) xs.get

/-- Converts a `LazyList` to an ordinary list by forcing all the embedded thunks -/
def toList (l : LazyList α) : List α :=
  toListAux [] l

/-- We pretty-print `LazyList`s by converting them to ordinary lists
    (forcing all the thunks) & pretty-printing the resultant list. -/
instance [Repr α] : Repr (LazyList α) where
  reprPrec l _ := repr l.toList

/-- Retrieves a prefix of the `LazyList` (only the thunks in the prefix are evaluated) -/
def take (n : Nat) (l : LazyList α) : LazyList α :=
  match n with
  | .zero => lnil
  | .succ n' =>
    match l with
    | .lnil => lnil
    | .lcons x xs => .lcons x (take n' xs.get)

/-- Stack-safe append, written using continuation-passing style -/
def appendCPS (xs : LazyList α) (ys : LazyList α) : LazyList α :=
  let rec go (current : LazyList α) (cont : LazyList α → LazyList α) : LazyList α :=
    match current with
    | .lnil => cont ys
    | .lcons x xs' =>
      .lcons x (Thunk.mk $ fun _ => go xs'.get cont)
  go xs id

/-- Appends two `LazyLists` together -/
def append (xs : LazyList α) (ys : LazyList α) : LazyList α :=
  appendCPS xs ys

/-- `observe tag i` uses `dbg_trace` to emit a trace of the variable
    associated with `tag` -/
def observe (tag : String) (i : Fin n) : Nat :=
  dbg_trace "{tag}: {i.val}"
  i.val

/-- Maps a function over a LazyList -/
def mapLazyList (f : α → β) (l : LazyList α) : LazyList β :=
  match l with
  | .lnil => .lnil
  | .lcons x xs => .lcons (f x) (Thunk.mk $ fun _ => mapLazyList f xs.get)

/-- `Functor` instance for `LazyList` -/
instance : Functor LazyList where
  map := mapLazyList

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
  concatCPS l

/-- Bind for `LazyList`s is just `concatMap` (same as the list monad) -/
def bindLazyList (l : LazyList α) (f : α → LazyList β) : LazyList β :=
  concat (f <$> l)

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

end LazyList
