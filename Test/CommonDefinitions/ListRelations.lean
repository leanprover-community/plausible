
/-- List membership expressed as an inductive relation:
   `InList x l` means `x ∈ l`. -/
inductive InList : Nat → List Nat → Prop where
| Here : ∀ x l, InList x (x::l)
| There : ∀ x y l, InList x l → InList x (y::l)

-- Thanks to Chase Johnson for providing the example inductive relations in this file!

/-- Example inductive relation involving pattern-matching on just one input -/
inductive MinOk : List Nat → List Nat → Prop where
| MO_empty : MinOk [] []
| MO_present : ∀ x l l',
    MinOk l l' →
    InList x l →
    MinOk l (x::l')

/-- Example inductive relation involving simultaneous pattern-matching on multiple inputs -/
inductive MinEx : Nat → List Nat → List Nat → Prop where
| ME_empty : MinEx .zero [] []
| ME_present : ∀ x l n l',
    MinEx n l l' →
    InList x l →
    MinEx (Nat.succ n) l (x::l')

/-- Example inductive relation involving a non-trivial function call
    (`l'' = [x] + l'`)  in the conclusion -/
inductive MinEx2 : Nat → List Nat → List Nat → Prop where
| ME_empty : MinEx2 .zero [] []
| ME_present : ∀ x l l',
    MinEx2 x l l' →
    MinEx2 (Nat.succ x) l ([x] ++ l')

/-- Example inductive relation involving a non-trivial function call
    (e.g. `[x] ++ l`) in the conclusion -/
inductive MinEx3 : Nat → List Nat → List Nat → Prop where
| ME_empty : MinEx3 .zero [] []
| ME_present : ∀ x l,
    MinEx3 x l ([x] ++ l)
