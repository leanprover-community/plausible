
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveConstrainedProducer
import Test.DeriveArbitrarySuchThat.SimultaneousMatchingTests

open DecOpt

set_option guard_msgs.diff true

/-- `LessThanEq n m` is an inductive relation that means `n <= m`.
    Adapted from https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html -/
inductive LessThanEq : Nat → Nat → Prop where
  | Refl : ∀ n, LessThanEq n n
  | Succ : ∀ n m, LessThanEq n m → LessThanEq n (.succ m)

/-- `NatChain a b` means there is an ascending chain of `Nat`s under the usual `<=` order,
    where `a` and `b` are the start and end of the chain respectively.
    This is an inductive relation with multiple existentially quantified variables
    (note how `x` and `y` don't appear in the conclusion of the `ChainExists` constructor).

    We use `LessThanEq` (defined above) instead of the `LE.le` operator from the Lean standard library,
    since `LE` is defined as a typeclass and not as an inductive relation. -/
inductive NatChain (a b : Nat) : Prop where
| ChainExists : ∀ (x y : Nat),
    (LessThanEq a x) →
    (LessThanEq x y) ->
    (LessThanEq y b) →
    NatChain a b

/--
info: Try this enumerator: instance : EnumSizedSuchThat Nat (fun x_1 => LessThanEq a_1 x_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (a_1 : Nat) : OptionT Enumerator Nat :=
      match size with
      | Nat.zero => EnumeratorCombinators.enumerate [return a_1]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [return a_1, do
            let m ← aux_enum initSize size' a_1;
            return Nat.succ m]
    fun size => aux_enum size size a_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (x : Nat) => LessThanEq a x)

/--
info: Try this enumerator: instance : EnumSizedSuchThat Nat (fun y_1 => LessThanEq x_1 y_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (x_1 : Nat) : OptionT Enumerator Nat :=
      match size with
      | Nat.zero => EnumeratorCombinators.enumerate [return x_1]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [return x_1, do
            let m ← aux_enum initSize size' x_1;
            return Nat.succ m]
    fun size => aux_enum size size x_1
-/
#guard_msgs(info, drop warning) in
#derive_enumerator (fun (y : Nat) => LessThanEq x y)

/--
info: Try this checker: instance : DecOpt (LessThanEq n_1 m_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (n_1 : Nat) (m_1 : Nat) : Option Bool :=
      match size with
      | Nat.zero => DecOpt.checkerBacktrack [fun _ => DecOpt.decOpt (BEq.beq n_1 m_1) initSize]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ => DecOpt.decOpt (BEq.beq n_1 m_1) initSize, fun _ =>
            match m_1 with
            | Nat.succ m => aux_dec initSize size' n_1 m
            | _ => Option.some Bool.false]
    fun size => aux_dec size size n_1 m_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (LessThanEq n m)

/--
info: Try this checker: instance : DecOpt (NatChain a_1 b_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (a_1 : Nat) (b_1 : Nat) : Option Bool :=
      match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            EnumeratorCombinators.enumeratingOpt (EnumSizedSuchThat.enumSizedST (fun x => LessThanEq a_1 x) initSize)
              (fun x =>
                EnumeratorCombinators.enumeratingOpt (EnumSizedSuchThat.enumSizedST (fun y => LessThanEq x y) initSize)
                  (fun y => DecOpt.decOpt (LessThanEq y b_1) initSize) (min 2 initSize))
              (min 2 initSize)]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            EnumeratorCombinators.enumeratingOpt (EnumSizedSuchThat.enumSizedST (fun x => LessThanEq a_1 x) initSize)
              (fun x =>
                EnumeratorCombinators.enumeratingOpt (EnumSizedSuchThat.enumSizedST (fun y => LessThanEq x y) initSize)
                  (fun y => DecOpt.decOpt (LessThanEq y b_1) initSize) (min 2 initSize))
              (min 2 initSize),
            ]
    fun size => aux_dec size size a_1 b_1
-/
#guard_msgs(info, drop warning) in
#derive_checker (NatChain a b)
