import Plausible

open Plausible

namespace ShrinkableMutualTests

-- Mutually recursive types
mutual
  inductive Even where
    | zero : Even
    | succOdd : Odd → Even

  inductive Odd where
    | succEven : Even → Odd
end

deriving instance Repr, Shrinkable for Even, Odd

-- `deriving instance ... for` on a non-mutual recursive type
inductive Expr where
  | Lit : Nat → Expr
  | Add : Expr → Expr → Expr
  | Neg : Expr → Expr
  deriving Repr

deriving instance Shrinkable for Expr

/-- info: [] -/
#guard_msgs in
#eval Shrinkable.shrink (Even.succOdd (Odd.succEven Even.zero))

/--
info: [ShrinkableMutualTests.Expr.Lit 3,
 ShrinkableMutualTests.Expr.Neg (ShrinkableMutualTests.Expr.Lit 1),
 ShrinkableMutualTests.Expr.Add
   (ShrinkableMutualTests.Expr.Lit 1)
   (ShrinkableMutualTests.Expr.Neg (ShrinkableMutualTests.Expr.Lit 1)),
 ShrinkableMutualTests.Expr.Add
   (ShrinkableMutualTests.Expr.Lit 0)
   (ShrinkableMutualTests.Expr.Neg (ShrinkableMutualTests.Expr.Lit 1)),
 ShrinkableMutualTests.Expr.Add (ShrinkableMutualTests.Expr.Lit 3) (ShrinkableMutualTests.Expr.Lit 1),
 ShrinkableMutualTests.Expr.Add
   (ShrinkableMutualTests.Expr.Lit 3)
   (ShrinkableMutualTests.Expr.Neg (ShrinkableMutualTests.Expr.Lit 0))]
-/
#guard_msgs in
#eval Shrinkable.shrink (Expr.Add (Expr.Lit 3) (Expr.Neg (Expr.Lit 1)))

end ShrinkableMutualTests
