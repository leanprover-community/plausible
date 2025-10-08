import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveChecker

inductive onetrue : Nat → Prop where
| bad1 : False → onetrue n
| bad2 : False → onetrue n
| good : onetrue (Nat.succ Nat.zero)

inductive onetrue' : Nat → Prop where
| bad : False → onetrue' n
| good : onetrue' (Nat.succ Nat.zero)

/-

Ensures that the subenumerator derived from each constructor is used exactly once when
combining them into the top level enumerator for an inductive family.

-/

#guard_msgs(drop info, drop warning) in
#derive_enumerator (fun (n : _) => onetrue n)
#guard_msgs(drop info, drop warning) in
#derive_enumerator (fun (n : _) => onetrue' n)

/--
info: 1
-/
#guard_msgs(info) in
#eval (List.length) <$>
  (runSizedEnum (limit := 10) (EnumSizedSuchThat.enumSizedST (fun t => onetrue t)) 5)

/--
info: 1
-/
#guard_msgs(all) in
#eval ((List.length) <$>
  (runSizedEnum (limit := 10) (EnumSizedSuchThat.enumSizedST (fun t => onetrue' t)) 5))
