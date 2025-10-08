import Plausible.Chamelean.DeriveConstrainedProducer

structure TypeBox where
  ty : Type

instance : Inhabited TypeBox := ⟨⟨Unit⟩⟩

abbrev NatFoo : TypeBox where
  ty := Nat

opaque SomeFoo : TypeBox

def five := 5

inductive TypeBoxPred : Nat → Prop where
| someRefl {x : NatFoo.ty} : x = x → TypeBoxPred five

inductive TypeBoxPred' : Nat → Prop where
| someRefl {x : SomeFoo.ty} : x = x → TypeBoxPred' five

#guard_msgs(error, drop warning, drop info) in
#derive_generator (fun (n : Nat) => TypeBoxPred n)

/-- error: exprToHypothesisExpr: unable to convert SomeFoo.1 to a HypothesisExpr, must be a constructor or an inductive applied to arguments. -/
#guard_msgs(error, drop warning, drop info) in
#derive_generator (fun (n : Nat) => TypeBoxPred' n)
