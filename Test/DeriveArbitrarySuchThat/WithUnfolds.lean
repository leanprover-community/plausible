import Plausible.Chamelean.DeriveConstrainedProducer

structure TypeBox where
  ty : Type

instance : Inhabited TypeBox := ⟨⟨Unit⟩⟩

abbrev NatFoo : TypeBox where
  ty := Nat

opaque SomeFoo : TypeBox

def five := 5

--
inductive TypeBoxPred : Nat → Prop where
| someRefl {x : NatFoo.ty} : x = x → 0 = x → 5 = 5 → TypeBoxPred 5

inductive TypeBoxPredS : String → Prop where
| someRefl {x : NatFoo.ty} y : x = x → y = "foo" → TypeBoxPredS "foo"

inductive TypeBoxPred' : Nat → Prop where
| someRefl {x : SomeFoo.ty} : x = x → TypeBoxPred' five

instance (α : Type) (n : Nat) [OfNat α n] : ArbitrarySizedSuchThat α (fun x => OfNat.ofNat n = x) where
  arbitrarySizedST _ := return OfNat.ofNat n

/--
error: failed to synthesize
  ArbitrarySizedSuchThat Nat fun x => OfNat.ofNat 0 = x

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
#guard_msgs(all) in
#check ArbitrarySizedSuchThat.arbitrarySizedST (fun (x : Nat) => Eq (OfNat.ofNat 0) x)


/--
error: failed to synthesize
  ArbitrarySizedSuchThat NatFoo.ty fun x => OfNat.ofNat 0 = x

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
error: failed to synthesize
  ArbitrarySizedSuchThat NatFoo.ty fun x => OfNat.ofNat 0 = x

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs(error, drop info, drop warning) in
derive_generator ∃ (n : Nat), TypeBoxPred n

#guard_msgs(error, drop info, drop warning) in
derive_generator ∃ (n : _), TypeBoxPredS n

#guard_msgs(drop error, drop warning, drop info) in
derive_generator ∃ (n : Nat), TypeBoxPred' n
