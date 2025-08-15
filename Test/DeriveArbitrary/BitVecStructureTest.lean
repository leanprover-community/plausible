import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Attr
import Plausible.Testable

open Plausible Gen

set_option guard_msgs.diff true

/-- Dummy `inductive` where a constructor has a dependently-typed argument (`BitVec n`)
    whose index does not appear in the overall type (`DummyInductive`) -/
inductive DummyInductive where
  | FromBitVec : ∀ (n : Nat), BitVec n → String → DummyInductive
  deriving Repr

set_option trace.plausible.deriving.arbitrary true in
/--
trace: [plausible.deriving.arbitrary] ⏎
    [mutual
       def arbitraryDummyInductive✝ : Nat → Plausible.Gen (@DummyInductive✝) :=
         let rec aux_arb (fuel✝ : Nat) : Plausible.Gen (@DummyInductive✝) :=
           match fuel✝ with
           | Nat.zero =>
             Plausible.Gen.oneOfWithDefault
               (do
                 let a✝ ← Plausible.Arbitrary.arbitrary
                 let a✝¹ ← Plausible.Arbitrary.arbitrary
                 let a✝² ← Plausible.Arbitrary.arbitrary
                 return DummyInductive.FromBitVec a✝ a✝¹ a✝²)
               [(do
                   let a✝ ← Plausible.Arbitrary.arbitrary
                   let a✝¹ ← Plausible.Arbitrary.arbitrary
                   let a✝² ← Plausible.Arbitrary.arbitrary
                   return DummyInductive.FromBitVec a✝ a✝¹ a✝²)]
           | fuel'✝ + 1 =>
             Plausible.Gen.frequency
               (do
                 let a✝ ← Plausible.Arbitrary.arbitrary
                 let a✝¹ ← Plausible.Arbitrary.arbitrary
                 let a✝² ← Plausible.Arbitrary.arbitrary
                 return DummyInductive.FromBitVec a✝ a✝¹ a✝²)
               [(1,
                   (do
                     let a✝ ← Plausible.Arbitrary.arbitrary
                     let a✝¹ ← Plausible.Arbitrary.arbitrary
                     let a✝² ← Plausible.Arbitrary.arbitrary
                     return DummyInductive.FromBitVec a✝ a✝¹ a✝²)),
                 ]
         fun fuel✝ => aux_arb fuel✝
     end,
     instance : Plausible.ArbitraryFueled✝ (@DummyInductive✝) :=
       ⟨arbitraryDummyInductive✝⟩]
-/
#guard_msgs in
deriving instance Arbitrary for DummyInductive

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitraryFueled`

/-- info: instArbitraryFueledDummyInductive -/
#guard_msgs in
#synth ArbitraryFueled DummyInductive

/-- info: instArbitraryOfArbitraryFueled -/
#guard_msgs in
#synth Arbitrary DummyInductive

/-- Shrinker for `DummyInductive` -/
def shrinkDummyInductive : DummyInductive → List DummyInductive
  | .FromBitVec n bitVec str =>
    let shrunkenBitVecs := Shrinkable.shrink bitVec
    let shrunkenStrs := Shrinkable.shrink str
    (fun (bv, s) => .FromBitVec n bv s) <$> List.zip shrunkenBitVecs shrunkenStrs

/-- `Shrinkable` instance for `DummyInductive` -/
instance : Shrinkable DummyInductive where
  shrink := shrinkDummyInductive

/-- `SampleableExt` instance for `DummyInductive` -/
instance : SampleableExt DummyInductive :=
  SampleableExt.mkSelfContained Arbitrary.arbitrary

/-- To test whether the derived generator can generate counterexamples,
    we state an (erroneous) property that states that all `BitVec` arguments
    to `DummyInductive.FromBitVec` represent the `Nat` 2, and see
    if the derived generator can refute this property. -/
def BitVecEqualsTwo : DummyInductive → Bool
  | .FromBitVec _ bitVec _ => bitVec.toNat == 2

/-- error: Found a counter-example! -/
#guard_msgs in
#eval Testable.check (∀ ind : DummyInductive, BitVecEqualsTwo ind)
  (cfg := {numInst := 10, maxSize := 5, quiet := true})
