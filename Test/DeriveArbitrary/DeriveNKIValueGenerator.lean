import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Attr
import Plausible.Testable

open Plausible Gen

set_option guard_msgs.diff true

/-- A datatype representing values in the NKI language, adapted from
    https://github.com/leanprover/KLR/blob/main/KLR/NKI/Basic.lean -/
inductive NKIValue where
  | none
  | bool (value : Bool)
  | int (value : Int)
  | string (value : String)
  | ellipsis
  | tensor (shape : List Nat) (dtype : String)
  deriving Repr

set_option trace.plausible.deriving.arbitrary true in
/--
trace: [plausible.deriving.arbitrary] ⏎
    [mutual
       def arbitraryNKIValue✝ : Nat → Plausible.Gen (@NKIValue✝) :=
         let rec aux_arb (fuel✝ : Nat) : Plausible.Gen (@NKIValue✝) :=
           match fuel✝ with
           | Nat.zero =>
             Plausible.Gen.oneOfWithDefault (pure NKIValue.none)
               [(pure NKIValue.none),
                 (do
                   let a✝ ← Plausible.Arbitrary.arbitrary
                   return NKIValue.bool a✝),
                 (do
                   let a✝¹ ← Plausible.Arbitrary.arbitrary
                   return NKIValue.int a✝¹),
                 (do
                   let a✝² ← Plausible.Arbitrary.arbitrary
                   return NKIValue.string a✝²),
                 (pure NKIValue.ellipsis),
                 (do
                   let a✝³ ← Plausible.Arbitrary.arbitrary
                   let a✝⁴ ← Plausible.Arbitrary.arbitrary
                   return NKIValue.tensor a✝³ a✝⁴)]
           | fuel'✝ + 1 =>
             Plausible.Gen.frequency (pure NKIValue.none)
               [(1, (pure NKIValue.none)),
                 (1,
                   (do
                     let a✝ ← Plausible.Arbitrary.arbitrary
                     return NKIValue.bool a✝)),
                 (1,
                   (do
                     let a✝¹ ← Plausible.Arbitrary.arbitrary
                     return NKIValue.int a✝¹)),
                 (1,
                   (do
                     let a✝² ← Plausible.Arbitrary.arbitrary
                     return NKIValue.string a✝²)),
                 (1, (pure NKIValue.ellipsis)),
                 (1,
                   (do
                     let a✝³ ← Plausible.Arbitrary.arbitrary
                     let a✝⁴ ← Plausible.Arbitrary.arbitrary
                     return NKIValue.tensor a✝³ a✝⁴)),
                 ]
         fun fuel✝ => aux_arb fuel✝
     end,
     instance : Plausible.ArbitraryFueled✝ (@NKIValue✝) :=
       ⟨arbitraryNKIValue✝⟩]
-/
#guard_msgs in
deriving instance Arbitrary for NKIValue

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitraryFueled`

/-- info: instArbitraryFueledNKIValue -/
#guard_msgs in
#synth ArbitraryFueled NKIValue

/-- info: instArbitraryOfArbitraryFueled -/
#guard_msgs in
#synth Arbitrary NKIValue

/-- `Shrinkable` instance for `NKIValue`s which recursively
    shrinks each argument to a constructor -/
instance : Shrinkable NKIValue where
  shrink (v : NKIValue) :=
    match v with
    | .none | .ellipsis => []
    | .bool b => .bool <$> Shrinkable.shrink b
    | .int n => .int <$> Shrinkable.shrink n
    | .string s => .string <$> Shrinkable.shrink s
    | .tensor shape dtype =>
      let shrunkenShapes := Shrinkable.shrink shape
      let shrunkenDtypes := Shrinkable.shrink dtype
      (Function.uncurry .tensor) <$> List.zip shrunkenShapes shrunkenDtypes

/-- `SampleableExt` instance for `NKIValue` -/
instance : SampleableExt NKIValue :=
  SampleableExt.mkSelfContained Arbitrary.arbitrary

-- To test whether the derived generator can generate counterexamples,
-- we state an (erroneous) property that states that all `NKIValue`s are `Bool`s
-- and see if the generator can refute this property.

/-- Determines whether a `NKIValue` is a `Bool` -/
def isBool (v : NKIValue) : Bool :=
  match v with
  | .bool _ => true
  | _ => false

/-- error: Found a counter-example! -/
#guard_msgs in
#eval Testable.check (∀ v : NKIValue, isBool v)
  (cfg := {numInst := 10, maxSize := 5, quiet := true})
