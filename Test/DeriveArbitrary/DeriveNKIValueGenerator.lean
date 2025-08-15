import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Attr
import Plausible.Testable

open Plausible Gen

set_option guard_msgs.diff true

/-- A datatype representing values in the NKI language, adapted from
    https://github.com/leanprover/KLR/blob/main/KLR/NKI/Basic.lean -/
inductive Value where
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
       def arbitraryValue✝ : Nat → Plausible.Gen (@Value✝) :=
         let rec aux_arb (fuel✝ : Nat) : Plausible.Gen (@Value✝) :=
           match fuel✝ with
           | Nat.zero =>
             Plausible.Gen.oneOfWithDefault (pure Value.none)
               [(pure Value.none),
                 (do
                   let a✝ ← Plausible.Arbitrary.arbitrary
                   return Value.bool a✝),
                 (do
                   let a✝¹ ← Plausible.Arbitrary.arbitrary
                   return Value.int a✝¹),
                 (do
                   let a✝² ← Plausible.Arbitrary.arbitrary
                   return Value.string a✝²),
                 (pure Value.ellipsis),
                 (do
                   let a✝³ ← Plausible.Arbitrary.arbitrary
                   let a✝⁴ ← Plausible.Arbitrary.arbitrary
                   return Value.tensor a✝³ a✝⁴)]
           | fuel'✝ + 1 =>
             Plausible.Gen.frequency (pure Value.none)
               [(1, (pure Value.none)),
                 (1,
                   (do
                     let a✝ ← Plausible.Arbitrary.arbitrary
                     return Value.bool a✝)),
                 (1,
                   (do
                     let a✝¹ ← Plausible.Arbitrary.arbitrary
                     return Value.int a✝¹)),
                 (1,
                   (do
                     let a✝² ← Plausible.Arbitrary.arbitrary
                     return Value.string a✝²)),
                 (1, (pure Value.ellipsis)),
                 (1,
                   (do
                     let a✝³ ← Plausible.Arbitrary.arbitrary
                     let a✝⁴ ← Plausible.Arbitrary.arbitrary
                     return Value.tensor a✝³ a✝⁴)),
                 ]
         fun fuel✝ => aux_arb fuel✝
     end,
     instance : Plausible.ArbitraryFueled✝ (@Value✝) :=
       ⟨arbitraryValue✝⟩]
-/
#guard_msgs in
deriving instance Arbitrary for Value

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitraryFueled`

/-- info: instArbitraryFueledValue -/
#guard_msgs in
#synth ArbitraryFueled Value

/-- info: instArbitraryOfArbitraryFueled -/
#guard_msgs in
#synth Arbitrary Value

/-- `Shrinkable` instance for `Value`s which recursively
    shrinks each argument to a constructor -/
instance : Shrinkable Value where
  shrink (v : Value) :=
    match v with
    | .none | .ellipsis => []
    | .bool b => .bool <$> Shrinkable.shrink b
    | .int n => .int <$> Shrinkable.shrink n
    | .string s => .string <$> Shrinkable.shrink s
    | .tensor shape dtype =>
      let shrunkenShapes := Shrinkable.shrink shape
      let shrunkenDtypes := Shrinkable.shrink dtype
      (Function.uncurry .tensor) <$> List.zip shrunkenShapes shrunkenDtypes

/-- `SampleableExt` instance for `Value` -/
instance : SampleableExt Value :=
  SampleableExt.mkSelfContained Arbitrary.arbitrary

-- To test whether the derived generator can generate counterexamples,
-- we state an (erroneous) property that states that all `Value`s are `Bool`s
-- and see if the generator can refute this property.

/-- Determines whether a `Value` is a `Bool` -/
def isBool (v : Value) : Bool :=
  match v with
  | .bool _ => true
  | _ => false

/-- error: Found a counter-example! -/
#guard_msgs in
#eval Testable.check (∀ v : Value, isBool v)
  (cfg := {numInst := 10, maxSize := 5, quiet := true})
