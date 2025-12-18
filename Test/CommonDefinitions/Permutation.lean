/-- Inductive relation specifying what it means for two lists to be permutations of each other.
    - Adapted from https://softwarefoundations.cis.upenn.edu/vfa-1.4/Perm.html -/
inductive Permutation : List Nat → List Nat → Prop where
  | PermNil : Permutation [] []
  | PermSkip : ∀ (x : Nat) (l l' : List Nat),
               Permutation l l' →
               Permutation (x :: l) (x :: l')
  | PermSwap : ∀ (x y : Nat) (l : List Nat),
              Permutation (y :: x :: l) (x :: y :: l)
  | PermTrans : ∀ (l l' l'' : List Nat),
                Permutation l l' →
                Permutation l' l'' →
                Permutation l l''
