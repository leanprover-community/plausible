import Plausible.Chamelean.Enumerators

/-- info: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] -/
#guard_msgs in
#eval (runEnum (α := Nat) 15)

/-- info: [0, 1, 2, 3, 4, 5, 6, 7] -/
#guard_msgs in
#eval (runEnum (α := Nat) 7)

/-- info: [0, 1, 2, 3, 4] -/
#guard_msgs in
#eval (runEnum (α := Fin 5) 5)

/-- info: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] -/
#guard_msgs in
#eval (runEnum (α := Fin 10) 10)


/-- info: [false, true] -/
#guard_msgs in
#eval (runEnum (α := Bool) 10)

/--
info: [(0, false), (0, true), (1, false), (1, true), (2, false), (2, true), (3, false), (3, true), (4, false), (4, true)]
-/
#guard_msgs in
#eval (runEnum (α := Nat × Bool) 5)

/--
info: [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inr false, Sum.inr true]
-/
#guard_msgs in
#eval (runEnum (α := Nat ⊕ Bool) 5)

/-- info: [[], [0], [1], [2], [3], [0, 0], [0, 1], [0, 2], [0, 3], [1, 0]] -/
#guard_msgs in
#eval (runEnum (α := List Nat) 3)

/-- info: [' ', '!', '\"', '#', '$', '%', '&', '\'', '(', ')'] -/
#guard_msgs in
#eval (runEnum (α := Char) 20)
