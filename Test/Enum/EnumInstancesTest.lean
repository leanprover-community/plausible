/-
Copyright (c) 2026 AWS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AWS
-/
import Plausible.Chamelean.Enumerators

#guard_msgs(error, drop info) in
#eval (runEnum (α := Nat) 15)

#guard_msgs(error, drop info) in
#eval (runEnum (α := Nat) 7)

#guard_msgs(error, drop info) in
#eval (runEnum (α := Fin 5) 5)

#guard_msgs(error, drop info) in
#eval (runEnum (α := Fin 10) 10)



#guard_msgs(error, drop info) in
#eval (runEnum (α := Bool) 10)

#guard_msgs(error, drop info) in
#eval (runEnum (α := Nat × Bool) 5)

#guard_msgs(error, drop info) in
#eval (runEnum (α := Nat ⊕ Bool) 5)

#guard_msgs(error, drop info) in
#eval (runEnum (α := List Nat) 3)

#guard_msgs(error, drop info) in
#eval (runEnum (α := Char) 20)
