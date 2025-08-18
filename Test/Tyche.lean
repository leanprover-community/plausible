import Plausible

theorem add_comm : ∀ (a b : Nat), a < b -> a + b = b + a := by
  plausible (config := {detailedReportingWithName := "add_comm"})
