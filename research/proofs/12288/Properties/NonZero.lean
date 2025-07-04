import Properties.Positivity

namespace Properties

-- All field constants are nonzero
theorem all_nonzero : ∀ i : Fin 8, Constants.α i ≠ 0 := by
  intro i
  have h := all_positive i
  linarith

end Properties