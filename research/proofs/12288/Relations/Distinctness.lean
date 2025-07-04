import Relations.Ordering

namespace Relations

-- All constants are distinct
theorem all_distinct : ∀ i j : Fin 8, i ≠ j → Constants.α i ≠ Constants.α j := by
  sorry

end Relations