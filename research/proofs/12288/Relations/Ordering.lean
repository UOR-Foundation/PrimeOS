import Constants.All
import Properties.Positivity

namespace Relations

-- Field constant ordering
axiom field_ordering : 
  Constants.α₇ < Constants.α₄ ∧ Constants.α₄ < Constants.α₆ ∧ Constants.α₆ < Constants.α₃ ∧ 
  Constants.α₃ < Constants.α₀ ∧ Constants.α₀ < Constants.α₂ ∧ Constants.α₂ < Constants.α₁ ∧ 
  Constants.α₁ < Constants.α₅

theorem α₇_smallest : ∀ i : Fin 8, i ≠ 7 → Constants.α₇ < Constants.α i := by
  sorry

theorem α₅_largest : ∀ i : Fin 8, i ≠ 5 → Constants.α i < Constants.α₅ := by
  sorry

end Relations