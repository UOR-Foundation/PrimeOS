/-
  Properties.Equations - Collect all defining equations
  
  This module collects all the defining equations for the field constants
  into a single theorem for easy reference.
-/

import Constants.All

namespace Properties

open Constants

-- Collect all defining equations
theorem defining_equations :
  α₀ = 1 ∧
  α₁^3 = α₁^2 + α₁ + 1 ∧
  α₂^2 = α₂ + 1 ∧
  α₃ = 1/2 ∧
  α₄ = 1/(2*π) ∧
  α₅ = 2*π ∧
  α₆ = 0.19961197478400415 ∧
  α₇ = 0.014134725141734695 := by
  exact ⟨α₀_eq_one, α₁_equation, α₂_equation, α₃_eq_half,
         rfl, rfl, α₆_value, α₇_value⟩

end Properties