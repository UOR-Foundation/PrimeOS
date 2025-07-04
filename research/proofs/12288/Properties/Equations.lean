import Constants.All

namespace Properties

-- Collect all defining equations
theorem defining_equations :
  Constants.α₀ = 1 ∧
  Constants.α₁^3 = Constants.α₁^2 + Constants.α₁ + 1 ∧
  Constants.α₂^2 = Constants.α₂ + 1 ∧
  Constants.α₃ = 1/2 ∧
  Constants.α₄ = 1/(2*Real.pi) ∧
  Constants.α₅ = 2*Real.pi ∧
  Constants.α₆ = 0.19961197478400415 ∧
  Constants.α₇ = 0.014134725141734695 := by
  sorry

end Properties