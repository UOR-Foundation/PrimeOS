import Mathlib.Data.Real.Basic

namespace PrimeOS12288.Axioms

-- The existence of multiplicative identity
axiom unity_exists : ∃ (α : ℝ), α = 1 ∧ ∀ x : ℝ, α * x = x ∧ x * α = x

end PrimeOS12288.Axioms