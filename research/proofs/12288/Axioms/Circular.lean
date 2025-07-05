import Mathlib.Data.Real.Basic

namespace PrimeOS12288.Axioms

-- The circular constant π exists with certain properties and bounds
axiom pi_exists : ∃ (π : ℝ), π > 0 ∧ 
  (∀ (r : ℝ), r > 0 → ∃ (c : ℝ), c = 2 * π * r) ∧ -- circumference of circle with radius r
  3.14159 < π ∧ π < 3.14160 -- numerical bounds

end PrimeOS12288.Axioms