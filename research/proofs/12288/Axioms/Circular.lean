-- The circular constant π
axiom pi_exists : ∃ (π : ℝ), π > 0 ∧ 
  ∀ (r : ℝ), r > 0 → (circumference of circle with radius r) = 2 * π * r

-- Numerical bounds (since we can't construct π)
axiom pi_bounds : ∃ (π : ℝ), 3.14159 < π ∧ π < 3.14160