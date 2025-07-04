-- Tribonacci growth principle
axiom tribonacci_exists : ∃ (t : ℝ), t > 1 ∧ t^3 = t^2 + t + 1

-- Uniqueness of the tribonacci constant
axiom tribonacci_unique : ∃! (t : ℝ), t > 1 ∧ t^3 = t^2 + t + 1

-- Numerical bounds for the tribonacci constant
axiom tribonacci_bounds : ∃ (t : ℝ), 1.83928 < t ∧ t < 1.83929 ∧ t^3 = t^2 + t + 1