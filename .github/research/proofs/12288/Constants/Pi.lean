import Axioms.Circular
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace PrimeOS12288.Constants

open PrimeOS12288.Axioms

/-- The circular constant -/
noncomputable def π : ℝ := Classical.choose pi_exists

/-- The specification of π -/
theorem π_spec : π > 0 ∧ 
  (∀ (r : ℝ), r > 0 → ∃ (c : ℝ), c = 2 * π * r) ∧
  3.14159 < π ∧ π < 3.14160 :=
  Classical.choose_spec pi_exists

/-- π is positive -/
theorem π_pos : 0 < π := π_spec.1

/-- π satisfies the circle circumference property -/
theorem π_circle : ∀ (r : ℝ), r > 0 → ∃ (c : ℝ), c = 2 * π * r :=
  π_spec.2.1

/-- π lower bound -/
theorem π_lower : 3.14159 < π := π_spec.2.2.1

/-- π upper bound -/
theorem π_upper : π < 3.14160 := π_spec.2.2.2

/-- π/2 is positive -/
theorem π_div_two_pos : 0 < π / 2 := by
  apply div_pos π_pos
  exact two_pos

/-- π is nonzero -/
theorem π_ne_zero : π ≠ 0 :=
  ne_of_gt π_pos

/-- π is greater than 3 -/
theorem three_lt_π : 3 < π := by
  calc 3 < 3.14159 := by norm_num
  _ < π := π_lower

/-- π is greater than 1 -/
theorem one_lt_π : 1 < π := by
  calc 1 < 3 := by norm_num
  _ < π := three_lt_π

/-- 2π is greater than 1 -/
theorem one_lt_two_π : 1 < 2 * π := by
  calc 1 < 2 * 1 := by norm_num
  _ < 2 * π := by exact mul_lt_mul_of_pos_left one_lt_π (by norm_num : (0 : ℝ) < 2)

end PrimeOS12288.Constants