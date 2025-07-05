import Constants.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace PrimeOS12288.Constants

/-- Derived constant that encodes π: α₄ = 1/(2π) -/
noncomputable def α₄ : ℝ := 1 / (2 * π)

/-- Derived constant that encodes π: α₅ = 2π -/
noncomputable def α₅ : ℝ := 2 * π

/-- α₄ is positive -/
theorem α₄_pos : 0 < α₄ := by
  simp only [α₄]
  refine div_pos ?_ ?_
  · norm_num
  · exact mul_pos (by norm_num : (0 : ℝ) < 2) π_pos

/-- α₅ is positive -/
theorem α₅_pos : 0 < α₅ := by
  simp only [α₅]
  exact mul_pos (by norm_num : (0 : ℝ) < 2) π_pos

/-- α₄ times α₅ equals 1 (unity product) -/
theorem α₄_mul_α₅ : α₄ * α₅ = 1 := by
  simp only [α₄, α₅]
  -- (1 / (2 * π)) * (2 * π) = 1
  rw [div_mul]
  simp [mul_comm, π_ne_zero]

/-- α₄ is nonzero -/
theorem α₄_ne_zero : α₄ ≠ 0 :=
  ne_of_gt α₄_pos

/-- α₅ is nonzero -/  
theorem α₅_ne_zero : α₅ ≠ 0 :=
  ne_of_gt α₅_pos

/-- α₄ is less than 1 -/
theorem α₄_lt_one : α₄ < 1 := by
  simp only [α₄]
  -- 1/(2π) < 1 since 2π > 1
  rw [div_lt_one (mul_pos (by norm_num : (0 : ℝ) < 2) π_pos)]
  exact one_lt_two_π

/-- α₅ is greater than 1 -/
theorem α₅_gt_one : 1 < α₅ := by
  simp only [α₅]
  exact one_lt_two_π

/-- Bounds for α₄ -/
theorem α₄_bounds : 1/(2*3.14160) < α₄ ∧ α₄ < 1/(2*3.14159) := by
  simp only [α₄]
  constructor
  · -- Lower bound: 1/(2π) > 1/(2*3.14160)
    -- Since π < 3.14160, we have 2π < 2*3.14160
    -- So 1/(2*3.14160) < 1/(2π)
    apply div_lt_div_of_pos_left
    · norm_num
    · exact mul_pos (by norm_num : (0 : ℝ) < 2) π_pos
    · exact mul_lt_mul_of_pos_left π_upper (by norm_num : (0 : ℝ) < 2)
  · -- Upper bound: 1/(2π) < 1/(2*3.14159)
    -- Since π > 3.14159, we have 2π > 2*3.14159  
    -- So 1/(2π) < 1/(2*3.14159)
    apply div_lt_div_of_pos_left
    · norm_num
    · norm_num
    · exact mul_lt_mul_of_pos_left π_lower (by norm_num : (0 : ℝ) < 2)

/-- Lower bound for α₄ -/
theorem α₄_lower_bound : 1/(2*3.14160) < α₄ := α₄_bounds.1

/-- Upper bound for α₄ -/
theorem α₄_upper_bound : α₄ < 1/(2*3.14159) := α₄_bounds.2

/-- Bounds for α₅ -/
theorem α₅_bounds : 2*3.14159 < α₅ ∧ α₅ < 2*3.14160 := by
  simp only [α₅]
  constructor
  · exact mul_lt_mul_of_pos_left π_lower (by norm_num : (0 : ℝ) < 2)
  · exact mul_lt_mul_of_pos_left π_upper (by norm_num : (0 : ℝ) < 2)

/-- Lower bound for α₅ -/
theorem α₅_lower_bound : 2*3.14159 < α₅ := α₅_bounds.1

/-- Upper bound for α₅ -/
theorem α₅_upper_bound : α₅ < 2*3.14160 := α₅_bounds.2

/-- α₅ > 6 (useful for distinctness) -/
theorem α₅_gt_six : 6 < α₅ := by
  calc 6 < 2 * 3.14159 := by norm_num
  _ < α₅ := α₅_lower_bound

/-- α₄ < 1/6 (useful for distinctness) -/
theorem α₄_lt_one_sixth : α₄ < 1/6 := by
  calc α₄ < 1/(2*3.14159) := α₄_upper_bound
  _ < 1/6 := by norm_num

end PrimeOS12288.Constants