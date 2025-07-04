import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import PrimeOS12288.Axioms.Golden

namespace PrimeOS12288.Constants

/-- The golden ratio α₂ = (1 + √5) / 2 ≈ 1.618... -/
noncomputable def α₂ : ℝ := Classical.choose golden_exists

/-- α₂ satisfies the golden ratio equation -/
theorem α₂_golden : α₂^2 = α₂ + 1 := by
  have h := Classical.choose_spec golden_exists
  exact h.2

/-- α₂ is positive -/
theorem α₂_pos : 0 < α₂ := by
  have h := Classical.choose_spec golden_exists
  exact h.1

/-- α₂ equals (1 + √5) / 2 -/
theorem α₂_formula : α₂ = (1 + Real.sqrt 5) / 2 := by
  -- We need to show α₂ is the unique positive solution to x² = x + 1
  -- First, verify that (1 + √5)/2 satisfies the equation
  have h1 : ((1 + Real.sqrt 5) / 2)^2 = (1 + Real.sqrt 5) / 2 + 1 := by
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    ring
  -- Show (1 + √5)/2 is positive
  have h2 : 0 < (1 + Real.sqrt 5) / 2 := by
    apply div_pos
    apply add_pos_of_pos_of_nonneg
    · norm_num
    · exact Real.sqrt_nonneg 5
    · norm_num
  -- Now show uniqueness: if x > 0 and x² = x + 1, then x = (1 + √5)/2
  have unique : ∀ x : ℝ, 0 < x → x^2 = x + 1 → x = (1 + Real.sqrt 5) / 2 := by
    intro x hpos heq
    -- x² = x + 1 iff x² - x - 1 = 0
    have : x^2 - x - 1 = 0 := by linarith
    -- Using quadratic formula: x = (1 ± √5)/2
    -- Since x > 0 and √5 > 2, only (1 + √5)/2 is positive
    have : x = (1 + Real.sqrt 5) / 2 ∨ x = (1 - Real.sqrt 5) / 2 := by
      have h := Real.quadratic_eq_zero_iff (a := 1) (b := -1) (c := -1) (by norm_num : (1 : ℝ) ≠ 0)
      rw [h] at this
      simp at this
      convert this
      · ring
      · ring
      · norm_num
    cases this with
    | inl h => exact h
    | inr h => 
      -- Show (1 - √5)/2 < 0, contradicting x > 0
      exfalso
      rw [h] at hpos
      have : Real.sqrt 5 > 2 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
        apply Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (4 : ℝ) < 5)
      linarith
  -- Apply uniqueness to α₂
  exact unique α₂ α₂_pos α₂_golden

/-- α₂ is greater than 1 -/
theorem α₂_gt_one : 1 < α₂ := by
  rw [α₂_formula]
  have : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  linarith

/-- α₂ is less than 2 -/
theorem α₂_lt_two : α₂ < 2 := by
  rw [α₂_formula]
  have : Real.sqrt 5 < 3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
    apply Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (5 : ℝ) < 9)
  linarith

/-- Approximation of α₂ -/
theorem α₂_approx : |α₂ - 1.618| < 0.001 := by
  rw [α₂_formula]
  -- We need to show |(1 + √5)/2 - 1.618| < 0.001
  -- This is equivalent to showing 1.617 < (1 + √5)/2 < 1.619
  -- Which requires 2.234 < √5 < 2.238
  
  -- First establish bounds on √5
  have sqrt5_lower : 2.234 < Real.sqrt 5 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.234)]
    apply Real.sqrt_lt_sqrt
    · norm_num
    · norm_num
  
  have sqrt5_upper : Real.sqrt 5 < 2.238 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.238)]
    apply Real.sqrt_lt_sqrt
    · norm_num
    · norm_num
  
  -- Now show the bounds on α₂
  have lower_bound : 1.617 < (1 + Real.sqrt 5) / 2 := by
    calc (1 + Real.sqrt 5) / 2 
        > (1 + 2.234) / 2 := by linarith [sqrt5_lower]
      _ = 3.234 / 2 := by ring
      _ = 1.617 := by norm_num
  
  have upper_bound : (1 + Real.sqrt 5) / 2 < 1.619 := by
    calc (1 + Real.sqrt 5) / 2 
        < (1 + 2.238) / 2 := by linarith [sqrt5_upper]
      _ = 3.238 / 2 := by ring
      _ = 1.619 := by norm_num
  
  -- Convert to absolute value form
  rw [abs_sub_lt_iff]
  constructor
  · linarith [lower_bound]
  · linarith [upper_bound]

/-- α₂ - 1 = 1/α₂ -/
theorem α₂_reciprocal : α₂ - 1 = 1 / α₂ := by
  have h1 : α₂^2 = α₂ + 1 := α₂_golden
  have h2 : α₂ ≠ 0 := ne_of_gt α₂_pos
  -- From α₂² = α₂ + 1, we get α₂² - α₂ = 1
  -- So α₂(α₂ - 1) = 1
  -- Therefore α₂ - 1 = 1/α₂
  have : α₂ * (α₂ - 1) = 1 := by
    rw [mul_sub, ← sq]
    linarith
  rw [← div_eq_iff h2]
  exact this.symm

end PrimeOS12288.Constants