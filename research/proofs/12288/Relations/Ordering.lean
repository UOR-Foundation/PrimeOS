import PrimeOS12288.Constants.All
import PrimeOS12288.Properties.Positivity
import Mathlib.Tactic.Norm.Num
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace PrimeOS12288

open Real Constants

/-!
# Ordering Relations Between Field Constants

This file establishes the complete ordering of the field constants:
α₇ < α₄ < α₆ < α₃ < α₀ < α₂ < α₁ < α₅

We prove:
1. The complete ordering chain
2. α₇ is the smallest constant
3. α₅ is the largest constant
-/

/-- Helper lemma: α₇ < α₄ -/
lemma α₇_lt_α₄ : α₇ < α₄ := by
  -- α₇ = 0.014134725141734695
  -- α₄ = 1/(2π) ≈ 0.159...
  -- We need to show α₇ < 1/(2π)
  -- This is equivalent to 2π * α₇ < 1
  rw [α₄_eq]
  rw [div_gt_iff (mul_pos two_pos Real.pi_pos)]
  simp [α₇, α₇_rational]
  norm_num
  -- We need 2π * (14134725141734695 / 1000000000000000000) < 1
  -- Which is 2π * 14134725141734695 < 1000000000000000000
  -- Since π < 4, we have 2π < 8
  -- So 2π * 14134725141734695 < 8 * 14134725141734695 = 113077801133477560
  have h1 : Real.pi < 4 := Real.pi_lt_four
  have h2 : 2 * Real.pi < 8 := by linarith
  have h3 : (2 * Real.pi) * (14134725141734695 : ℝ) < 8 * 14134725141734695 := by
    apply mul_lt_mul_of_pos_right h2
    norm_num
  have h4 : 8 * 14134725141734695 < 1000000000000000000 := by norm_num
  linarith

/-- Helper lemma: α₄ < α₆ -/
lemma α₄_lt_α₆ : α₄ < α₆ := by
  -- α₄ = 1/(2π) ≈ 0.159...
  -- α₆ = 0.19961197478400415
  -- We need to show 1/(2π) < 0.19961197478400415
  -- This is equivalent to 1 < 2π * 0.19961197478400415
  rw [α₄_eq]
  rw [div_lt_iff (mul_pos two_pos Real.pi_pos)]
  simp [α₆, α₆_rational]
  norm_num
  -- We need 1 < 2π * (19961197478400415 / 100000000000000000)
  -- Which is 100000000000000000 < 2π * 19961197478400415
  -- Since π > 3, we have 2π > 6
  -- So 2π * 19961197478400415 > 6 * 19961197478400415 = 119767184870402490
  have h1 : 3 < Real.pi := Real.three_lt_pi
  have h2 : 6 < 2 * Real.pi := by linarith
  have h3 : 6 * 19961197478400415 < (2 * Real.pi) * 19961197478400415 := by
    apply mul_lt_mul_of_pos_right h2
    norm_num
  have h4 : 100000000000000000 < 6 * 19961197478400415 := by norm_num
  linarith

/-- Helper lemma: α₆ < α₃ -/
lemma α₆_lt_α₃ : α₆ < α₃ := by
  -- α₆ = 0.19961197478400415
  -- α₃ = 1/2 = 0.5
  simp [α₆, α₆_rational, α₃]
  norm_num

/-- Helper lemma: α₃ < α₀ -/
lemma α₃_lt_α₀ : α₃ < α₀ := by
  -- α₃ = 1/2 = 0.5
  -- α₀ = 1
  simp [α₃, α₀]
  norm_num

/-- Helper lemma: α₀ < α₂ -/
lemma α₀_lt_α₂ : α₀ < α₂ := by
  -- α₀ = 1
  -- α₂ = golden ratio > 1
  simp [α₀]
  exact α₂_gt_one

/-- Helper lemma: α₂ < α₁ -/
lemma α₂_lt_α₁ : α₂ < α₁ := by
  -- α₂ = golden ratio ≈ 1.618
  -- α₁ = tribonacci ≈ 1.839
  -- From the bounds we know:
  -- α₁ > 1.83928 (by α₁_bounds)
  have h1 := α₁_bounds.1  -- 1.83928 < α₁
  have h2 := α₂_lt_two    -- α₂ < 2
  -- We need a more precise bound for α₂
  -- From α₂ = (1 + √5)/2 and √5 < 2.24 (since 2.24² = 5.0176 > 5)
  have sqrt5_bound : Real.sqrt 5 < 2.24 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.24)]
    apply Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (5 : ℝ) < 5.0176)
  have α₂_bound : α₂ < 1.62 := by
    rw [α₂_formula]
    calc α₂ = (1 + Real.sqrt 5) / 2 := rfl
    _ < (1 + 2.24) / 2 := by apply div_lt_div_of_lt_left; linarith; norm_num; linarith
    _ = 3.24 / 2 := by norm_num
    _ = 1.62 := by norm_num
  linarith

/-- Helper lemma: α₁ < α₅ -/
lemma α₁_lt_α₅ : α₁ < α₅ := by
  -- α₁ = tribonacci ≈ 1.839
  -- α₅ = 2π ≈ 6.283
  have h1 := α₁_lt_two  -- α₁ < 2
  have h2 : 2 < α₅ := by
    simp [α₅]
    have : 1 < Real.pi := Real.one_lt_pi
    linarith
  linarith

/-- The complete ordering chain of field constants -/
theorem field_ordering :
    α₇ < α₄ ∧ α₄ < α₆ ∧ α₆ < α₃ ∧ α₃ < α₀ ∧ α₀ < α₂ ∧ α₂ < α₁ ∧ α₁ < α₅ := by
  exact ⟨α₇_lt_α₄, α₄_lt_α₆, α₆_lt_α₃, α₃_lt_α₀, α₀_lt_α₂, α₂_lt_α₁, α₁_lt_α₅⟩

/-- α₇ is the smallest field constant -/
theorem α₇_smallest (i : Fin 8) (hi : i ≠ 7) : α₇ < fieldConstant i := by
  fin_cases i <;> simp [fieldConstant] at hi ⊢
  · -- i = 0: α₇ < α₀
    have h := field_ordering
    linarith
  · -- i = 1: α₇ < α₁
    have h := field_ordering
    linarith
  · -- i = 2: α₇ < α₂
    have h := field_ordering
    linarith
  · -- i = 3: α₇ < α₃
    have h := field_ordering
    linarith
  · -- i = 4: α₇ < α₄
    exact field_ordering.1
  · -- i = 5: α₇ < α₅
    have h := field_ordering
    linarith
  · -- i = 6: α₇ < α₆
    have h := field_ordering
    linarith
  · -- i = 7: contradiction
    contradiction

/-- α₅ is the largest field constant -/
theorem α₅_largest (i : Fin 8) (hi : i ≠ 5) : fieldConstant i < α₅ := by
  fin_cases i <;> simp [fieldConstant] at hi ⊢
  · -- i = 0: α₀ < α₅
    have h := field_ordering
    linarith
  · -- i = 1: α₁ < α₅
    exact field_ordering.2.2.2.2.2.2
  · -- i = 2: α₂ < α₅
    have h := field_ordering
    linarith
  · -- i = 3: α₃ < α₅
    have h := field_ordering
    linarith
  · -- i = 4: α₄ < α₅
    have h := field_ordering
    linarith
  · -- i = 5: contradiction
    contradiction
  · -- i = 6: α₆ < α₅
    have h := field_ordering
    linarith
  · -- i = 7: α₇ < α₅
    have h := field_ordering
    linarith

end PrimeOS12288