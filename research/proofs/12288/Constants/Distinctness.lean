import Constants.Alpha0
import Constants.Alpha1
import Constants.Alpha2
import Constants.Alpha3
import Constants.Alpha4_Alpha5
import Constants.Alpha6_Alpha7
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace PrimeOS12288.Constants

/-- All constants are pairwise distinct -/

-- α₀ = 1 distinctness
theorem α₀_ne_α₁ : α₀ ≠ α₁ := by
  -- α₀ = 1 < α₁
  simp only [α₀_eq_one]
  exact ne_of_lt α₁_gt_one

theorem α₀_ne_α₂ : α₀ ≠ α₂ := by
  -- α₀ = 1 < α₂
  simp only [α₀_eq_one]
  exact ne_of_lt α₂_gt_one

theorem α₀_ne_α₃ : α₀ ≠ α₃ := by
  -- α₀ = 1 ≠ 1/2 = α₃
  simp only [α₀_eq_one, α₃_eq_half]
  norm_num

theorem α₀_ne_α₄ : α₀ ≠ α₄ := by
  -- α₄ < 1 = α₀
  simp only [α₀_eq_one]
  exact ne_of_gt α₄_lt_one

theorem α₀_ne_α₅ : α₀ ≠ α₅ := by
  -- α₀ = 1 < α₅
  simp only [α₀_eq_one]
  exact ne_of_lt α₅_gt_one

theorem α₀_ne_α₆ : α₀ ≠ α₆ := by
  -- α₆ < 1 = α₀
  simp only [α₀_eq_one]
  exact ne_of_gt α₆_lt_one

theorem α₀_ne_α₇ : α₀ ≠ α₇ := by
  -- α₇ < 1 = α₀
  simp only [α₀_eq_one]
  exact ne_of_gt α₇_lt_one

-- α₁ distinctness
theorem α₁_ne_α₂ : α₁ ≠ α₂ := by
  -- Use the equation difference
  intro h
  have h1 := α₁_equation
  have h2 := α₂_equation
  rw [h] at h1
  -- α₂³ = α₂² + α₂ + 1 but also α₂² = α₂ + 1
  -- So α₂³ = (α₂ + 1) + α₂ + 1 = 2α₂ + 2
  have : α₂^3 = 2*α₂ + 2 := by
    calc α₂^3 = α₂^2 + α₂ + 1 := h1
    _ = (α₂ + 1) + α₂ + 1 := by rw [h2]
    _ = 2*α₂ + 2 := by ring
  -- But α₂³ = α₂ · α₂² = α₂(α₂ + 1) = α₂² + α₂
  have : α₂^3 = α₂^2 + α₂ := by
    calc α₂^3 = α₂ * α₂^2 := by ring
    _ = α₂ * (α₂ + 1) := by rw [h2]
    _ = α₂^2 + α₂ := by ring
  -- So 2α₂ + 2 = α₂² + α₂, which gives α₂² = α₂ + 2
  have : α₂^2 = α₂ + 2 := by linarith
  -- But we know α₂² = α₂ + 1
  rw [h2] at this
  -- So α₂ + 1 = α₂ + 2, contradiction
  linarith

theorem α₁_ne_α₃ : α₁ ≠ α₃ := by
  -- α₃ = 1/2 < 1 < α₁
  intro h
  have h1 : α₃ < 1 := by simp [α₃_eq_half]; norm_num
  have h2 : 1 < α₁ := α₁_gt_one
  rw [h] at h2
  linarith

theorem α₁_ne_α₄ : α₁ ≠ α₄ := by
  -- α₄ < 1 < α₁
  exact ne_of_gt (lt_trans α₄_lt_one α₁_gt_one)

theorem α₁_ne_α₅ : α₁ ≠ α₅ := by
  -- α₁ < 2 < 6 < α₅
  intro h
  have h1 : α₁ < 2 := α₁_lt_two
  have h2 : 6 < α₅ := α₅_gt_six
  rw [h] at h1
  linarith

theorem α₁_ne_α₆ : α₁ ≠ α₆ := by
  -- α₆ < 1 < α₁
  exact ne_of_gt (lt_trans α₆_lt_one α₁_gt_one)

theorem α₁_ne_α₇ : α₁ ≠ α₇ := by
  -- α₇ < 1 < α₁
  exact ne_of_gt (lt_trans α₇_lt_one α₁_gt_one)

-- α₂ distinctness
theorem α₂_ne_α₃ : α₂ ≠ α₃ := by
  -- α₃ = 1/2 < 1 < α₂
  intro h
  have h1 : α₃ < 1 := by simp [α₃_eq_half]; norm_num
  have h2 : 1 < α₂ := α₂_gt_one
  rw [h] at h2
  linarith

theorem α₂_ne_α₄ : α₂ ≠ α₄ := by
  -- α₄ < 1 < α₂
  exact ne_of_gt (lt_trans α₄_lt_one α₂_gt_one)

theorem α₂_ne_α₅ : α₂ ≠ α₅ := by
  -- α₂ < 2 < 6 < α₅
  intro h
  have h1 : α₂ < 2 := α₂_lt_two
  have h2 : 6 < α₅ := α₅_gt_six
  rw [h] at h1
  linarith

theorem α₂_ne_α₆ : α₂ ≠ α₆ := by
  -- α₆ < 1 < α₂
  exact ne_of_gt (lt_trans α₆_lt_one α₂_gt_one)

theorem α₂_ne_α₇ : α₂ ≠ α₇ := by
  -- α₇ < 1 < α₂
  exact ne_of_gt (lt_trans α₇_lt_one α₂_gt_one)

-- α₃ distinctness
theorem α₃_ne_α₄ : α₃ ≠ α₄ := by
  -- α₄ < 1/6 < 1/2 = α₃
  intro h
  have h1 : α₄ < 1/6 := α₄_lt_one_sixth
  have h2 : (1:ℝ)/6 < 1/2 := by norm_num
  rw [← h, α₃_eq_half] at h1
  linarith

theorem α₃_ne_α₅ : α₃ ≠ α₅ := by
  -- α₃ = 1/2 < 1 < α₅
  intro h
  have h1 : α₃ < 1 := by simp [α₃_eq_half]; norm_num
  have h2 : 1 < α₅ := α₅_gt_one
  rw [h] at h1
  linarith

theorem α₃_ne_α₆ : α₃ ≠ α₆ := by
  -- α₃ = 1/2, α₆ = 0.19961197478400415
  simp only [α₃_eq_half, α₆_eq]
  norm_num

theorem α₃_ne_α₇ : α₃ ≠ α₇ := by
  -- α₃ = 1/2, α₇ = 0.014134725141734695
  simp only [α₃_eq_half, α₇_eq]
  norm_num

-- α₄ distinctness
theorem α₄_ne_α₅ : α₄ ≠ α₅ := by
  -- α₄ < 1 < α₅
  exact ne_of_lt (lt_trans α₄_lt_one α₅_gt_one)

theorem α₄_ne_α₆ : α₄ ≠ α₆ := by
  -- α₄ < 1/6 < α₆ (since α₆ = 0.1996... > 1/6 = 0.1666...)
  intro h
  have h1 : α₄ < 1/6 := α₄_lt_one_sixth
  have h2 : (1:ℝ)/6 < α₆ := by rw [α₆_eq]; norm_num
  rw [h] at h1
  linarith

theorem α₄_ne_α₇ : α₄ ≠ α₇ := by
  -- α₇ < α₄ (from System axiom: α₇ < α₆ < 1 and α₄ < 1)
  -- We need to show α₇ = 0.0141... < α₄ = 1/(2π) ≈ 0.159...
  intro h
  -- α₄ > 1/(2*3.14160) > 0.159
  have h1 : (1:ℝ)/(2*3.14160) < α₄ := α₄_lower_bound
  have h2 : (0.159:ℝ) < 1/(2*3.14160) := by norm_num
  -- α₇ = 0.0141... < 0.159
  have h3 : α₇ < 0.159 := by rw [α₇_eq]; norm_num
  rw [← h] at h3
  linarith

-- α₅ distinctness
theorem α₅_ne_α₆ : α₅ ≠ α₆ := by
  -- α₆ < 1 < α₅
  exact ne_of_gt (lt_trans α₆_lt_one α₅_gt_one)

theorem α₅_ne_α₇ : α₅ ≠ α₇ := by
  -- α₇ < 1 < α₅
  exact ne_of_gt (lt_trans α₇_lt_one α₅_gt_one)

-- α₆ distinctness
theorem α₆_ne_α₇ : α₆ ≠ α₇ := by
  -- Direct from their values
  simp only [α₆_eq, α₇_eq]
  norm_num

end PrimeOS12288.Constants