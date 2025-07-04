import PrimeOS12288.Constants.Alpha0
import PrimeOS12288.Constants.Alpha1
import PrimeOS12288.Constants.Alpha2
import PrimeOS12288.Constants.Alpha3
import PrimeOS12288.Constants.Alpha4_Alpha5
import PrimeOS12288.Constants.Alpha6_Alpha7

namespace PrimeOS12288.Constants

/-- All constants are pairwise distinct -/

-- α₀ distinctness
theorem α₀_ne_α₁ : α₀ ≠ α₁ := by
  unfold α₀ α₁
  norm_num
  -- α₁ satisfies α₁³ = α₁² + α₁ + 1
  -- Since α₀ = 1, we'd need 1³ = 1² + 1 + 1, i.e., 1 = 3, which is false
  intro h
  rw [← h] at α₁_value
  norm_num at α₁_value

theorem α₀_ne_α₂ : α₀ ≠ α₂ := by
  unfold α₀ α₂
  norm_num
  -- α₂ satisfies α₂² = α₂ + 1
  -- Since α₀ = 1, we'd need 1² = 1 + 1, i.e., 1 = 2, which is false
  intro h
  rw [← h] at α₂_value
  norm_num at α₂_value

theorem α₀_ne_α₃ : α₀ ≠ α₃ := by
  unfold α₀ α₃
  norm_num

theorem α₀_ne_α₄ : α₀ ≠ α₄ := by
  intro h
  have h1 := α₀_value
  have h2 := α₄_lt_one
  rw [h1] at h
  rw [← h] at h2
  norm_num at h2

theorem α₀_ne_α₅ : α₀ ≠ α₅ := by
  intro h
  have h1 := α₀_value
  have h2 := α₅_gt_one
  rw [h1] at h
  rw [← h] at h2
  norm_num at h2

theorem α₀_ne_α₆ : α₀ ≠ α₆ := by
  intro h
  have h1 := α₀_value
  have h2 := α₆_lt_one
  rw [h1] at h
  rw [← h] at h2
  norm_num at h2

theorem α₀_ne_α₇ : α₀ ≠ α₇ := by
  intro h
  have h1 := α₀_value
  have h2 := α₇_lt_one
  rw [h1] at h
  rw [← h] at h2
  norm_num at h2

-- α₁ distinctness
theorem α₁_ne_α₂ : α₁ ≠ α₂ := by
  -- Both are roots of different irreducible polynomials
  intro h
  -- α₁³ = α₁² + α₁ + 1 and α₂² = α₂ + 1
  have h1 := α₁_value
  have h2 := α₂_value
  rw [h] at h1
  -- Now α₂³ = α₂² + α₂ + 1
  rw [h2] at h1
  -- α₂³ = (α₂ + 1) + α₂ + 1 = 2α₂ + 2
  ring_nf at h1
  -- But also α₂³ = α₂ · α₂² = α₂(α₂ + 1) = α₂² + α₂ = (α₂ + 1) + α₂ = 2α₂ + 1
  have h3 : α₂^3 = 2*α₂ + 1 := by
    rw [pow_succ, h2]
    ring
  rw [h1] at h3
  linarith

theorem α₁_ne_α₃ : α₁ ≠ α₃ := by
  intro h
  have h1 := α₁_gt_one
  have h2 := α₃_value
  rw [h] at h1
  rw [h2] at h1
  norm_num at h1

theorem α₁_ne_α₄ : α₁ ≠ α₄ := by
  intro h
  have h1 := α₁_gt_one
  have h2 := α₄_lt_one
  rw [h] at h1
  linarith

theorem α₁_ne_α₅ : α₁ ≠ α₅ := by
  -- α₁ ≈ 1.84 and α₅ = 2π ≈ 6.28
  intro h
  have h1 := α₁_upper_bound
  have h2 := α₅_lower_bound
  rw [h] at h1
  linarith

theorem α₁_ne_α₆ : α₁ ≠ α₆ := by
  intro h
  have h1 := α₁_gt_one
  have h2 := α₆_lt_one
  rw [h] at h1
  linarith

theorem α₁_ne_α₇ : α₁ ≠ α₇ := by
  intro h
  have h1 := α₁_gt_one
  have h2 := α₇_lt_one
  rw [h] at h1
  linarith

-- α₂ distinctness
theorem α₂_ne_α₃ : α₂ ≠ α₃ := by
  intro h
  have h1 := α₂_gt_one
  have h2 := α₃_value
  rw [h] at h1
  rw [h2] at h1
  norm_num at h1

theorem α₂_ne_α₄ : α₂ ≠ α₄ := by
  intro h
  have h1 := α₂_gt_one
  have h2 := α₄_lt_one
  rw [h] at h1
  linarith

theorem α₂_ne_α₅ : α₂ ≠ α₅ := by
  -- α₂ ≈ 1.62 and α₅ = 2π ≈ 6.28
  intro h
  have h1 := α₂_upper_bound
  have h2 := α₅_lower_bound
  rw [h] at h1
  linarith

theorem α₂_ne_α₆ : α₂ ≠ α₆ := by
  intro h
  have h1 := α₂_gt_one
  have h2 := α₆_lt_one
  rw [h] at h1
  linarith

theorem α₂_ne_α₇ : α₂ ≠ α₇ := by
  intro h
  have h1 := α₂_gt_one
  have h2 := α₇_lt_one
  rw [h] at h1
  linarith

-- α₃ distinctness
theorem α₃_ne_α₄ : α₃ ≠ α₄ := by
  intro h
  have h1 := α₃_value
  have h2 := α₄_upper_bound
  rw [h1] at h
  rw [← h] at h2
  norm_num at h2

theorem α₃_ne_α₅ : α₃ ≠ α₅ := by
  intro h
  have h1 := α₃_value
  have h2 := α₅_gt_one
  rw [h1] at h
  rw [← h] at h2
  norm_num at h2

theorem α₃_ne_α₆ : α₃ ≠ α₆ := by
  intro h
  have h1 := α₃_value
  have h2 := α₆_value
  rw [h1] at h
  rw [← h] at h2
  norm_num at h2

theorem α₃_ne_α₇ : α₃ ≠ α₇ := by
  intro h
  have h1 := α₃_value
  have h2 := α₇_value
  rw [h1] at h
  rw [← h] at h2
  norm_num at h2

-- α₄ distinctness (α₄_ne_α₅ already defined in Alpha4_Alpha5.lean)
theorem α₄_ne_α₆ : α₄ ≠ α₆ := by
  intro h
  have h1 := α₄_upper_bound
  have h2 := α₆_value
  rw [h] at h1
  rw [h2] at h1
  norm_num at h1

theorem α₄_ne_α₇ : α₄ ≠ α₇ := by
  intro h
  have h1 := α₄_lower_bound
  have h2 := α₇_value
  rw [h] at h1
  rw [h2] at h1
  norm_num at h1

-- α₅ distinctness
theorem α₅_ne_α₆ : α₅ ≠ α₆ := by
  intro h
  have h1 := α₅_gt_one
  have h2 := α₆_lt_one
  rw [h] at h1
  linarith

theorem α₅_ne_α₇ : α₅ ≠ α₇ := by
  intro h
  have h1 := α₅_gt_one
  have h2 := α₇_lt_one
  rw [h] at h1
  linarith

-- α₆ distinctness (α₆_ne_α₇ already defined in Alpha6_Alpha7.lean)

end PrimeOS12288.Constants