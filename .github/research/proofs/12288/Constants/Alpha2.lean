import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Axioms.Golden

namespace PrimeOS12288.Constants

open PrimeOS12288.Axioms

/-- The golden ratio -/
noncomputable def α₂ : ℝ := Classical.choose golden_exists

/-- α₂ is positive -/
theorem α₂_pos : 0 < α₂ :=
  (Classical.choose_spec golden_exists).1

/-- α₂ satisfies the golden ratio equation -/
theorem α₂_equation : α₂^2 = α₂ + 1 :=
  (Classical.choose_spec golden_exists).2

/-- α₂ is greater than 1 -/
theorem α₂_gt_one : 1 < α₂ := by
  -- From α₂² = α₂ + 1 and α₂ > 0
  have h1 := α₂_equation
  have h2 := α₂_pos
  -- If α₂ ≤ 1, then α₂² ≤ 1, but α₂² = α₂ + 1 > 1
  by_contra h
  push_neg at h
  have h3 : α₂^2 ≤ 1 := by
    exact pow_le_one 2 (le_of_lt h2) h
  rw [h1] at h3
  -- Now h3 says α₂ + 1 ≤ 1, which means α₂ ≤ 0
  linarith [h2]

/-- α₂ is nonzero -/
theorem α₂_ne_zero : α₂ ≠ 0 :=
  ne_of_gt α₂_pos

/-- Numerical bounds for α₂ -/
theorem α₂_bounds : 1.618 < α₂ ∧ α₂ < 1.619 := by
  -- Get the bounded golden ratio from the axiom
  have ⟨φ, hφ⟩ := golden_bounds
  have hφ_bounds : 1.618 < φ ∧ φ < 1.619 := ⟨hφ.1, hφ.2.1⟩
  have hφ_eq : φ^2 = φ + 1 := hφ.2.2
  have hφ_gt : φ > 0 := by
    -- Since φ > 1.618 and 1.618 > 0, we have φ > 0
    have h : (1.618 : ℝ) > 0 := by norm_num
    linarith [hφ.1, h]
  
  -- α₂ also satisfies these properties
  have hα₂_gt := α₂_pos
  have hα₂_eq := α₂_equation
  
  -- By uniqueness, φ = α₂
  have unique := golden_unique
  obtain ⟨x, ⟨_, hx_unique⟩⟩ := unique
  have : φ = x := hx_unique φ ⟨hφ_gt, hφ_eq⟩
  have : α₂ = x := hx_unique α₂ ⟨hα₂_gt, hα₂_eq⟩
  -- Therefore φ = α₂
  have : φ = α₂ := by
    rw [‹φ = x›, ‹α₂ = x›]
  rw [←this]
  exact hφ_bounds

/-- Lower bound for α₂ -/
theorem α₂_lower_bound : 1.618 < α₂ := α₂_bounds.1

/-- Upper bound for α₂ -/
theorem α₂_upper_bound : α₂ < 1.619 := α₂_bounds.2

/-- α₂ is less than 2 -/
theorem α₂_lt_two : α₂ < 2 := by
  calc α₂ < 1.619 := α₂_upper_bound
  _ < 2 := by norm_num

-- Note: α₂ = (1 + √5)/2 ≈ 1.6180339887...
-- This exact formula is not needed for our proofs,
-- the bounds 1.618 < α₂ < 1.619 are sufficient.

end PrimeOS12288.Constants