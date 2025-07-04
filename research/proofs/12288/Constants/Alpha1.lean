import Mathlib.Data.Real.Basic
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Tactic.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Logic.Unique
import PrimeOS12288.Axioms.Growth

namespace PrimeOS12288.Constants

open PrimeOS12288.Axioms

/-- The tribonacci constant α₁ ≈ 1.839... -/
noncomputable def α₁ : ℝ := Classical.choose tribonacci_exists

/-- α₁ satisfies the tribonacci equation -/
theorem α₁_tribonacci : α₁^3 = α₁^2 + α₁ + 1 := by
  have h := Classical.choose_spec tribonacci_exists
  exact h.2

/-- α₁ is positive -/
theorem α₁_pos : 0 < α₁ := by
  have h := Classical.choose_spec tribonacci_exists
  linarith [h.1]

/-- α₁ is greater than 1 -/
theorem α₁_gt_one : 1 < α₁ := by
  have h := Classical.choose_spec tribonacci_exists
  exact h.1

/-- α₁ is less than 2 -/
theorem α₁_lt_two : α₁ < 2 := by
  -- We'll prove this by contradiction: if α₁ ≥ 2, then α₁³ ≥ 8 > 7 = 2² + 2 + 1
  by_contra h
  push_neg at h
  have h1 : 2 ≤ α₁ := h
  have h2 : 8 ≤ α₁^3 := by
    calc 8 = 2^3 := by norm_num
    _ ≤ α₁^3 := by exact pow_le_pow_left (by linarith : 0 ≤ 2) h1 3
  have h3 : α₁^3 = α₁^2 + α₁ + 1 := α₁_tribonacci
  have h4 : α₁^2 + α₁ + 1 ≤ α₁^2 + α₁ + α₁ := by linarith
  have h5 : α₁^2 + α₁ + α₁ = α₁^2 + 2*α₁ := by ring
  have h6 : α₁^2 + 2*α₁ < α₁^2 + 2*α₁ + 1 := by linarith
  have h7 : α₁^2 + 2*α₁ + 1 = (α₁ + 1)^2 := by ring
  have h8 : (α₁ + 1)^2 ≤ (2 + 1)^2 := by
    apply sq_le_sq'
    · linarith
    · linarith [h1]
  have h9 : (2 + 1)^2 = 9 := by norm_num
  have : 8 ≤ α₁^3 := h2
  rw [h3] at this
  have : 8 ≤ α₁^2 + α₁ + 1 := this
  have : α₁^2 + α₁ + 1 < 9 := by
    calc α₁^2 + α₁ + 1 ≤ α₁^2 + 2*α₁ := h4
    _ < (α₁ + 1)^2 := by rw [← h5, ← h7]; exact h6
    _ ≤ 9 := by rw [← h9]; exact h8
  linarith

/-- Bounds for α₁ -/
theorem α₁_bounds : 1.83928 < α₁ ∧ α₁ < 1.83929 := by
  -- Get the bounds from the axiom
  have ⟨t, ht⟩ := tribonacci_bounds
  -- We need to show that t = α₁
  -- Since both t and α₁ satisfy the tribonacci equation and are > 1
  have h_t : t > 1 ∧ t^3 = t^2 + t + 1 := by
    constructor
    · linarith [ht.1]
    · exact ht.2.2
  have h_α₁ : α₁ > 1 ∧ α₁^3 = α₁^2 + α₁ + 1 := ⟨α₁_gt_one, α₁_tribonacci⟩
  -- By uniqueness, t = α₁
  have : t = α₁ := by
    have unique := tribonacci_unique
    rw [ExistsUnique] at unique
    have ⟨x, hx, hunique⟩ := unique
    have : t = x := hunique t h_t
    have : α₁ = x := hunique α₁ h_α₁
    rw [this, ← this]
  rw [← this]
  exact ⟨ht.1, ht.2.1⟩

/-- Approximation of α₁ -/
theorem α₁_approx : |α₁ - 1.839| < 0.001 := by
  have h := α₁_bounds
  have h1 : 1.83928 < α₁ := h.1
  have h2 : α₁ < 1.83929 := h.2
  -- We need to show |α₁ - 1.839| < 0.001
  -- This is equivalent to -0.001 < α₁ - 1.839 < 0.001
  -- Which is 1.838 < α₁ < 1.840
  rw [abs_sub_lt_iff]
  constructor
  · linarith
  · linarith

end PrimeOS12288.Constants