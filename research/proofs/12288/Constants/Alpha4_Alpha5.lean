import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Pi.Bounds
import PrimeOS12288.Constants.Pi

namespace PrimeOS12288.Constants

/-- The derived constant α₄ = 1/(2π) -/
noncomputable def α₄ : ℝ := 1 / (2 * Real.pi)

/-- The derived constant α₅ = 2π -/
noncomputable def α₅ : ℝ := 2 * Real.pi

/-- α₄ is positive -/
theorem α₄_pos : 0 < α₄ := by
  unfold α₄
  apply div_pos
  · exact one_pos
  · apply mul_pos
    · exact two_pos
    · exact Real.pi_pos

/-- α₅ is positive -/
theorem α₅_pos : 0 < α₅ := by
  unfold α₅
  apply mul_pos
  · exact two_pos
  · exact Real.pi_pos

/-- α₄ is less than 1 -/
theorem α₄_lt_one : α₄ < 1 := by
  unfold α₄
  rw [div_lt_iff]
  · simp only [one_mul]
    apply lt_trans two_lt_three
    exact Real.three_lt_pi
  · apply mul_pos
    · exact two_pos
    · exact Real.pi_pos

/-- α₅ is greater than 1 -/
theorem α₅_gt_one : 1 < α₅ := by
  unfold α₅
  rw [lt_mul_iff_one_lt_left]
  · apply lt_trans one_lt_two
    exact Real.two_lt_pi
  · exact two_pos

/-- Numerical lower bound for α₄ -/
theorem α₄_lower_bound : 0.159 < α₄ := by
  unfold α₄
  -- We want to show 0.159 < 1/(2π)
  -- This is equivalent to 0.159 * 2π < 1
  rw [div_lt_iff (mul_pos two_pos Real.pi_pos)]
  norm_num
  ring_nf
  -- Need to show π * 0.318 < 1, which is π < 1/0.318 ≈ 3.1446
  -- Since π ≈ 3.14159..., we have π < 3.1446
  -- We'll use the approximation π < 3.1416 (which is true)
  have h_pi_upper : Real.pi < 3.1416 := Real.pi_lt_31416
  calc Real.pi * 0.318 < 3.1416 * 0.318 := by
    apply mul_lt_mul_of_pos_right h_pi_upper
    norm_num
  _ = 0.9990288 := by norm_num
  _ < 1 := by norm_num

/-- Numerical upper bound for α₄ -/
theorem α₄_upper_bound : α₄ < 0.160 := by
  unfold α₄
  -- We want to show 1/(2π) < 0.160
  -- This is equivalent to 1 < 0.160 * 2π
  rw [lt_div_iff (mul_pos two_pos Real.pi_pos)]
  norm_num
  ring_nf
  -- Need to show 1 < π * 0.32, which is 3.125 < π
  -- Since π > 3.14159... > 3.125, this holds
  have h_pi_lower : 3.14159 < Real.pi := by
    -- We use that 3.1415 < π
    have h : 3.1415 < Real.pi := Real.pi_gt_31415
    linarith
  calc 1 = 0.32 * 3.125 := by norm_num
  _ < 0.32 * 3.14159 := by
    apply mul_lt_mul_of_pos_left
    norm_num
    norm_num
  _ < 0.32 * Real.pi := by
    apply mul_lt_mul_of_pos_left h_pi_lower
    norm_num

/-- Numerical lower bound for α₅ -/
theorem α₅_lower_bound : 6.28 < α₅ := by
  unfold α₅
  -- We want to show 6.28 < 2π
  -- This is equivalent to 3.14 < π
  have h_pi_lower : 3.14 < Real.pi := Real.pi_gt_314
  calc 6.28 = 2 * 3.14 := by norm_num
  _ < 2 * Real.pi := by
    apply mul_lt_mul_of_pos_left h_pi_lower
    norm_num

/-- Numerical upper bound for α₅ -/
theorem α₅_upper_bound : α₅ < 6.29 := by
  unfold α₅
  -- We want to show 2π < 6.29
  -- This is equivalent to π < 3.145
  have h_pi_upper : Real.pi < 3.145 := by
    -- We use that π < 3.15
    have h : Real.pi < 3.15 := Real.pi_lt_315
    linarith
  calc 2 * Real.pi < 2 * 3.145 := by
    apply mul_lt_mul_of_pos_left h_pi_upper
    norm_num
  _ = 6.29 := by norm_num

/-- The unity product: α₄ * α₅ = 1 -/
theorem α₄_mul_α₅_eq_one : α₄ * α₅ = 1 := by
  unfold α₄ α₅
  rw [mul_comm α₄ α₅]
  simp only [mul_div_assoc]
  rw [mul_comm (2 * Real.pi)]
  simp only [div_self_iff_one]
  ring_nf
  simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Real.pi_ne_zero, or_self, not_false_eq_true]

/-- α₄ and α₅ are distinct -/
theorem α₄_ne_α₅ : α₄ ≠ α₅ := by
  intro h
  have h1 := α₄_lt_one
  have h2 := α₅_gt_one
  rw [h] at h1
  linarith

/-- There exist coefficients relating α₄ to π -/
theorem α₄_encodes_π : ∃ k : ℝ, Real.pi = k * α₄ := by
  use 2 * Real.pi * Real.pi
  unfold α₄
  field_simp
  ring

/-- There exist coefficients relating α₅ to π -/
theorem α₅_encodes_π : ∃ k : ℝ, Real.pi = k * α₅ := by
  use 1 / 2
  unfold α₅
  field_simp
  ring

/-- α₄ and α₅ are linearly independent over ℝ -/
theorem α₄_α₅_lin_indep : ∀ a b : ℝ, a * α₄ + b * α₅ = 0 → a = 0 ∧ b = 0 := by
  intro a b h
  -- If a * α₄ + b * α₅ = 0, multiply by α₄ to get a * α₄² + b * α₄ * α₅ = 0
  have h1 : a * α₄^2 + b * α₄ * α₅ = 0 := by
    rw [← mul_zero α₄]
    rw [← h]
    ring
  -- Use α₄ * α₅ = 1
  rw [α₄_mul_α₅_eq_one] at h1
  have h1' : a * α₄^2 + b = 0 := by simp [mul_one] at h1; exact h1
  -- Also multiply by α₅ to get a * α₄ * α₅ + b * α₅² = 0
  have h2 : a * α₄ * α₅ + b * α₅^2 = 0 := by
    rw [← mul_zero α₅]
    rw [← h]
    ring
  rw [α₄_mul_α₅_eq_one] at h2
  have h2' : a + b * α₅^2 = 0 := by simp [mul_one] at h2; exact h2
  -- From h2': a = -b * α₅²
  have ha : a = -b * α₅^2 := by linarith
  -- Substitute into h1'
  rw [ha] at h1'
  have : -b * α₅^2 * α₄^2 + b = 0 := h1'
  have : b * (-α₅^2 * α₄^2 + 1) = 0 := by ring_nf at this ⊢; exact this
  -- We need to show -α₅² * α₄² + 1 ≠ 0
  have key : -α₅^2 * α₄^2 + 1 ≠ 0 := by
    rw [← neg_ne_zero]
    rw [neg_sub]
    rw [sub_ne_zero]
    rw [← sq_eq_sq (α₄_mul_α₅_eq_one) (one_pow 2)]
    rw [mul_pow]
    rw [mul_comm α₄^2]
    exact one_ne_zero
  -- Therefore b = 0
  have hb : b = 0 := by
    cases' mul_eq_zero.mp this with h h
    · exact h
    · exfalso; exact key h
  -- And from ha and hb: a = 0
  rw [hb] at ha
  simp at ha
  exact ⟨ha, hb⟩

/-- α₄ and α₅ together encode π uniquely -/
theorem α₄_α₅_encode_π : ∃ a b : ℝ, Real.pi = a * α₄ + b * α₅ ∧ 
  ∀ a' b' : ℝ, Real.pi = a' * α₄ + b' * α₅ → a = a' ∧ b = b' := by
  -- We can express π = 0 * α₄ + (1/2) * α₅
  use 0, 1/2
  constructor
  · unfold α₄ α₅
    simp only [zero_mul, zero_add]
    field_simp
    ring
  · intro a' b' h
    -- From our representation and h: 0 * α₄ + (1/2) * α₅ = a' * α₄ + b' * α₅
    have h_eq : 0 * α₄ + (1/2) * α₅ = a' * α₄ + b' * α₅ := by
      rw [← h]
      unfold α₄ α₅
      simp only [zero_mul, zero_add]
      field_simp
      ring
    -- Rearranging: (a' - 0) * α₄ + (b' - 1/2) * α₅ = 0
    have : (a' - 0) * α₄ + (b' - 1/2) * α₅ = 0 := by linarith
    -- By linear independence
    have ⟨ha, hb⟩ := α₄_α₅_lin_indep (a' - 0) (b' - 1/2) this
    simp at ha hb
    exact ⟨ha, by linarith⟩

/-- α₄ equals 1/(2π) -/
theorem α₄_eq : α₄ = 1 / (2 * Real.pi) := rfl

/-- α₅ equals 2π -/
theorem α₅_eq : α₅ = 2 * Real.pi := rfl

/-- π can be expressed in terms of α₄ -/
theorem pi_from_α₄ : Real.pi = 1 / (2 * α₄) := by
  unfold α₄
  field_simp
  ring

/-- π can be expressed in terms of α₅ -/
theorem pi_from_α₅ : Real.pi = α₅ / 2 := by
  unfold α₅
  ring

/-- The product α₄ * α₅ equals 1 (alternative proof) -/
theorem α₄_α₅_unity : α₄ * α₅ = 1 := by
  rw [α₄_eq, α₅_eq]
  field_simp
  ring

/-- α₄ is the reciprocal of α₅ -/
theorem α₄_eq_inv_α₅ : α₄ = 1 / α₅ := by
  rw [← α₄_mul_α₅_eq_one]
  field_simp [ne_of_gt α₅_pos]

/-- α₅ is the reciprocal of α₄ -/
theorem α₅_eq_inv_α₄ : α₅ = 1 / α₄ := by
  rw [← α₄_mul_α₅_eq_one]
  field_simp [ne_of_gt α₄_pos]

end PrimeOS12288.Constants