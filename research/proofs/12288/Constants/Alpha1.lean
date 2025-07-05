import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Axioms.Growth

namespace PrimeOS12288.Constants

open PrimeOS12288.Axioms

/-- The tribonacci constant -/
noncomputable def α₁ : ℝ := Classical.choose tribonacci_exists

/-- α₁ is greater than 1 -/
theorem α₁_gt_one : 1 < α₁ :=
  (Classical.choose_spec tribonacci_exists).1

/-- α₁ satisfies the tribonacci equation -/
theorem α₁_equation : α₁^3 = α₁^2 + α₁ + 1 :=
  (Classical.choose_spec tribonacci_exists).2

/-- α₁ is positive -/
theorem α₁_pos : 0 < α₁ := by
  linarith [α₁_gt_one]

/-- α₁ is nonzero -/
theorem α₁_ne_zero : α₁ ≠ 0 :=
  ne_of_gt α₁_pos

/-- α₁ satisfies the tribonacci equation (alias for compatibility) -/
theorem α₁_tribonacci : α₁^3 = α₁^2 + α₁ + 1 := α₁_equation

/-- α₁ satisfies the tribonacci equation (alias for compatibility) -/
theorem α₁_value : α₁^3 = α₁^2 + α₁ + 1 := α₁_equation

/-- Numerical bounds for α₁ -/
theorem α₁_bounds : 1.83928 < α₁ ∧ α₁ < 1.83929 := by
  -- Get the bounded tribonacci constant from the axiom
  have ⟨t, ht⟩ := tribonacci_bounds
  have ht_bounds : 1.83928 < t ∧ t < 1.83929 := ⟨ht.1, ht.2.1⟩
  have ht_eq : t^3 = t^2 + t + 1 := ht.2.2
  have ht_gt : t > 1 := by
    -- Since t > 1.83928 and 1.83928 > 1, we have t > 1
    have h : (1.83928 : ℝ) > 1 := by norm_num
    linarith [ht.1, h]
  
  -- α₁ also satisfies these properties
  have hα₁_gt := α₁_gt_one
  have hα₁_eq := α₁_equation
  
  -- By uniqueness, t = α₁
  have unique := tribonacci_unique
  obtain ⟨x, ⟨_, hx_unique⟩⟩ := unique
  have : t = x := hx_unique t ⟨ht_gt, ht_eq⟩
  have : α₁ = x := hx_unique α₁ ⟨hα₁_gt, hα₁_eq⟩
  -- Therefore t = α₁
  have : t = α₁ := by
    rw [‹t = x›, ‹α₁ = x›]
  rw [←this]
  exact ht_bounds

/-- Upper bound for α₁ -/
theorem α₁_upper_bound : α₁ < 1.83929 := α₁_bounds.2

/-- Lower bound for α₁ -/ 
theorem α₁_lower_bound : 1.83928 < α₁ := α₁_bounds.1

/-- α₁ is less than 2 -/
theorem α₁_lt_two : α₁ < 2 := by
  calc α₁ < 1.83929 := α₁_upper_bound
  _ < 2 := by norm_num

/-- α₁ is not equal to 2 -/
theorem α₁_ne_two : α₁ ≠ 2 := ne_of_lt α₁_lt_two

/-- α₁ is not equal to 6 -/
theorem α₁_ne_six : α₁ ≠ 6 := by
  intro h
  have : α₁ < 2 := α₁_lt_two
  rw [h] at this
  norm_num at this

end PrimeOS12288.Constants