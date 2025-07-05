import Axioms.Unity
import Mathlib.Data.Real.Basic

namespace PrimeOS12288.Constants

open PrimeOS12288.Axioms

/-- The identity constant -/
noncomputable def α₀ : ℝ := Classical.choose unity_exists

/-- α₀ equals 1 -/
theorem α₀_eq_one : α₀ = 1 :=
  (Classical.choose_spec unity_exists).1

/-- α₀ is the multiplicative identity -/
theorem α₀_identity : ∀ x : ℝ, α₀ * x = x ∧ x * α₀ = x :=
  (Classical.choose_spec unity_exists).2

/-- α₀ is positive -/
theorem α₀_pos : 0 < α₀ := by
  rw [α₀_eq_one]
  norm_num

/-- α₀ is the multiplicative identity (left) -/
theorem α₀_mul_id_left (x : ℝ) : α₀ * x = x :=
  (α₀_identity x).1

/-- α₀ is the multiplicative identity (right) -/
theorem α₀_mul_id_right (x : ℝ) : x * α₀ = x :=
  (α₀_identity x).2

/-- α₀ raised to any power equals α₀ -/
theorem α₀_pow (n : ℕ) : α₀ ^ n = α₀ := by
  rw [α₀_eq_one]
  rw [one_pow]

/-- α₀ equals 1 (alias for compatibility) -/
theorem α₀_value : α₀ = 1 := α₀_eq_one

end PrimeOS12288.Constants
