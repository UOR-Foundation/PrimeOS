import Axioms.Binary
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace PrimeOS12288.Constants

open PrimeOS12288.Axioms

/-- The binary constant (one-half) -/
noncomputable def α₃ : ℝ := Classical.choose binary_exists

/-- α₃ equals 1/2 -/
theorem α₃_eq_half : α₃ = 1/2 :=
  (Classical.choose_spec binary_exists).1

/-- α₃ doubles to 1 -/
theorem α₃_double : α₃ + α₃ = 1 :=
  (Classical.choose_spec binary_exists).2

/-- α₃ is positive -/
theorem α₃_pos : 0 < α₃ := by
  rw [α₃_eq_half]
  norm_num

/-- α₃ is less than 1 -/
theorem α₃_lt_one : α₃ < 1 := by
  rw [α₃_eq_half]
  norm_num

/-- α₃ squared equals 1/4 -/
theorem α₃_sq : α₃^2 = 1/4 := by
  rw [α₃_eq_half]
  norm_num

/-- Two times α₃ equals 1 -/
theorem two_α₃ : 2 * α₃ = 1 := by
  have h := α₃_double
  linarith

/-- α₃ is the multiplicative inverse of 2 -/
theorem α₃_inv_two : α₃ = 1 / 2 := α₃_eq_half

/-- α₃ equals 1/2 (alias for compatibility) -/
theorem α₃_value : α₃ = 1/2 := α₃_eq_half

end PrimeOS12288.Constants
