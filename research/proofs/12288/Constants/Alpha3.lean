import Mathlib.Data.Real.Basic

namespace PrimeOS12288.Constants

/-- The binary constant α₃ = 1/2 -/
def α₃ : ℝ := 1/2

/-- α₃ equals 1/2 -/
theorem α₃_value : α₃ = 1/2 := rfl

/-- α₃ is positive -/
theorem α₃_pos : 0 < α₃ := by
  simp [α₃]
  norm_num

/-- α₃ is less than 1 -/
theorem α₃_lt_one : α₃ < 1 := by
  simp [α₃]
  norm_num

/-- α₃ squared equals 1/4 -/
theorem α₃_sq : α₃^2 = 1/4 := by
  simp [α₃]
  norm_num

/-- Two times α₃ equals 1 -/
theorem two_α₃ : 2 * α₃ = 1 := by
  simp [α₃]
  norm_num

/-- α₃ is the multiplicative inverse of 2 -/
theorem α₃_inv_two : α₃ = 1 / 2 := rfl

end PrimeOS12288.Constants