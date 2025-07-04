import Mathlib.Data.Real.Basic

namespace PrimeOS12288.Constants

/-- The identity constant α₀ = 1 -/
def α₀ : ℝ := 1

/-- α₀ equals 1 -/
theorem α₀_value : α₀ = 1 := rfl

/-- α₀ is positive -/
theorem α₀_pos : 0 < α₀ := by
  simp [α₀]

/-- α₀ is the multiplicative identity -/
theorem α₀_mul_id (x : ℝ) : α₀ * x = x := by
  simp [α₀]

/-- α₀ raised to any power equals α₀ -/
theorem α₀_pow (n : ℕ) (hn : 0 < n) : α₀ ^ n = α₀ := by
  simp [α₀]

end PrimeOS12288.Constants