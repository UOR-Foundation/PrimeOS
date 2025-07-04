/-
  Constants.Alpha4_Alpha5 - Derived constants that encode π
  
  This module defines α₄ = 1/(2π) and α₅ = 2π, which are derived
  from the circular constant π.
-/

import Constants.Pi

namespace Constants

-- Derived constants that encode π
noncomputable def α₄ : ℝ := 1 / (2 * π)
noncomputable def α₅ : ℝ := 2 * π

theorem α₄_pos : 0 < α₄ := by
  unfold α₄
  exact div_pos one_pos (mul_pos two_pos π_pos)

theorem α₅_pos : 0 < α₅ := by
  unfold α₅
  exact mul_pos two_pos π_pos

end Constants