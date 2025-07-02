/-
  Relations.UnityProduct - Unity product relationship
  
  This module proves that α₄ × α₅ = 1, which represents
  the Heisenberg uncertainty principle in our system.
-/

import Constants.Alpha4_Alpha5
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

namespace Relations

open Constants

theorem unity_product : α₄ * α₅ = 1 := by
  unfold α₄ α₅
  -- α₄ = 1/(2*π) and α₅ = 2*π
  -- We need to show: (1/(2*π)) * (2*π) = 1
  field_simp
  -- Now we need to show: (2*π) / (2*π) = 1
  apply div_self
  exact mul_ne_zero two_ne_zero (ne_of_gt π_pos)

end Relations