/-
  Relations.PiEncoding - π encoding relationships
  
  This module proves relationships showing how π is encoded
  through combinations of field constants.
-/

import Constants.Alpha3
import Constants.Alpha4_Alpha5
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Relations

open Constants

theorem pi_encoding : α₃ * α₅ = π := by
  rw [α₃_eq_half, α₅]
  -- 1/2 * (2*π) = π
  ring

theorem pi_encoding_alt : α₃ / α₄ = π := by
  rw [α₃_eq_half, α₄]
  -- (1/2) / (1/(2*π)) = π
  field_simp

end Relations