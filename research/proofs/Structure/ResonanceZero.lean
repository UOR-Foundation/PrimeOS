/-
  Structure.ResonanceZero - Resonance of position 0
  
  This module proves that the resonance at position 0 equals 1,
  since no fields are activated when all bits are 0.
-/

import Structure.FieldActivation

namespace Structure

open Basic Constants

-- Resonance of position 0 (no fields activated)
theorem resonance_zero : resonance 0 = 1 := by
  -- Unfold definitions
  unfold resonance activated_fields
  -- Simplify the coercion: (0 : Fin 12288).val = 0
  simp only [Fin.val_zero]
  -- Need to show the filtered list is empty
  have empty : (List.finRange 8).filter (fun i => (0 : Nat).testBit i.val) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro i
    simp only [List.mem_filter, List.mem_finRange, not_and]
    intro _
    -- 0.testBit i = false for all i
    simp [Nat.testBit]
  rw [empty]
  -- Empty map and product give 1
  simp

end Structure