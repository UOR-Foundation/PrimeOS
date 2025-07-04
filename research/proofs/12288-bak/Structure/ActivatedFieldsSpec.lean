/-
  Structure.ActivatedFieldsSpec - Membership characterization for activated fields
  
  This module provides the key characterization theorem for field activation.
-/

import Structure.FieldActivation

namespace Structure

open Basic Constants

-- Helper: activated fields membership characterization
theorem activated_fields_spec (n : Fin 12288) (i : Fin 8) :
  i ∈ activated_fields n ↔ n.val.testBit i.val := by
  simp [activated_fields, List.mem_filter, List.mem_finRange]

-- Resonance depends only on activated fields  
theorem resonance_characterization (n : Fin 12288) :
  resonance n = List.prod (List.map α ((List.finRange 8).filter (fun i => n.val.testBit i.val))) := by
  rfl

-- Empty activation gives resonance 1
theorem resonance_empty (n : Fin 12288) :
  activated_fields n = [] → resonance n = 1 := by
  intro h
  simp [resonance, h]

end Structure