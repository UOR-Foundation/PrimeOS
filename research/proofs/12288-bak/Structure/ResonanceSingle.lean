/-
  Structure.ResonanceSingle - Single field activation theorem
  
  When only one field is activated (at position 2^i), the resonance equals α_i.
-/

import Structure.FieldActivation
import Structure.ActivatedFieldsSpec
import Structure.Pow2TestBit

namespace Structure

open Basic Constants

-- Helper: 2^i < 12288 for i < 8
private lemma pow2_bound (i : Fin 8) : 2^i.val < 12288 := by
  have h1 : i.val < 8 := i.isLt
  have h2 : 2^i.val < 2^8 := by
    -- Use monotonicity of pow for base 2
    apply Nat.pow_lt_pow_right
    · norm_num  -- 1 < 2
    · exact h1  -- i.val < 8
  have h3 : 2^8 = 256 := by norm_num
  have h4 : 256 < 12288 := by norm_num
  calc 2^i.val < 2^8 := h2
  _ = 256 := h3
  _ < 12288 := h4

-- Helper: The filtered list for 2^i contains exactly [i]
private lemma filtered_singleton (i : Fin 8) :
  (List.finRange 8).filter (fun j => (2^i.val).testBit j.val) = [i] := by
  -- We'll show that j is in the filtered list iff j = i
  ext j
  simp only [List.mem_filter, List.mem_singleton, List.mem_finRange]
  constructor
  · -- If j is in filtered list, then j = i
    intro ⟨_, htest⟩
    -- j.val < 8 and (2^i.val).testBit j.val
    -- By pow2_testBit, this means i.val = j.val
    rw [pow2_testBit] at htest
    ext
    exact htest.symm
  · -- If j = i, then j is in filtered list
    intro hj
    rw [hj]
    constructor
    · exact i.isLt
    · rw [pow2_testBit]

-- Main theorem: single field activation
theorem resonance_single (i : Fin 8) :
  resonance ⟨2^i.val, pow2_bound i⟩ = α i := by
  simp [resonance, activated_fields]
  rw [filtered_singleton]
  simp

end Structure