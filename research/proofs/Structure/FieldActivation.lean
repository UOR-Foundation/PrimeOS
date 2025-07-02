/-
  Structure.FieldActivation - Field activation and resonance computation
  
  This module defines how fields are activated based on binary representation
  and computes the resonance value for any position in the 12,288-element space.
-/

import Basic.Types
import Constants.All

namespace Structure

open Basic Constants

/-
  Core Definitions
  ----------------
  We define field activation based on binary representation of positions.
  Each bit position i (0 ≤ i < 8) activates field α_i when set.
-/

-- Field activation based on binary representation
def activated_fields (n : Fin 12288) : List (Fin 8) :=
  (List.finRange 8).filter (fun i => n.val.testBit i.val)

-- Resonance computation as product of activated fields
noncomputable def resonance (n : Fin 12288) : ℝ :=
  (activated_fields n).map α |>.prod

end Structure