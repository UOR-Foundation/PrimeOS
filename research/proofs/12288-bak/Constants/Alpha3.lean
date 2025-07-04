/-
  Constants.Alpha3 - The binary constant (one-half)
  
  This module extracts the binary constant 1/2 from the binary axiom
  and proves its fundamental properties.
-/

import Axioms.Binary

namespace Constants

open Classical

-- The binary constant (one-half)
noncomputable def α₃ : ℝ := choose Axioms.Binary.binary_exists

theorem α₃_eq_half : α₃ = 1/2 :=
  (choose_spec Axioms.Binary.binary_exists).1

theorem α₃_double : α₃ + α₃ = 1 :=
  (choose_spec Axioms.Binary.binary_exists).2

end Constants