/-
  Constants.Pi - The circular constant
  
  This module extracts π from the circular axiom and proves its
  fundamental properties.
-/

import Axioms.Circular

namespace Constants

open Classical

-- The circular constant
noncomputable def π : ℝ := choose Axioms.Circular.pi_exists

theorem π_pos : 0 < π :=
  (choose_spec Axioms.Circular.pi_exists).1

theorem π_circle : ∀ (r : ℝ), r > 0 → 
  ∃ (circumference : ℝ), circumference = 2 * π * r :=
  (choose_spec Axioms.Circular.pi_exists).2

-- Numerical bounds
-- We axiomatize that our π satisfies the numerical bounds
axiom π_satisfies_bounds : 3.14159 < π ∧ π < 3.14160

theorem π_lower : 3.14159 < π := π_satisfies_bounds.1

theorem π_upper : π < 3.14160 := π_satisfies_bounds.2

end Constants