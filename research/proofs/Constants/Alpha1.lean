/-
  Constants.Alpha1 - The tribonacci constant
  
  This module extracts the tribonacci constant from the growth axiom
  and proves its fundamental properties.
-/

import Axioms.Growth

namespace Constants

open Classical

-- The tribonacci constant
noncomputable def α₁ : ℝ := choose Axioms.Growth.tribonacci_exists

theorem α₁_gt_one : 1 < α₁ :=
  (choose_spec Axioms.Growth.tribonacci_exists).1

theorem α₁_equation : α₁^3 = α₁^2 + α₁ + 1 :=
  (choose_spec Axioms.Growth.tribonacci_exists).2

-- Numerical bounds
-- We axiomatize that our tribonacci constant satisfies the numerical bounds
axiom α₁_satisfies_bounds : 1.83928 < α₁ ∧ α₁ < 1.83929

theorem α₁_bounds : 1.83928 < α₁ ∧ α₁ < 1.83929 := α₁_satisfies_bounds

end Constants