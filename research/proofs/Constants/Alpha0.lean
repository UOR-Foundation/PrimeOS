/-
  Constants.Alpha0 - The identity constant
  
  This module extracts the identity constant from the unity axiom
  and proves its fundamental properties.
-/

import Axioms.Unity

namespace Constants

open Classical

-- The identity constant
noncomputable def α₀ : ℝ := choose Axioms.Unity.unity_exists

theorem α₀_eq_one : α₀ = 1 := 
  (choose_spec Axioms.Unity.unity_exists).1

theorem α₀_identity : ∀ x : ℝ, α₀ * x = x ∧ x * α₀ = x :=
  (choose_spec Axioms.Unity.unity_exists).2

end Constants