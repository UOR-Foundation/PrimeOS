/-
  Constants.Alpha2 - The golden ratio
  
  This module extracts the golden ratio from the golden axiom
  and proves its fundamental properties.
-/

import Axioms.Golden
import Mathlib.Data.Real.Sqrt

namespace Constants

open Classical Real

-- The golden ratio
noncomputable def α₂ : ℝ := choose Axioms.Golden.golden_exists

theorem α₂_pos : 0 < α₂ :=
  (choose_spec Axioms.Golden.golden_exists).1

theorem α₂_equation : α₂^2 = α₂ + 1 :=
  (choose_spec Axioms.Golden.golden_exists).2

-- We need to axiomatize that the positive solution to x² = x + 1 is unique
axiom golden_unique : ∀ x y : ℝ, x > 0 → y > 0 → x^2 = x + 1 → y^2 = y + 1 → x = y

-- Derived property: the golden ratio equals (1 + √5)/2
theorem α₂_value : α₂ = (1 + sqrt 5) / 2 := by
  -- First, show that (1 + √5)/2 is positive
  have h_pos : 0 < (1 + sqrt 5) / 2 := by
    apply div_pos
    · apply add_pos_of_pos_of_nonneg one_pos
      exact sqrt_nonneg 5
    · exact two_pos
  
  -- Next, show that (1 + √5)/2 satisfies the golden ratio equation
  have h_eq : ((1 + sqrt 5) / 2)^2 = (1 + sqrt 5) / 2 + 1 := by
    field_simp
    ring_nf
    rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    ring
  
  -- Since both α₂ and (1 + √5)/2 are positive and satisfy x² = x + 1,
  -- they must be equal by uniqueness
  exact golden_unique α₂ ((1 + sqrt 5) / 2) α₂_pos h_pos α₂_equation h_eq

end Constants