import Axioms.System
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace PrimeOS12288.Constants

open PrimeOS12288.Axioms

/-- System-determined constant α₆ -/
noncomputable def α₆ : ℝ := Classical.choose system_constants_exist

/-- System-determined constant α₇ -/
noncomputable def α₇ : ℝ := Classical.choose (Classical.choose_spec system_constants_exist)

/-- The specification of system constants -/
theorem system_spec :
  α₆ = 0.19961197478400415 ∧
  α₇ = 0.014134725141734695 ∧
  0 < α₇ ∧ α₇ < α₆ ∧ α₆ < 1 := by
  have h1 := Classical.choose_spec system_constants_exist
  have h2 := Classical.choose_spec h1
  simp only [α₆, α₇] at h2 ⊢
  exact h2

/-- α₆ equals its specified value -/
theorem α₆_eq : α₆ = 0.19961197478400415 :=
  system_spec.1

/-- α₇ equals its specified value -/
theorem α₇_eq : α₇ = 0.014134725141734695 :=
  system_spec.2.1

/-- α₇ is positive -/
theorem α₇_pos : 0 < α₇ :=
  system_spec.2.2.1

/-- α₇ is less than α₆ -/
theorem α₇_lt_α₆ : α₇ < α₆ :=
  system_spec.2.2.2.1

/-- α₆ is less than 1 -/
theorem α₆_lt_one : α₆ < 1 :=
  system_spec.2.2.2.2

/-- α₆ is positive -/
theorem α₆_pos : 0 < α₆ := by
  linarith [α₇_pos, α₇_lt_α₆]

/-- α₆ is nonzero -/
theorem α₆_ne_zero : α₆ ≠ 0 :=
  ne_of_gt α₆_pos

/-- α₇ is nonzero -/
theorem α₇_ne_zero : α₇ ≠ 0 :=
  ne_of_gt α₇_pos

/-- α₇ is less than 1 -/
theorem α₇_lt_one : α₇ < 1 := by
  linarith [α₇_lt_α₆, α₆_lt_one]

/-- The ordering of system constants -/
theorem system_constants_order : 0 < α₇ ∧ α₇ < α₆ ∧ α₆ < 1 := by
  exact ⟨α₇_pos, α₇_lt_α₆, α₆_lt_one⟩

end PrimeOS12288.Constants