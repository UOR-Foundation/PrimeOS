import PrimeOS12288.Constants.All
import PrimeOS12288.Basic.Types

namespace PrimeOS12288.Properties

open PrimeOS12288.Constants

/-- All field constants are positive -/
theorem all_positive : ∀ i : FieldIndex, 0 < fieldConstant i := by
  intro i
  -- FieldIndex is Fin 8, so we can use fieldConstant_pos directly
  exact fieldConstant_pos i

/-- Alternative proof that explicitly handles each field constant -/
theorem all_positive_explicit : ∀ i : FieldIndex, 0 < fieldConstant i := by
  intro i
  fin_cases i <;> simp [fieldConstant]
  case mk _ 0 => exact α₀_pos
  case mk _ 1 => exact α₁_pos
  case mk _ 2 => exact α₂_pos
  case mk _ 3 => exact α₃_pos
  case mk _ 4 => exact α₄_pos
  case mk _ 5 => exact α₅_pos
  case mk _ 6 => exact α₆_pos
  case mk _ 7 => exact α₇_pos

/-- Field constant 0 (identity) equals 1, hence positive -/
theorem field0_eq_one : fieldConstant 0 = 1 := by
  simp [fieldConstant, α₀_eq_one]

/-- Field constant 1 (tribonacci) is greater than 1 -/
theorem field1_gt_one : 1 < fieldConstant 1 := by
  simp [fieldConstant]
  exact α₁_gt_one

/-- Field constant 2 (golden ratio) is positive -/
theorem field2_pos : 0 < fieldConstant 2 := by
  simp [fieldConstant]
  exact α₂_pos

/-- Field constant 3 equals 1/2, hence positive -/
theorem field3_eq_half : fieldConstant 3 = 1/2 := by
  simp [fieldConstant]
  exact α₃_eq_half

/-- Field constants 4-7 are positive but less than 1 -/
theorem field4_to_7_positive_lt_one (i : FieldIndex) (hi : 3 < i.val) : 
  0 < fieldConstant i ∧ fieldConstant i < 1 := by
  constructor
  · exact fieldConstant_pos i
  · exact fieldConstant_lt_one i hi

end PrimeOS12288.Properties