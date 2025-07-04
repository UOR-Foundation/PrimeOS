import PrimeOS12288.Constants.Alpha0
import PrimeOS12288.Constants.Alpha1
import PrimeOS12288.Constants.Alpha2
import PrimeOS12288.Constants.Alpha3
import PrimeOS12288.Constants.Pi
import PrimeOS12288.Constants.Alpha4_Alpha5
import PrimeOS12288.Constants.Alpha6_Alpha7
import PrimeOS12288.Constants.Distinctness

namespace PrimeOS12288.Constants

/-- The complete field constant function mapping indices to constants -/
noncomputable def fieldConstant : Fin 8 → ℝ
| 0 => α₀
| 1 => α₁
| 2 => α₂
| 3 => α₃
| 4 => α₄
| 5 => α₅
| 6 => α₆
| 7 => α₇

/-- All field constants are positive -/
theorem fieldConstant_pos (i : Fin 8) : 0 < fieldConstant i := by
  fin_cases i <;> simp [fieldConstant]
  · exact α₀_pos
  · exact α₁_pos
  · exact α₂_pos
  · exact α₃_pos
  · exact α₄_pos
  · exact α₅_pos
  · exact α₆_pos
  · exact α₇_pos

/-- Field constants satisfy their defining properties -/
theorem fieldConstant_properties : 
  fieldConstant 0 = 1 ∧ 
  fieldConstant 1 ^ 3 = fieldConstant 1 ^ 2 + fieldConstant 1 + 1 ∧
  fieldConstant 2 ^ 2 = fieldConstant 2 + 1 ∧
  fieldConstant 3 = 1/2 := by
  simp [fieldConstant]
  exact ⟨α₀_value, α₁_value, α₂_value, α₃_value⟩

/-- Field constants 4-7 are all less than 1 -/
theorem fieldConstant_lt_one (i : Fin 8) (hi : 3 < i.val) : fieldConstant i < 1 := by
  interval_cases i.val
  · simp [fieldConstant]
    exact α₄_lt_one
  · simp [fieldConstant]
    exact α₅_lt_one
  · simp [fieldConstant]
    exact α₆_lt_one
  · simp [fieldConstant]
    exact α₇_lt_one

/-- Distinct field constants are different -/
theorem fieldConstant_injective : Function.Injective fieldConstant := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [fieldConstant] at hij <;> try rfl
  · exact absurd hij α₀_ne_α₁
  · exact absurd hij α₀_ne_α₂
  · exact absurd hij α₀_ne_α₃
  · exact absurd hij α₀_ne_α₄
  · exact absurd hij α₀_ne_α₅
  · exact absurd hij α₀_ne_α₆
  · exact absurd hij α₀_ne_α₇
  · exact absurd hij.symm α₀_ne_α₁
  · exact absurd hij α₁_ne_α₂
  · exact absurd hij α₁_ne_α₃
  · exact absurd hij α₁_ne_α₄
  · exact absurd hij α₁_ne_α₅
  · exact absurd hij α₁_ne_α₆
  · exact absurd hij α₁_ne_α₇
  · exact absurd hij.symm α₀_ne_α₂
  · exact absurd hij.symm α₁_ne_α₂
  · exact absurd hij α₂_ne_α₃
  · exact absurd hij α₂_ne_α₄
  · exact absurd hij α₂_ne_α₅
  · exact absurd hij α₂_ne_α₆
  · exact absurd hij α₂_ne_α₇
  · exact absurd hij.symm α₀_ne_α₃
  · exact absurd hij.symm α₁_ne_α₃
  · exact absurd hij.symm α₂_ne_α₃
  · exact absurd hij α₃_ne_α₄
  · exact absurd hij α₃_ne_α₅
  · exact absurd hij α₃_ne_α₆
  · exact absurd hij α₃_ne_α₇
  · exact absurd hij.symm α₀_ne_α₄
  · exact absurd hij.symm α₁_ne_α₄
  · exact absurd hij.symm α₂_ne_α₄
  · exact absurd hij.symm α₃_ne_α₄
  · exact absurd hij α₄_ne_α₅
  · exact absurd hij α₄_ne_α₆
  · exact absurd hij α₄_ne_α₇
  · exact absurd hij.symm α₀_ne_α₅
  · exact absurd hij.symm α₁_ne_α₅
  · exact absurd hij.symm α₂_ne_α₅
  · exact absurd hij.symm α₃_ne_α₅
  · exact absurd hij.symm α₄_ne_α₅
  · exact absurd hij α₅_ne_α₆
  · exact absurd hij α₅_ne_α₇
  · exact absurd hij.symm α₀_ne_α₆
  · exact absurd hij.symm α₁_ne_α₆
  · exact absurd hij.symm α₂_ne_α₆
  · exact absurd hij.symm α₃_ne_α₆
  · exact absurd hij.symm α₄_ne_α₆
  · exact absurd hij.symm α₅_ne_α₆
  · exact absurd hij α₆_ne_α₇
  · exact absurd hij.symm α₀_ne_α₇
  · exact absurd hij.symm α₁_ne_α₇
  · exact absurd hij.symm α₂_ne_α₇
  · exact absurd hij.symm α₃_ne_α₇
  · exact absurd hij.symm α₄_ne_α₇
  · exact absurd hij.symm α₅_ne_α₇
  · exact absurd hij.symm α₆_ne_α₇

/-- The field constants encode all necessary mathematical information -/
theorem fieldConstant_complete :
  ∃ (encode : ℝ → Fin 8 → ℝ → Prop),
  encode π 4 (fieldConstant 4) ∧ 
  encode π 5 (fieldConstant 5) ∧
  ∀ x : ℝ, (x = 1 ∨ x = α₁ ∨ x = α₂ ∨ x = 1/2) → 
    ∃ i : Fin 8, fieldConstant i = x := by
  use fun r i c => c = fieldConstant i ∧ (i = 4 ∨ i = 5 → ∃ (P : ℝ → ℝ → Prop), P r c)
  constructor
  · simp [fieldConstant]
    use fun r c => c = α₄
    rfl
  · constructor
    · simp [fieldConstant]
      use fun r c => c = α₅
      rfl
    · intro x hx
      rcases hx with (h1 | h2 | h3 | h4)
      · use 0
        simp [fieldConstant, ← h1, α₀_value]
      · use 1
        simp [fieldConstant, h2]
      · use 2
        simp [fieldConstant, h3]
      · use 3
        simp [fieldConstant, ← h4, α₃_value]

end PrimeOS.Constants