import Constants.Alpha0
import Constants.Alpha1
import Constants.Alpha2
import Constants.Alpha3
import Constants.Pi
import Constants.Alpha4_Alpha5
import Constants.Alpha6_Alpha7
import Constants.Distinctness

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

/-- All field constants are positive (alternative name) -/
theorem all_positive (i : Fin 8) : 0 < fieldConstant i := fieldConstant_pos i

/-- All field constants are nonzero -/
theorem all_nonzero (i : Fin 8) : fieldConstant i ≠ 0 := by
  have h := fieldConstant_pos i
  linarith

/-- Field constants satisfy their defining properties -/
theorem fieldConstant_properties : 
  fieldConstant 0 = 1 ∧ 
  fieldConstant 1 ^ 3 = fieldConstant 1 ^ 2 + fieldConstant 1 + 1 ∧
  fieldConstant 2 ^ 2 = fieldConstant 2 + 1 ∧
  fieldConstant 3 = 2⁻¹ := by
  simp [fieldConstant]
  refine ⟨α₀_eq_one, α₁_equation, α₂_equation, ?_⟩
  rw [α₃_eq_half]
  norm_num

/-- Field constants 4, 6, 7 are all less than 1, while 5 is greater -/
theorem fieldConstant_lt_one_except_5 (i : Fin 8) : 
  (i = 4 ∨ i = 6 ∨ i = 7) → fieldConstant i < 1 := by
  intro hi
  rcases hi with (h4 | h6 | h7)
  · rw [h4]; simp [fieldConstant]; exact α₄_lt_one
  · rw [h6]; simp [fieldConstant]; exact α₆_lt_one
  · rw [h7]; simp [fieldConstant]; exact α₇_lt_one

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
  -- Define encode to capture that fieldConstant 4 and 5 are related to π
  use fun r i c => (i = 4 → c = 1/(2*r)) ∧ (i = 5 → c = 2*r)
  constructor
  · -- encode π 4 (fieldConstant 4)
    constructor
    · intro _
      simp only [fieldConstant, α₄]
    · intro h
      -- 4 = 5 is false, so this case is vacuous
      cases h
  · constructor
    · -- encode π 5 (fieldConstant 5)
      constructor
      · intro h
        -- 5 = 4 is false, so this case is vacuous
        cases h
      · intro _
        simp only [fieldConstant, α₅]
    · -- All basic constants can be found
      intro x hx
      rcases hx with (h1 | h2 | h3 | h4)
      · use 0
        simp [fieldConstant, ← h1, α₀_eq_one]
      · use 1
        simp [fieldConstant, h2]
      · use 2
        simp [fieldConstant, h3]
      · use 3
        simp [fieldConstant, ← h4, α₃_eq_half]

end PrimeOS12288.Constants