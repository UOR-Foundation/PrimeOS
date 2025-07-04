/-
  Properties.Positivity - All field constants are positive
  
  This module proves that all 8 field constants are positive real numbers.
-/

import Constants.All

namespace Properties

open Constants

theorem all_positive : ∀ i : Fin 8, 0 < α i := by
  intro i
  match i with
  | ⟨0, _⟩ => -- α 0 = α₀ = 1
    show 0 < α 0
    simp only [α]
    exact α₀_eq_one ▸ one_pos
  | ⟨1, _⟩ => -- α 1 = α₁ (tribonacci)
    show 0 < α 1
    simp only [α]
    exact zero_lt_one.trans α₁_gt_one
  | ⟨2, _⟩ => -- α 2 = α₂ (golden ratio)
    show 0 < α 2
    simp only [α]
    exact α₂_pos
  | ⟨3, _⟩ => -- α 3 = α₃ = 1/2
    show 0 < α 3
    simp only [α]
    rw [α₃_eq_half]
    norm_num
  | ⟨4, _⟩ => -- α 4 = α₄ = 1/(2π)
    show 0 < α 4
    simp only [α]
    exact α₄_pos
  | ⟨5, _⟩ => -- α 5 = α₅ = 2π
    show 0 < α 5
    simp only [α]
    exact α₅_pos
  | ⟨6, _⟩ => -- α 6 = α₆
    show 0 < α 6
    simp only [α]
    exact α₆_pos
  | ⟨7, _⟩ => -- α 7 = α₇
    show 0 < α 7
    simp only [α]
    exact α₇_pos

end Properties