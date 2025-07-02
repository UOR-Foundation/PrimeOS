/-
  Relations.Ordering - Ordering relationships between field constants
  
  This module axiomatizes the numerical ordering of the field constants
  and proves derived properties.
-/

import Constants.All
import Properties.Positivity

namespace Relations

open Constants

-- Axiomatize the numerical ordering
axiom field_ordering : 
  α₇ < α₄ ∧ α₄ < α₆ ∧ α₆ < α₃ ∧ 
  α₃ < α₀ ∧ α₀ < α₂ ∧ α₂ < α₁ ∧ α₁ < α₅

theorem α₇_smallest : ∀ i : Fin 8, i ≠ 7 → α₇ < α i := by
  intro i hi
  match i with
  | ⟨0, _⟩ => -- α₇ < α₀
    have h1 := field_ordering.1 -- α₇ < α₄
    have h2 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h3 := field_ordering.2.2.1 -- α₆ < α₃
    have h4 := field_ordering.2.1 -- α₄ < α₆
    exact h1.trans (h4.trans (h3.trans h2))
  | ⟨1, _⟩ => -- α₇ < α₁
    have h1 := field_ordering.1 -- α₇ < α₄
    have h2 := field_ordering.2.2.2.2.2.1 -- α₂ < α₁
    have h3 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    have h4 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h5 := field_ordering.2.2.1 -- α₆ < α₃
    have h6 := field_ordering.2.1 -- α₄ < α₆
    exact h1.trans (h6.trans (h5.trans (h4.trans (h3.trans h2))))
  | ⟨2, _⟩ => -- α₇ < α₂
    have h1 := field_ordering.1 -- α₇ < α₄
    have h2 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    have h3 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h4 := field_ordering.2.2.1 -- α₆ < α₃
    have h5 := field_ordering.2.1 -- α₄ < α₆
    exact h1.trans (h5.trans (h4.trans (h3.trans h2)))
  | ⟨3, _⟩ => -- α₇ < α₃
    have h1 := field_ordering.1 -- α₇ < α₄
    have h2 := field_ordering.2.2.1 -- α₆ < α₃
    have h3 := field_ordering.2.1 -- α₄ < α₆
    exact h1.trans (h3.trans h2)
  | ⟨4, _⟩ => -- α₇ < α₄
    exact field_ordering.1
  | ⟨5, _⟩ => -- α₇ < α₅
    have h1 := field_ordering.1 -- α₇ < α₄
    have h2 := field_ordering.2.2.2.2.2.2 -- α₁ < α₅
    have h3 := field_ordering.2.2.2.2.2.1 -- α₂ < α₁
    have h4 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    have h5 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h6 := field_ordering.2.2.1 -- α₆ < α₃
    have h7 := field_ordering.2.1 -- α₄ < α₆
    exact h1.trans (h7.trans (h6.trans (h5.trans (h4.trans (h3.trans h2)))))
  | ⟨6, _⟩ => -- α₇ < α₆
    have h1 := field_ordering.1 -- α₇ < α₄
    have h2 := field_ordering.2.1 -- α₄ < α₆
    exact h1.trans h2
  | ⟨7, _⟩ => -- This case is excluded by hi
    exact absurd rfl hi

theorem α₅_largest : ∀ i : Fin 8, i ≠ 5 → α i < α₅ := by
  intro i hi
  match i with
  | ⟨0, _⟩ => -- α₀ < α₅
    have h1 := field_ordering.2.2.2.2.2.2 -- α₁ < α₅
    have h2 := field_ordering.2.2.2.2.2.1 -- α₂ < α₁
    have h3 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    exact h3.trans (h2.trans h1)
  | ⟨1, _⟩ => -- α₁ < α₅
    exact field_ordering.2.2.2.2.2.2
  | ⟨2, _⟩ => -- α₂ < α₅
    have h1 := field_ordering.2.2.2.2.2.2 -- α₁ < α₅
    have h2 := field_ordering.2.2.2.2.2.1 -- α₂ < α₁
    exact h2.trans h1
  | ⟨3, _⟩ => -- α₃ < α₅
    have h1 := field_ordering.2.2.2.2.2.2 -- α₁ < α₅
    have h2 := field_ordering.2.2.2.2.2.1 -- α₂ < α₁
    have h3 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    have h4 := field_ordering.2.2.2.1 -- α₃ < α₀
    exact h4.trans (h3.trans (h2.trans h1))
  | ⟨4, _⟩ => -- α₄ < α₅
    have h1 := field_ordering.2.2.2.2.2.2 -- α₁ < α₅
    have h2 := field_ordering.2.2.2.2.2.1 -- α₂ < α₁
    have h3 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    have h4 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h5 := field_ordering.2.2.1 -- α₆ < α₃
    have h6 := field_ordering.2.1 -- α₄ < α₆
    exact h6.trans (h5.trans (h4.trans (h3.trans (h2.trans h1))))
  | ⟨5, _⟩ => -- This case is excluded by hi
    exact absurd rfl hi
  | ⟨6, _⟩ => -- α₆ < α₅
    have h1 := field_ordering.2.2.2.2.2.2 -- α₁ < α₅
    have h2 := field_ordering.2.2.2.2.2.1 -- α₂ < α₁
    have h3 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    have h4 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h5 := field_ordering.2.2.1 -- α₆ < α₃
    exact h5.trans (h4.trans (h3.trans (h2.trans h1)))
  | ⟨7, _⟩ => -- α₇ < α₅
    -- We need to show α₇ < α₅
    -- We know α₇ is the smallest, so α₇ < α i for all i ≠ 7
    -- But we can't directly use α₇_smallest 5 because it expects 5 ≠ 7
    -- Let's build the chain: α₇ < α₄ < ... < α₅
    have h1 := field_ordering.1 -- α₇ < α₄
    have h2 := field_ordering.2.1 -- α₄ < α₆
    have h3 := field_ordering.2.2.1 -- α₆ < α₃
    have h4 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h5 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    have h6 := field_ordering.2.2.2.2.2.1 -- α₂ < α₁
    have h7 := field_ordering.2.2.2.2.2.2 -- α₁ < α₅
    exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))

end Relations