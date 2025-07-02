/-
  Relations.Distinctness - All field constants are distinct
  
  This module proves that all field constants have different values,
  using the ordering relations.
-/

import Relations.Ordering
import Mathlib.Tactic.FinCases

namespace Relations

open Constants

/-
  Strategy: We have the ordering α₇ < α₄ < α₆ < α₃ < α₀ < α₂ < α₁ < α₅
  
  We prove distinctness by showing that for each pair i ≠ j, we have α i ≠ α j.
  We use the ordering to establish α i < α j or α j < α i, then apply ne_of_lt or ne_of_gt.
-/

-- Helper lemma: if a < b then a ≠ b
private lemma ne_of_lt {a b : ℝ} (h : a < b) : a ≠ b := by
  intro heq
  rw [heq] at h
  exact lt_irrefl _ h

-- Helper lemma: if a < b then b ≠ a
private lemma ne_of_gt {a b : ℝ} (h : a < b) : b ≠ a := by
  intro heq
  rw [← heq] at h
  exact lt_irrefl _ h

-- Main theorem: all field constants are distinct
theorem all_distinct : ∀ i j : Fin 8, i ≠ j → α i ≠ α j := by
  intro i j hij
  -- We'll prove by establishing an ordering between α i and α j
  -- The ordering is: α₇ < α₄ < α₆ < α₃ < α₀ < α₂ < α₁ < α₅
  
  -- First handle the special cases with 7 and 5
  by_cases h7i : i = 7
  · -- i = 7, so α i = α₇ which is smallest
    subst h7i
    have : j ≠ 7 := fun h => hij (by rw [h])
    exact ne_of_lt (α₇_smallest j this)
  
  by_cases h7j : j = 7
  · -- j = 7, so α j = α₇ which is smallest
    subst h7j
    exact ne_of_gt (α₇_smallest i h7i)
  
  by_cases h5i : i = 5
  · -- i = 5, so α i = α₅ which is largest
    subst h5i
    have : j ≠ 5 := fun h => hij (by rw [h])
    exact ne_of_gt (α₅_largest j this)
  
  by_cases h5j : j = 5
  · -- j = 5, so α j = α₅ which is largest
    subst h5j
    exact ne_of_lt (α₅_largest i h5i)
  
  -- Now we know i, j ∈ {0, 1, 2, 3, 4, 6}
  -- The ordering among {0,1,2,3,4,6} is: α₄ < α₆ < α₃ < α₀ < α₂ < α₁
  
  -- We'll use fin_cases to handle all remaining possibilities
  fin_cases i <;> fin_cases j
  -- All cases where i = j are contradictions
  all_goals (first | exact absurd rfl hij | skip)
  -- All cases where j = 5 or j = 7 contradict our assumptions
  all_goals (first | exact absurd rfl h5j | exact absurd rfl h7j | skip)
  -- All cases where i = 5 or i = 7 contradict our assumptions  
  all_goals (first | exact absurd rfl h5i | exact absurd rfl h7i | skip)
  
  -- Now handle the remaining cases systematically
  -- Case i = 0, j = 1: α₀ < α₁
  · simp only [α]
    exact ne_of_lt (field_ordering.2.2.2.2.1.trans field_ordering.2.2.2.2.2.1)
  -- Case i = 0, j = 2: α₀ < α₂
  · simp only [α]
    exact ne_of_lt field_ordering.2.2.2.2.1
  -- Case i = 0, j = 3: α₃ < α₀
  · simp only [α]
    exact ne_of_gt field_ordering.2.2.2.1
  -- Case i = 0, j = 4: α₄ < α₀
  · simp only [α]
    have h1 := field_ordering.2.1 -- α₄ < α₆
    have h2 := field_ordering.2.2.1 -- α₆ < α₃
    have h3 := field_ordering.2.2.2.1 -- α₃ < α₀
    exact ne_of_gt (h1.trans (h2.trans h3))
  -- Case i = 0, j = 6: α₆ < α₀
  · simp only [α]
    have h1 := field_ordering.2.2.1 -- α₆ < α₃
    have h2 := field_ordering.2.2.2.1 -- α₃ < α₀
    exact ne_of_gt (h1.trans h2)
  
  -- Case i = 1, j = 0: α₀ < α₁
  · simp only [α]
    exact ne_of_gt (field_ordering.2.2.2.2.1.trans field_ordering.2.2.2.2.2.1)
  -- Case i = 1, j = 2: α₂ < α₁
  · simp only [α]
    exact ne_of_gt field_ordering.2.2.2.2.2.1
  -- Case i = 1, j = 3: α₃ < α₁
  · simp only [α]
    have h1 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h2 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    have h3 := field_ordering.2.2.2.2.2.1 -- α₂ < α₁
    exact ne_of_gt (h1.trans (h2.trans h3))
  -- Case i = 1, j = 4: α₄ < α₁
  · simp only [α]
    have h1 := field_ordering.2.1 -- α₄ < α₆
    have h2 := field_ordering.2.2.1 -- α₆ < α₃
    have h3 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h4 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    have h5 := field_ordering.2.2.2.2.2.1 -- α₂ < α₁
    exact ne_of_gt (h1.trans (h2.trans (h3.trans (h4.trans h5))))
  -- Case i = 1, j = 6: α₆ < α₁
  · simp only [α]
    have h1 := field_ordering.2.2.1 -- α₆ < α₃
    have h2 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h3 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    have h4 := field_ordering.2.2.2.2.2.1 -- α₂ < α₁
    exact ne_of_gt (h1.trans (h2.trans (h3.trans h4)))
  
  -- Case i = 2, j = 0: α₀ < α₂
  · simp only [α]
    exact ne_of_gt field_ordering.2.2.2.2.1
  -- Case i = 2, j = 1: α₂ < α₁
  · simp only [α]
    exact ne_of_lt field_ordering.2.2.2.2.2.1
  -- Case i = 2, j = 3: α₃ < α₂
  · simp only [α]
    have h1 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h2 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    exact ne_of_gt (h1.trans h2)
  -- Case i = 2, j = 4: α₄ < α₂
  · simp only [α]
    have h1 := field_ordering.2.1 -- α₄ < α₆
    have h2 := field_ordering.2.2.1 -- α₆ < α₃
    have h3 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h4 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    exact ne_of_gt (h1.trans (h2.trans (h3.trans h4)))
  -- Case i = 2, j = 6: α₆ < α₂
  · simp only [α]
    have h1 := field_ordering.2.2.1 -- α₆ < α₃
    have h2 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h3 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    exact ne_of_gt (h1.trans (h2.trans h3))
  
  -- Case i = 3, j = 0: α₃ < α₀
  · simp only [α]
    exact ne_of_lt field_ordering.2.2.2.1
  -- Case i = 3, j = 1: α₃ < α₁
  · simp only [α]
    have h1 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h2 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    have h3 := field_ordering.2.2.2.2.2.1 -- α₂ < α₁
    exact ne_of_lt (h1.trans (h2.trans h3))
  -- Case i = 3, j = 2: α₃ < α₂
  · simp only [α]
    have h1 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h2 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    exact ne_of_lt (h1.trans h2)
  -- Case i = 3, j = 4: α₄ < α₃
  · simp only [α]
    have h1 := field_ordering.2.1 -- α₄ < α₆
    have h2 := field_ordering.2.2.1 -- α₆ < α₃
    exact ne_of_gt (h1.trans h2)
  -- Case i = 3, j = 6: α₆ < α₃
  · simp only [α]
    exact ne_of_gt field_ordering.2.2.1
  
  -- Case i = 4, j = 0: α₄ < α₀
  · simp only [α]
    have h1 := field_ordering.2.1 -- α₄ < α₆
    have h2 := field_ordering.2.2.1 -- α₆ < α₃
    have h3 := field_ordering.2.2.2.1 -- α₃ < α₀
    exact ne_of_lt (h1.trans (h2.trans h3))
  -- Case i = 4, j = 1: α₄ < α₁
  · simp only [α]
    have h1 := field_ordering.2.1 -- α₄ < α₆
    have h2 := field_ordering.2.2.1 -- α₆ < α₃
    have h3 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h4 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    have h5 := field_ordering.2.2.2.2.2.1 -- α₂ < α₁
    exact ne_of_lt (h1.trans (h2.trans (h3.trans (h4.trans h5))))
  -- Case i = 4, j = 2: α₄ < α₂
  · simp only [α]
    have h1 := field_ordering.2.1 -- α₄ < α₆
    have h2 := field_ordering.2.2.1 -- α₆ < α₃
    have h3 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h4 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    exact ne_of_lt (h1.trans (h2.trans (h3.trans h4)))
  -- Case i = 4, j = 3: α₄ < α₃
  · simp only [α]
    have h1 := field_ordering.2.1 -- α₄ < α₆
    have h2 := field_ordering.2.2.1 -- α₆ < α₃
    exact ne_of_lt (h1.trans h2)
  -- Case i = 4, j = 6: α₄ < α₆
  · simp only [α]
    exact ne_of_lt field_ordering.2.1
  
  -- Case i = 6, j = 0: α₆ < α₀
  · simp only [α]
    have h1 := field_ordering.2.2.1 -- α₆ < α₃
    have h2 := field_ordering.2.2.2.1 -- α₃ < α₀
    exact ne_of_lt (h1.trans h2)
  -- Case i = 6, j = 1: α₆ < α₁
  · simp only [α]
    have h1 := field_ordering.2.2.1 -- α₆ < α₃
    have h2 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h3 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    have h4 := field_ordering.2.2.2.2.2.1 -- α₂ < α₁
    exact ne_of_lt (h1.trans (h2.trans (h3.trans h4)))
  -- Case i = 6, j = 2: α₆ < α₂
  · simp only [α]
    have h1 := field_ordering.2.2.1 -- α₆ < α₃
    have h2 := field_ordering.2.2.2.1 -- α₃ < α₀
    have h3 := field_ordering.2.2.2.2.1 -- α₀ < α₂
    exact ne_of_lt (h1.trans (h2.trans h3))
  -- Case i = 6, j = 3: α₆ < α₃
  · simp only [α]
    exact ne_of_lt field_ordering.2.2.1
  -- Case i = 6, j = 4: α₄ < α₆
  · simp only [α]
    exact ne_of_gt field_ordering.2.1

end Relations