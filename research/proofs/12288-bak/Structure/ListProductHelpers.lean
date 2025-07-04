/-
  Structure.ListProductHelpers - Helper lemmas for list products
  
  This module provides lemmas about products of lists, particularly
  when dealing with identity elements and list manipulations.
-/

import Mathlib.Data.List.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.BigOperators.List.Basic

namespace Structure

section ProductHelpers

-- Helper: Product of a list with one element removed
lemma list_prod_erase_of_mem {α : Type*} [CommMonoid α] (l : List α) (a : α) (h : a ∈ l) :
  l.prod = a * (l.erase a).prod := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    cases h with
    | inl h => 
      subst h
      simp [List.erase_cons_head]
    | inr h =>
      rw [List.prod_cons, List.erase_cons_tail]
      · rw [ih h, mul_comm x, mul_assoc]
      · intro heq
        subst heq
        exact h

-- Helper: Product doesn't change when multiplying by 1
lemma prod_mul_one {α : Type*} [CommMonoid α] (l : List α) :
  l.prod * 1 = l.prod := by simp

-- Helper: If we add element 1 to a list, the product doesn't change
lemma list_prod_cons_one {α : Type*} [CommMonoid α] (l : List α) (one : α) (h : one = 1) :
  (one :: l).prod = l.prod := by
  rw [List.prod_cons, h, one_mul]

-- Helper: Removing element 1 from a list doesn't change the product
lemma list_prod_erase_one {α : Type*} [CommMonoid α] (l : List α) (one : α) 
  (h_one : one = 1) (h_mem : one ∈ l) :
  l.prod = (l.erase one).prod := by
  rw [list_prod_erase_of_mem l one h_mem, h_one, one_mul]

-- Helper: Product of two lists where corresponding elements multiply to 1
lemma prod_mul_prod_eq_one {α : Type*} [CommMonoid α] (l1 l2 : List α) 
  (h_len : l1.length = l2.length)
  (h_mul : ∀ i : Fin l1.length, l1[i] * l2[i.cast h_len] = 1) :
  l1.prod * l2.prod = 1 := by
  induction l1 generalizing l2 with
  | nil => 
    cases l2 with
    | nil => simp
    | cons _ _ => simp at h_len
  | cons x xs ih =>
    cases l2 with
    | nil => simp at h_len
    | cons y ys =>
      simp only [List.prod_cons]
      rw [mul_comm x, mul_assoc, mul_comm (xs.prod * x), mul_assoc]
      rw [mul_comm y, mul_assoc]
      -- Now we have (x * y) * (xs.prod * ys.prod)
      have h0 : x * y = 1 := by
        have : x = l1[0] := by simp
        have : y = l2[0] := by simp
        rw [this, this]
        exact h_mul 0
      rw [h0, one_mul]
      apply ih
      · simp at h_len ⊢; exact h_len
      · intro i
        have : xs[i] = l1[i.succ] := by simp
        have : ys[i.cast (by simp at h_len ⊢; exact h_len)] = l2[i.succ.cast h_len] := by
          simp
        rw [this, this]
        exact h_mul i.succ

end ProductHelpers

end Structure