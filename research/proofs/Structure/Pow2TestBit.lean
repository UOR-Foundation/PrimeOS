/-
  Structure.Pow2TestBit - Bit manipulation properties for powers of 2
  
  This module proves that 2^n has exactly one bit set at position n.
-/

import Basic.Types

namespace Structure

open Basic

/-
  Bit Manipulation Properties
  ---------------------------
  We prove that powers of 2 have exactly one bit set.
  This is a fundamental property needed for single field activation.
-/

-- Powers of 2 have exactly one bit set
theorem pow2_testBit (i j : Nat) : (2^i).testBit j = (i = j) := by
  -- Unfold the definition of testBit
  unfold Nat.testBit
  -- We need to show: ((2^i >>> j) % 2 = 1) = (i = j)
  -- This is a boolean equality, so we split cases
  by_cases h : i = j
  · -- Case: i = j
    rw [h]
    -- Show (2^j >>> j) % 2 = 1
    rw [Nat.shiftRight_eq_div_pow]
    -- 2^j / 2^j = 1
    have h_pos : 0 < 2^j := Nat.pow_pos (by omega : 0 < 2)
    rw [Nat.div_self h_pos]
    -- 1 % 2 = 1
    simp
  · -- Case: i ≠ j
    -- Show the boolean equality is false
    simp only [h]
    -- We need to show (2^i >>> j) % 2 = 1 is false
    rw [Nat.shiftRight_eq_div_pow]
    -- Consider two cases: i < j or j < i
    cases Nat.lt_or_ge i j with
    | inl hij =>
      -- i < j: Then 2^i < 2^j
      have h_lt : 2^i < 2^j := Nat.pow_lt_pow_right (by omega : 1 < 2) hij
      -- So 2^i / 2^j = 0
      have h_div : 2^i / 2^j = 0 := by
        apply Nat.div_eq_zero_iff.mpr
        constructor
        · exact h_lt
        · exact Nat.pow_pos (by omega : 0 < 2)
      rw [h_div]
      -- 0 % 2 = 0 ≠ 1
      simp
    | inr hji =>
      -- j ≤ i and j ≠ i, so j < i
      have hji' : j < i := by
        cases Nat.eq_or_lt_of_le hji with
        | inl heq => exact absurd heq.symm h
        | inr hlt => exact hlt
      -- Write i = j + (i - j) where i - j > 0
      have hi_eq : i = j + (i - j) := by
        rw [Nat.add_sub_of_le (Nat.le_of_lt hji')]
      rw [hi_eq, Nat.pow_add]
      -- (2^j * 2^(i-j)) / 2^j = 2^(i-j)
      have h_pos : 0 < 2^j := Nat.pow_pos (by omega : 0 < 2)
      rw [Nat.mul_div_cancel_left _ h_pos]
      -- 2^(i-j) is even when i - j > 0
      have h_sub_pos : 0 < i - j := Nat.sub_pos_of_lt hji'
      -- Write i - j = k + 1 for some k
      obtain ⟨k, hk⟩ : ∃ k, i - j = k + 1 := ⟨i - j - 1, by omega⟩
      rw [hk, Nat.pow_succ]
      -- (2 * 2^k) % 2 = 0
      have : 2 * 2^k % 2 = 0 := by
        rw [Nat.mul_comm]
        apply Nat.mul_mod_right
      rw [this]
      simp

end Structure