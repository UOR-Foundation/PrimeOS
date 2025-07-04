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

-- Helper: x * n % x = 0
private theorem mul_mod_self_left (x n : Nat) : n * x % x = 0 := by
  cases x with
  | zero => simp
  | succ x' => 
    apply Nat.mod_eq_zero_of_dvd
    apply Nat.dvd_mul_left

-- Helper: if a < b then a / b = 0
private theorem div_eq_zero_of_lt {a b : Nat} (h : a < b) : a / b = 0 := by
  cases b with
  | zero => cases h
  | succ b' =>
    apply Nat.div_eq_of_lt h

-- Powers of 2 have exactly one bit set
theorem pow2_testBit (i j : Nat) : Basic.Nat.testBit (2^i) j = decide (i = j) := by
  -- Unfold the definition of testBit
  unfold Basic.Nat.testBit
  -- Split on whether i = j
  by_cases h : i = j
  · -- Case: i = j
    subst h
    -- Show (2^i >>> i) % 2 = 1 = true and decide (i = i) = true
    simp only []
    rw [Nat.shiftRight_eq_div_pow]
    -- 2^i / 2^i = 1
    have h_pos : 0 < 2^i := Nat.pow_pos (by decide : 0 < 2)
    rw [Nat.div_self h_pos]
    -- 1 % 2 = 1
    decide
  · -- Case: i ≠ j
    -- We need to show ((2^i >>> j) % 2 = 1) = false = decide (i = j)
    simp only [h]
    -- First show (2^i >>> j) % 2 = 0
    have h_eq_zero : (2^i >>> j) % 2 = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      -- Split on whether i < j or j < i
      cases Nat.lt_or_ge i j with
      | inl hij =>
        -- i < j: Then 2^i < 2^j
        have h_lt : 2^i < 2^j := Nat.pow_lt_pow_right (by decide : 1 < 2) hij
        -- So 2^i / 2^j = 0
        rw [div_eq_zero_of_lt h_lt]
      | inr hji =>
        -- j ≤ i and j ≠ i, so j < i
        have hji' : j < i := Nat.lt_of_le_of_ne hji (Ne.symm h)
        -- Write i = j + (i - j)
        have hi_eq : i = j + (i - j) := by
          omega
        rw [hi_eq, Nat.pow_add]
        -- (2^j * 2^(i-j)) / 2^j = 2^(i-j)
        have h_pos : 0 < 2^j := Nat.pow_pos (by decide : 0 < 2)
        rw [Nat.mul_div_cancel_left _ h_pos]
        -- 2^(i-j) is even when i - j > 0
        have h_sub_pos : 0 < i - j := Nat.sub_pos_of_lt hji'
        -- Write i - j = k + 1 for some k
        obtain ⟨k, hk⟩ : ∃ k, i - j = k + 1 := ⟨i - j - 1, by omega⟩
        rw [hk, Nat.pow_succ]
        -- 2^k * 2 % 2 = 0
        exact mul_mod_self_left 2 (2^k)
    -- Now show that (0 = 1) = false
    rw [h_eq_zero]
    simp

end Structure