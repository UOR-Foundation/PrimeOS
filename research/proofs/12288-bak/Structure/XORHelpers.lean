/-
  Structure.XORHelpers - XOR operations and bit manipulation helpers
  
  This module provides basic XOR operations and bit manipulation lemmas
  used in the resonance count proof.
-/

import Basic.Nat
import Mathlib.Data.Nat.Bitwise

namespace Structure

open Basic

-- Helper: XOR operation on Fin 256
def xor256 (a b : Fin 256) : Fin 256 := ⟨a.val ^^^ b.val, by
  have h : a.val ^^^ b.val < 256 := by
    have ha : a.val < 256 := a.isLt
    have hb : b.val < 256 := b.isLt
    exact Nat.xor_lt_iff_lt_max.mpr (Or.inl ha)
  exact h⟩

-- Helper: bit 0 activation differs by XOR 1
lemma bit_0_xor_1 (n : Nat) : (n ^^^ 1).testBit 0 = !n.testBit 0 := by
  unfold Basic.Nat.testBit
  simp only [Nat.shiftRight_zero]
  rw [Nat.xor_mod_two_eq_one]
  by_cases h : n % 2 = 1 <;> simp [h]

-- Helper: other bits unchanged by XOR 1
lemma bit_i_xor_1 (n : Nat) (i : Nat) (hi : i ≠ 0) : (n ^^^ 1).testBit i = n.testBit i := by
  unfold Basic.Nat.testBit
  -- Key: (n ^^^ 1) >>> i = n >>> i for i > 0
  have h1 : 1 >>> i = 0 := by
    cases i with
    | zero => contradiction
    | succ j => simp [Nat.shiftRight_succ, Nat.shiftRight_zero]
  rw [Nat.shiftRight_xor, h1, Nat.xor_zero]

-- Helper: 48 = 2^4 + 2^5
lemma forty_eight_eq : 48 = 16 + 32 := by norm_num

-- Helper: XOR with 48 flips bits 4 and 5
lemma xor_48_bits (n : Nat) (i : Nat) :
  (n ^^^ 48).testBit i = if i = 4 || i = 5 then !n.testBit i else n.testBit i := by
  unfold Basic.Nat.testBit
  -- 48 = 0b00110000, so it has bits 4 and 5 set
  have h48 : ∀ j, (48 : Nat).testBit j ↔ (j = 4 ∨ j = 5) := by
    intro j
    unfold Basic.Nat.testBit
    cases j with
    | zero => simp [Nat.shiftRight_zero]
    | succ j => cases j with
      | zero => simp [Nat.shiftRight_one]
      | succ j => cases j with
        | zero => simp [Nat.shiftRight_succ, Nat.shiftRight_one]
        | succ j => cases j with
          | zero => simp [Nat.shiftRight_succ, Nat.shiftRight_one]
          | succ j => cases j with
            | zero => simp [Nat.shiftRight_succ, Nat.shiftRight_one]
            | succ j => cases j with
              | zero => simp [Nat.shiftRight_succ, Nat.shiftRight_one]
              | succ j => 
                -- For j ≥ 6, 48 >>> j = 0
                have : 48 >>> (j.succ.succ.succ.succ.succ.succ) = 0 := by
                  simp only [Nat.shiftRight_eq_div_pow]
                  norm_num
                simp [Basic.Nat.testBit, this]
  -- XOR flips the bit if the corresponding bit in 48 is set
  by_cases hi4 : i = 4
  · subst hi4; simp [h48, Nat.xor_bit]
  by_cases hi5 : i = 5  
  · subst hi5; simp [h48, Nat.xor_bit]
  · -- i ≠ 4 and i ≠ 5
    simp [hi4, hi5]
    rw [Nat.xor_bit, h48]
    simp [hi4, hi5]

end Structure