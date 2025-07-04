/-!
# Concrete Implementation of Bit Arithmetic Basic

This file provides the concrete implementation of the BitArithmetic.Basic class,
establishing the bit manipulation properties needed for the proof system.
-/

import PrimeOS12288.BitArithmetic.Basic
import PrimeOS12288.Computational.FoundationImpl
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Bool.Basic

namespace PrimeOS12288.BitArithmetic

open PrimeOS12288 PrimeOS12288.Computational

/-- The concrete Basic instance for bit arithmetic properties -/
instance : Basic where
  -- Bit testing equivalence with division and modulo
  testBit_eq_one_iff := by
    intro n i
    exact Nat.testBit_eq_one_iff n i
  
  -- Bit is false if number is less than power of 2
  testBit_eq_false_of_lt := by
    intro n i h
    exact Nat.testBit_eq_false_of_lt h
  
  -- Key decomposition for 8-bit values using bits 4 and 5
  nat_decompose_bits_4_5 := by
    intro n h
    -- n = bits[0..3] + bits[4..5] * 16 + bits[6..7] * 64
    have h1 : n = n % 16 + (n / 16) % 4 * 16 + (n / 64) % 4 * 64 + (n / 256) * 256 := by
      conv_lhs => rw [← Nat.div_add_mod n 256]
      conv_rhs => rw [← Nat.div_add_mod n 16]
      conv_rhs => arg 2; rw [← Nat.div_add_mod (n / 16) 4]
      conv_rhs => arg 2; arg 2; rw [← Nat.div_add_mod (n / 64) 4]
      ring
    -- Since n < 256, we have n / 256 = 0
    have h2 : n / 256 = 0 := Nat.div_eq_zero_of_lt h
    rw [h1, h2, mul_zero, add_zero]
    -- Now simplify (n / 64) % 4 * 64 to (n / 64) * 64
    have h3 : n / 64 < 4 := by
      calc n / 64 < 256 / 64 := Nat.div_lt_div_of_lt_left h (by norm_num : 0 < 64)
      _ = 4 := by norm_num
    rw [Nat.mod_eq_of_lt h3]
  
  -- XOR bit testing property
  xor_testBit := by
    intro a b i
    exact Nat.xor_testBit a b i
  
  -- Bit 4 and 5 extraction
  bits_4_5_eq_div_16_mod_4 := by
    intro n h
    constructor
    · -- For bit 4: n.testBit 4 = (n / 16) % 2 = 1
      rw [Nat.testBit_eq_one_iff]
      simp only [pow_four, Nat.div_div_eq_div_mul]
      rfl
    · -- For bit 5: n.testBit 5 = (n / 32) % 2 = 1
      rw [Nat.testBit_eq_one_iff]
      simp only [pow_five, Nat.div_div_eq_div_mul]
      rfl

/-! ## Verification lemmas for bit arithmetic -/

/-- Verify XOR preserves byte bounds -/
theorem xor_byte_bound (a b : ByteValue) : a.val ^^^ b.val < ByteSize := by
  have ha : a.val < ByteSize := a.isLt
  have hb : b.val < ByteSize := b.isLt
  simp [ByteSize] at ha hb ⊢
  apply Nat.xor_lt_iff_lt_max.mpr
  exact Or.inl ha

/-- Complete the proof for xorBytes -/
theorem xorBytes_valid (a b : ByteValue) : 
  (xorBytes a b).val = a.val ^^^ b.val := by
  simp [xorBytes]
  rfl

/-- Verify XOR preserves position bounds when both positions are in same page -/
theorem xor_position_bound_same_page (a b : Position) 
  (ha : a.val < PageSize) (hb : b.val < PageSize) : 
  a.val ^^^ b.val < TotalSize := by
  have h_xor : a.val ^^^ b.val < PageSize := by
    apply Nat.xor_lt_iff_lt_max.mpr
    exact Or.inl ha
  calc a.val ^^^ b.val < PageSize := h_xor
  _ < TotalSize := by norm_num [PageSize, TotalSize]

/-- Helper: XOR of two numbers less than 2^k is also less than 2^k -/
theorem xor_lt_two_pow (a b k : ℕ) (ha : a < 2^k) (hb : b < 2^k) : 
  a ^^^ b < 2^k := by
  -- Use the fundamental property that XOR doesn't increase the maximum
  have h : a ^^^ b ≤ max a b := Nat.xor_le_max a b
  calc a ^^^ b ≤ max a b := h
  _ < 2^k := by
    cases' Nat.max_cases a b with h h
    · rw [h]; exact ha
    · rw [h]; exact hb

/-- Complete the proof for xorPositions when positions are in the full range -/
theorem xorPositions_valid (a b : Position) : 
  a.val ^^^ b.val < TotalSize := by
  -- TotalSize = 12288 = 3 * 2^12, so we need to show XOR preserves this bound
  -- First, note that 12288 < 2^14 (since 12288 = 3 * 4096 < 4 * 4096 = 16384)
  have h_bound : TotalSize < 2^14 := by norm_num [TotalSize]
  have ha : a.val < TotalSize := a.isLt
  have hb : b.val < TotalSize := b.isLt
  -- Both a and b are less than 2^14
  have ha' : a.val < 2^14 := lt_trans ha h_bound
  have hb' : b.val < 2^14 := lt_trans hb h_bound
  -- Therefore their XOR is less than 2^14
  have h_xor : a.val ^^^ b.val < 2^14 := xor_lt_two_pow a.val b.val 14 ha' hb'
  -- But we need the stronger result that it's less than 12288
  -- Use the fact that XOR doesn't exceed the maximum of the two values
  have h : a.val ^^^ b.val ≤ max a.val b.val := Nat.xor_le_max a.val b.val
  calc a.val ^^^ b.val ≤ max a.val b.val := h
  _ < TotalSize := by
    cases' Nat.max_cases a.val b.val with h h
    · rw [h]; exact ha
    · rw [h]; exact hb

/-- Bits 4 and 5 determine the value modulo 64 divided by 16 -/
theorem bits_4_5_determine_mid_nibble (n : ℕ) :
  (n / 16) % 4 = (if n.testBit 4 then 1 else 0) + (if n.testBit 5 then 2 else 0) := by
  -- Convert testBit to division form
  have h4 : n.testBit 4 = ((n / 16) % 2 = 1) := by
    rw [testBit_eq_one_iff]
    simp [pow_four, Nat.div_div_eq_div_mul]
  have h5 : n.testBit 5 = ((n / 32) % 2 = 1) := by
    rw [testBit_eq_one_iff]
    simp [pow_five, Nat.div_div_eq_div_mul]
  -- Now show the decomposition
  have : (n / 16) % 4 = (n / 16) % 2 + ((n / 16) / 2) % 2 * 2 := by
    conv_lhs => rw [← Nat.div_add_mod (n / 16) 2]
    rw [Nat.add_mod, Nat.mul_mod]
    simp
  rw [this]
  simp [h4, h5]
  split_ifs <;> simp <;> ring

/-- The resonance equivalence set has exactly 4 elements -/
theorem resonanceEquivSet_card : resonanceEquivSet.card = 4 := by
  simp [resonanceEquivSet]
  rfl

/-- XOR with 48 flips bits 4 and 5 -/
theorem xor_48_flips_bits_4_5 (n : ℕ) :
  (n ^^^ 48).testBit 4 = !n.testBit 4 ∧ 
  (n ^^^ 48).testBit 5 = !n.testBit 5 := by
  constructor
  · rw [xor_testBit]
    simp [Nat.testBit_succ, Nat.testBit_zero]
    -- 48 = 32 + 16 = 2^5 + 2^4
    have : (48).testBit 4 = true := by
      rw [testBit_eq_one_iff]
      norm_num
    simp [this]
  · rw [xor_testBit]
    have : (48).testBit 5 = true := by
      rw [testBit_eq_one_iff]
      norm_num
    simp [this]

end PrimeOS12288.BitArithmetic