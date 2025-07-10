/-!
# Tests for BitArithmetic.BasicImpl

This file contains verification tests for the bit arithmetic implementation.
-/

import PrimeOS12288.BitArithmetic.BasicImpl
import PrimeOS12288.BitArithmetic.Operations

namespace PrimeOS12288.BitArithmetic

open PrimeOS12288

/-- Test that bit operations work correctly for small examples -/
example : (5 : ℕ).testBit 0 = true := by simp [Nat.testBit_succ, Nat.testBit_zero]
example : (5 : ℕ).testBit 1 = false := by simp [Nat.testBit_succ, Nat.testBit_zero]
example : (5 : ℕ).testBit 2 = true := by simp [Nat.testBit_succ, Nat.testBit_zero]

/-- Test XOR operations -/
example : 5 ^^^ 3 = 6 := by norm_num
example : 48 ^^^ 0 = 48 := by norm_num
example : 48 ^^^ 1 = 49 := by norm_num

/-- Test the decomposition formula -/
example : 173 % 256 = (173 % 16) + 16 * ((173 / 16) % 4) + 64 * ((173 / 64) % 4) := by
  norm_num

/-- Test that xorBytes preserves byte bounds -/
example : ∀ (a b : ByteValue), (xorBytes a b).val < ByteSize := by
  intro a b
  exact (xorBytes a b).isLt

/-- Test specific byte XOR operations -/
example : (xorBytes ⟨48, by norm_num⟩ ⟨0, by norm_num⟩).val = 48 := by
  simp [xorBytes]
  rfl

example : (xorBytes ⟨48, by norm_num⟩ ⟨1, by norm_num⟩).val = 49 := by
  simp [xorBytes]
  norm_num

/-- Verify bits 4 and 5 for resonance set elements -/
example : (0 : ℕ).testBit 4 = false ∧ (0 : ℕ).testBit 5 = false := by
  simp [Nat.testBit_zero]

example : (48 : ℕ).testBit 4 = true ∧ (48 : ℕ).testBit 5 = true := by
  constructor
  · rw [testBit_eq_one_iff]; norm_num
  · rw [testBit_eq_one_iff]; norm_num

/-- Test the has_bits_45 function -/
example : hasBits45 ⟨48, by norm_num⟩ = true := by
  simp [hasBits45, isFieldActive]
  constructor
  · rw [Computational.isFieldActive_testBit]
    rw [testBit_eq_one_iff]; norm_num
  · rw [Computational.isFieldActive_testBit]
    rw [testBit_eq_one_iff]; norm_num

example : hasBits45 ⟨0, by norm_num⟩ = false := by
  simp [hasBits45, isFieldActive]
  rw [Computational.isFieldActive_testBit]
  simp [Nat.testBit_zero]

end PrimeOS12288.BitArithmetic