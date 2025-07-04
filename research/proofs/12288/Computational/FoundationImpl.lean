/-!
# Concrete Implementation of Computational Foundation

This file provides the concrete implementation of the Foundation class,
establishing the core mappings between positions, bytes, and field activation.
-/

import PrimeOS12288.Computational.Foundation

namespace PrimeOS12288.Computational

open PrimeOS12288

/-- Concrete implementation of position to byte mapping -/
def positionToByteImpl (n : Position) : ByteValue :=
  ⟨n.val % ByteSize, by
    simp [ByteSize]
    exact Nat.mod_lt n.val (by norm_num : 0 < 256)⟩

/-- Concrete implementation of field activation check -/
def isFieldActiveImpl (b : ByteValue) (i : FieldIndex) : Bool :=
  b.val.testBit i.val

/-- The concrete Foundation instance for the PrimeOS 12288 system -/
instance : Foundation where
  positionToByte := positionToByteImpl
  isFieldActive := isFieldActiveImpl
  
  position_byte_periodic := by
    intro n
    simp [positionToByteImpl]
    rfl
  
  field_active_bit := by
    intro b i
    simp [isFieldActiveImpl]
    rfl

/-! ## Verification lemmas -/

/-- Verify that position to byte mapping is indeed modulo 256 -/
theorem positionToByte_mod (n : Position) :
  (positionToByte n).val = n.val % 256 := by
  simp [positionToByte, positionToByteImpl]

/-- Verify that field activation uses bit testing -/
theorem isFieldActive_testBit (b : ByteValue) (i : FieldIndex) :
  isFieldActive b i = b.val.testBit i.val := by
  simp [isFieldActive, isFieldActiveImpl]

/-- Two positions with the same byte value have the same active fields -/
theorem same_byte_same_fields (n₁ n₂ : Position) 
  (h : positionToByte n₁ = positionToByte n₂) :
  activeFields n₁ = activeFields n₂ := by
  simp [activeFields]
  ext i
  simp
  rw [h]

/-- Active fields are determined by the byte value modulo 256 -/
theorem activeFields_periodic (n : Position) (k : ℕ) 
  (h : n.val + k * 256 < TotalSize) :
  activeFields n = activeFields ⟨n.val + k * 256, h⟩ := by
  apply same_byte_same_fields
  simp [positionToByte, positionToByteImpl]
  rw [Nat.add_mod, Nat.mul_mod]
  simp [ByteSize]

/-- A byte value has at most 8 active fields -/
theorem activeFields_card_le (n : Position) :
  (activeFields n).card ≤ 8 := by
  simp [activeFields]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- If bit i is set in byte b, then field i is active -/
theorem bit_set_field_active (b : ByteValue) (i : FieldIndex) 
  (h : b.val.testBit i.val = true) :
  isFieldActive b i = true := by
  simp [isFieldActive, isFieldActiveImpl, h]

/-- If bit i is not set in byte b, then field i is not active -/
theorem bit_unset_field_inactive (b : ByteValue) (i : FieldIndex) 
  (h : b.val.testBit i.val = false) :
  isFieldActive b i = false := by
  simp [isFieldActive, isFieldActiveImpl, h]

/-- The byte value 0 has no active fields -/
theorem byte_zero_no_active_fields :
  ∀ i : FieldIndex, isFieldActive ⟨0, by norm_num⟩ i = false := by
  intro i
  simp [isFieldActive, isFieldActiveImpl]
  apply Nat.testBit_zero

/-- The byte value 255 has all fields active -/
theorem byte_255_all_fields_active :
  ∀ i : FieldIndex, isFieldActive ⟨255, by norm_num⟩ i = true := by
  intro i
  simp [isFieldActive, isFieldActiveImpl]
  have h : i.val < 8 := i.isLt
  simp [NumFields] at h
  apply Nat.testBit_two_pow_sub_one
  exact h

end PrimeOS12288.Computational