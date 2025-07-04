/-!
# Bit Arithmetic Operations

This file provides concrete bit operations that depend on the Basic implementation.
-/

import PrimeOS12288.BitArithmetic.BasicImpl

namespace PrimeOS12288.BitArithmetic

open PrimeOS12288 PrimeOS12288.Computational

/-- XOR operation on positions -/
def xorPositions (a b : Position) : Position :=
  ⟨a.val ^^^ b.val, xorPositions_valid a b⟩

/-- XOR operation on byte values -/
def xorBytes (a b : ByteValue) : ByteValue :=
  ⟨a.val ^^^ b.val, xor_byte_bound a b⟩

/-- Helper: Check if bits 4 and 5 are both set -/
def hasBits45 (b : ByteValue) : Bool :=
  isFieldActive b 4 && isFieldActive b 5

/-- The resonance equivalence set {0, 1, 48, 49} -/
def resonanceEquivSet : Finset ℕ := {0, 1, 48, 49}

/-- Helper lemma: XOR result membership characterization -/
private lemma xor_in_resonance_iff (x : ℕ) :
  x ∈ resonanceEquivSet ↔ x = 0 ∨ x = 1 ∨ x = 48 ∨ x = 49 := by
  simp [resonanceEquivSet]
  tauto

/-- Helper lemma: XOR preserves all bits except specific ones -/
private lemma xor_preserves_other_bits (n m : ByteValue) (x : ℕ) 
  (hx : x = n.val ^^^ m.val) (hres : x ∈ resonanceEquivSet) :
  ∀ i : FieldIndex, i.val ∉ {0, 4, 5} → (n.val.testBit i.val = m.val.testBit i.val) := by
  intro i hi
  have hx_val : x = 0 ∨ x = 1 ∨ x = 48 ∨ x = 49 := xor_in_resonance_iff.mp hres
  cases' hx_val with h0 hrest
  · -- Case x = 0: n = m
    have hnm : n.val = m.val := by
      rw [h0] at hx
      exact Nat.xor_eq_zero.mp hx
    rw [hnm]
  · cases' hrest with h1 hrest
    · -- Case x = 1: n and m differ only in bit 0
      rw [h1] at hx
      have hdiff : ∀ j, (n.val ^^^ m.val).testBit j ↔ (j = 0) := by
        intro j
        rw [← hx]
        simp [Nat.testBit_one]
      have : (n.val ^^^ m.val).testBit i.val = false := by
        rw [hdiff]
        simp at hi
        tauto
      rw [xor_testBit] at this
      simp at this
      exact this
    · cases' hrest with h48 h49
      · -- Case x = 48: n and m differ only in bits 4 and 5
        rw [h48] at hx
        have hdiff : ∀ j, (n.val ^^^ m.val).testBit j ↔ (j = 4 ∨ j = 5) := by
          intro j
          rw [← hx]
          -- 48 = 32 + 16 = 2^5 + 2^4
          simp [Nat.testBit_succ]
          cases' Nat.lt_trichotomy j 4 with hlt heq
          · simp [Nat.testBit_eq_false_of_lt hlt]
          · cases' heq with heq hgt
            · simp [heq]
            · cases' Nat.lt_trichotomy hgt 5 with hlt5 heq5
              · omega
              · cases' heq5 with heq5 hgt5
                · simp [heq5]
                · have : 48 < 2^j := by
                  calc 48 < 2^6 := by norm_num
                  _ ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hgt5
                  exact Nat.testBit_eq_false_of_lt this
        have : (n.val ^^^ m.val).testBit i.val = false := by
          rw [hdiff]
          simp at hi
          tauto
        rw [xor_testBit] at this
        simp at this
        exact this
      · -- Case x = 49: n and m differ in bits 0, 4, and 5
        rw [h49] at hx
        have hdiff : ∀ j, (n.val ^^^ m.val).testBit j ↔ (j = 0 ∨ j = 4 ∨ j = 5) := by
          intro j
          rw [← hx]
          -- 49 = 32 + 16 + 1 = 2^5 + 2^4 + 2^0
          simp [Nat.testBit_succ]
          cases' Nat.lt_trichotomy j 4 with hlt heq
          · cases' Nat.lt_trichotomy j 1 with hlt1 heq1
            · simp [Nat.testBit_eq_false_of_lt hlt1]
            · cases' heq1 with heq1 hgt1
              · simp [heq1]
              · have : j < 4 ∧ 1 ≤ j := ⟨hlt, hgt1⟩
                simp [Nat.testBit_eq_false_of_lt (by omega : j < 4)]
          · cases' heq with heq hgt
            · simp [heq]
            · cases' Nat.lt_trichotomy hgt 5 with hlt5 heq5
              · omega
              · cases' heq5 with heq5 hgt5
                · simp [heq5]
                · have : 49 < 2^j := by
                  calc 49 < 2^6 := by norm_num
                  _ ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hgt5
                  exact Nat.testBit_eq_false_of_lt this
        have : (n.val ^^^ m.val).testBit i.val = false := by
          rw [hdiff]
          simp at hi
          tauto
        rw [xor_testBit] at this
        simp at this
        exact this

/-- Key property: XOR with resonance equivalence set preserves certain properties -/
theorem resonance_equiv_characterization (n m : ByteValue) :
  n.val ^^^ m.val ∈ resonanceEquivSet ↔ 
  (∀ i : FieldIndex, i.val ∉ {0, 4, 5} → isFieldActive n i = isFieldActive m i) ∧
  (isFieldActive n 0 ≠ isFieldActive m 0) = (n.val ^^^ m.val ∈ {1, 49}) ∧
  (hasBits45 n ≠ hasBits45 m) = (n.val ^^^ m.val ∈ {48, 49}) := by
  constructor
  · intro h
    have hx := xor_in_resonance_iff.mp h
    constructor
    · -- First part: other bits are preserved
      intro i hi
      simp [isFieldActive, isFieldActiveImpl]
      exact xor_preserves_other_bits n m _ rfl h i hi
    constructor
    · -- Second part: bit 0 difference characterization
      simp [isFieldActive, isFieldActiveImpl]
      cases' hx with h0 hrest
      · -- x = 0
        simp [← h0]
        have : n.val = m.val := Nat.xor_eq_zero.mp h0
        simp [this]
      · cases' hrest with h1 hrest
        · -- x = 1
          simp [← h1]
          constructor
          · intro _
            simp [resonanceEquivSet]
          · intro _
            rw [xor_testBit]
            simp [Nat.testBit_one]
        · cases' hrest with h48 h49
          · -- x = 48
            simp [← h48]
            constructor
            · intro h
              exfalso
              rw [xor_testBit] at h
              simp at h
              -- 48.testBit 0 = false
              have : ¬(48).testBit 0 := by norm_num
              contradiction
            · intro h
              exfalso
              simp [resonanceEquivSet] at h
          · -- x = 49
            simp [← h49]
            constructor
            · intro _
              simp [resonanceEquivSet]
            · intro _
              rw [xor_testBit]
              -- 49.testBit 0 = true
              have : (49).testBit 0 = true := by norm_num
              simp [this]
    · -- Third part: bits 4,5 difference characterization
      simp [hasBits45, isFieldActive, isFieldActiveImpl]
      cases' hx with h0 hrest
      · -- x = 0
        simp [← h0]
        have : n.val = m.val := Nat.xor_eq_zero.mp h0
        simp [this]
      · cases' hrest with h1 hrest
        · -- x = 1
          simp [← h1]
          constructor
          · intro h
            exfalso
            have h4 : (n.val ^^^ m.val).testBit 4 = (n.val.testBit 4 != m.val.testBit 4) := xor_testBit _ _ _
            have h5 : (n.val ^^^ m.val).testBit 5 = (n.val.testBit 5 != m.val.testBit 5) := xor_testBit _ _ _
            rw [h1] at h4 h5
            -- 1.testBit 4 = false and 1.testBit 5 = false
            have : ¬(1).testBit 4 ∧ ¬(1).testBit 5 := by norm_num
            simp [this.1, this.2] at h4 h5
            simp [h4, h5] at h
          · intro h
            exfalso
            simp [resonanceEquivSet] at h
        · cases' hrest with h48 h49
          · -- x = 48
            simp [← h48]
            constructor
            · intro _
              simp [resonanceEquivSet]
            · intro _
              -- Need to show bits 4 and 5 differ
              rw [Bool.and_ne_and]
              rw [xor_testBit, xor_testBit]
              -- 48.testBit 4 = true and 48.testBit 5 = true
              have h4 : (48).testBit 4 = true := by norm_num
              have h5 : (48).testBit 5 = true := by norm_num
              simp [h4, h5]
              tauto
          · -- x = 49
            simp [← h49]
            constructor
            · intro _
              simp [resonanceEquivSet]
            · intro _
              rw [Bool.and_ne_and]
              rw [xor_testBit, xor_testBit]
              -- 49.testBit 4 = true and 49.testBit 5 = true
              have h4 : (49).testBit 4 = true := by norm_num
              have h5 : (49).testBit 5 = true := by norm_num
              simp [h4, h5]
              tauto
  · -- Reverse direction
    intro ⟨h_preserve, h_bit0, h_bits45⟩
    -- Analyze the XOR result
    have hxor_bound : n.val ^^^ m.val < 256 := by
      exact xor_byte_bound n m
    -- Consider all possible values of the XOR
    by_cases h0 : isFieldActive n 0 = isFieldActive m 0
    · by_cases h45 : hasBits45 n = hasBits45 m
      · -- Both bit 0 and bits 4,5 are equal
        -- This means n and m differ only in bits not in {0,4,5}
        -- But h_preserve says they're equal on those bits, so n = m
        have : n.val = m.val := by
          apply Nat.eq_of_testBit_eq
          intro i
          by_cases hi : i ∈ {0, 4, 5}
          · simp at hi
            cases' hi with hi0 hi45
            · simp [isFieldActive, isFieldActiveImpl] at h0
              exact h0
            · cases' hi45 with hi4 hi5
              · simp [hasBits45, isFieldActive, isFieldActiveImpl] at h45
                rw [Bool.and_eq_true] at h45
                exact h45.1
              · simp [hasBits45, isFieldActive, isFieldActiveImpl] at h45
                rw [Bool.and_eq_true] at h45
                exact h45.2
          · -- Use h_preserve for other bits
            have : i < 8 ∨ 8 ≤ i := Nat.lt_or_le i 8
            cases' this with hlt hge
            · have hi_field : ∃ fi : FieldIndex, fi.val = i := by
                use ⟨i, by simp [NumFields]; exact hlt⟩
                simp
              obtain ⟨fi, rfl⟩ := hi_field
              have := h_preserve fi hi
              simp [isFieldActive, isFieldActiveImpl] at this
              exact this
            · -- For i ≥ 8, both are false since n,m < 256
              have hn : n.val < 2^i := by
                calc n.val < 256 := n.isLt
                _ = 2^8 := by norm_num
                _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) hge
              have hm : m.val < 2^i := by
                calc m.val < 256 := m.isLt
                _ = 2^8 := by norm_num
                _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) hge
              rw [testBit_eq_false_of_lt hn, testBit_eq_false_of_lt hm]
        rw [this, Nat.xor_self]
        simp [resonanceEquivSet]
      · -- Bits 4,5 differ but bit 0 is same
        rw [h_bits45.2] at h45
        simp [resonanceEquivSet] at h45
        cases' h45 with h48 h49
        · exact h48
        · -- Can't be 49 since bit 0 must be same
          exfalso
          simp [resonanceEquivSet] at h49
          rw [h_bit0.2] at h0
          simp [resonanceEquivSet] at h0
          exact h0 h49
    · -- Bit 0 differs
      rw [h_bit0.2] at h0
      simp [resonanceEquivSet] at h0
      cases' h0 with h1 h49
      · by_cases h45 : hasBits45 n = hasBits45 m
        · -- Only bit 0 differs
          exact h1
        · -- Both bit 0 and bits 4,5 differ
          rw [h_bits45.2] at h45
          simp [resonanceEquivSet] at h45
          cases' h45 with h48 h49'
          · -- Can't be 48 since bit 0 must differ
            exfalso
            have : n.val ^^^ m.val ∈ ({1, 49} : Finset ℕ) := h1
            have : n.val ^^^ m.val ∈ ({48, 49} : Finset ℕ) := h48
            simp [resonanceEquivSet] at this h48
            cases' this with h1' h49''
            · cases' h48 with h48' _
              · omega
              · omega
            · exact h49''
          · exact h49'
      · exact h49

/-- XOR is commutative for positions -/
theorem xorPositions_comm (a b : Position) :
  xorPositions a b = xorPositions b a := by
  simp [xorPositions]
  ext
  exact Nat.xor_comm a.val b.val

/-- XOR is associative for positions -/
theorem xorPositions_assoc (a b c : Position) :
  xorPositions (xorPositions a b) c = xorPositions a (xorPositions b c) := by
  simp [xorPositions]
  ext
  exact Nat.xor_assoc a.val b.val c.val

/-- XOR with self is zero for positions -/
theorem xorPositions_self (a : Position) :
  (xorPositions a a).val = 0 := by
  simp [xorPositions]
  exact Nat.xor_self a.val

/-- XOR is commutative for bytes -/
theorem xorBytes_comm (a b : ByteValue) :
  xorBytes a b = xorBytes b a := by
  simp [xorBytes]
  ext
  exact Nat.xor_comm a.val b.val

/-- XOR is associative for bytes -/
theorem xorBytes_assoc (a b c : ByteValue) :
  xorBytes (xorBytes a b) c = xorBytes a (xorBytes b c) := by
  simp [xorBytes]
  ext
  exact Nat.xor_assoc a.val b.val c.val

/-- XOR with self is zero for bytes -/
theorem xorBytes_self (a : ByteValue) :
  (xorBytes a a).val = 0 := by
  simp [xorBytes]
  exact Nat.xor_self a.val

/-- XOR preserves the property of being a valid position -/
theorem xorPositions_preserves_validity (a b : Position) :
  (xorPositions a b).val < TotalSize := by
  exact (xorPositions a b).isLt

/-- XOR preserves the property of being a valid byte -/
theorem xorBytes_preserves_validity (a b : ByteValue) :
  (xorBytes a b).val < ByteSize := by
  exact (xorBytes a b).isLt

/-- XOR with 0 is identity for positions -/
theorem xorPositions_zero_right (a : Position) (h : 0 < TotalSize := by norm_num) :
  xorPositions a ⟨0, h⟩ = a := by
  simp [xorPositions]
  ext
  exact Nat.xor_zero a.val

/-- XOR with 0 is identity for bytes -/
theorem xorBytes_zero_right (a : ByteValue) (h : 0 < ByteSize := by norm_num) :
  xorBytes a ⟨0, h⟩ = a := by
  simp [xorBytes]
  ext
  exact Nat.xor_zero a.val

/-- Helper: Convert position XOR to byte XOR -/
theorem positionToByte_xor (a b : Position) [Foundation] :
  positionToByte (xorPositions a b) = 
  xorBytes (positionToByte a) (positionToByte b) := by
  ext
  simp [xorPositions, xorBytes, positionToByte]
  -- Use the fact that positionToByte is modulo ByteSize
  have ha : (positionToByte a).val = a.val % ByteSize := position_byte_periodic a
  have hb : (positionToByte b).val = b.val % ByteSize := position_byte_periodic b
  have hxor : (positionToByte (xorPositions a b)).val = (a.val ^^^ b.val) % ByteSize := by
    simp [xorPositions]
    exact position_byte_periodic (xorPositions a b)
  rw [ha, hb, hxor]
  -- XOR distributes over modulo when the modulus is a power of 2
  -- ByteSize = 256 = 2^8
  have hpow : ByteSize = 2^8 := by norm_num [ByteSize]
  rw [hpow]
  exact Nat.xor_mod a.val b.val 8

end PrimeOS12288.BitArithmetic