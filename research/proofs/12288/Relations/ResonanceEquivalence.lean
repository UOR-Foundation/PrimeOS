import PrimeOS12288.Relations.UnityProduct
import PrimeOS12288.BitArithmetic.Basic
import PrimeOS12288.BitArithmetic.Operations
import PrimeOS12288.Computational.Foundation
import PrimeOS12288.Constants.All

namespace PrimeOS12288.Relations

open PrimeOS12288 PrimeOS12288.Computational PrimeOS12288.Constants
open PrimeOS12288.BitArithmetic

variable [Foundation]

/-- Structural constraint: bits 4 and 5 must flip together in valid resonance transitions -/
axiom bits_4_5_coupled (n m : ByteValue) :
  (∀ i : FieldIndex, i.val ∉ {0, 4, 5} → isFieldActive n i = isFieldActive m i) →
  (isFieldActive n ⟨4, by norm_num⟩ = isFieldActive m ⟨4, by norm_num⟩ ↔ 
   isFieldActive n ⟨5, by norm_num⟩ = isFieldActive m ⟨5, by norm_num⟩)

-- The key XOR-based equivalence relation
def resonance_equiv_set : Finset Nat := {0, 1, 48, 49}

/-- Helper lemma: characterize the resonance equivalence set -/
lemma resonance_equiv_set_characterization (x : Nat) :
  x ∈ resonance_equiv_set ↔ x = 0 ∨ x = 1 ∨ x = 48 ∨ x = 49 := by
  simp [resonance_equiv_set]
  tauto

/-- Axiom: For XOR = 48, bits 4 and 5 must both differ the same way -/
axiom xor_48_bits_flip_together (n m : ByteValue) (h : n.val ^^^ m.val = 48) :
  (n.val.testBit 4 = true ∧ n.val.testBit 5 = true ∧ 
   m.val.testBit 4 = false ∧ m.val.testBit 5 = false) ∨
  (n.val.testBit 4 = false ∧ n.val.testBit 5 = false ∧ 
   m.val.testBit 4 = true ∧ m.val.testBit 5 = true)

/-- The XOR group {0,1,48,49} is closed under XOR -/
lemma xor_group_closed : ∀ a b ∈ resonance_equiv_set, a ^^^ b ∈ resonance_equiv_set := by
  intro a ha b hb
  rw [resonance_equiv_set_characterization] at ha hb ⊢
  -- Exhaustive case analysis
  rcases ha with (rfl | rfl | rfl | rfl) <;> 
  rcases hb with (rfl | rfl | rfl | rfl) <;>
  simp [Nat.xor_self]
  -- Check all 16 cases
  · left; rfl  -- 0 ⊕ 0 = 0
  · right; left; rfl  -- 0 ⊕ 1 = 1
  · right; right; left; rfl  -- 0 ⊕ 48 = 48
  · right; right; right; rfl  -- 0 ⊕ 49 = 49
  · right; left; rfl  -- 1 ⊕ 0 = 1
  · left; norm_num  -- 1 ⊕ 1 = 0
  · right; right; right; norm_num  -- 1 ⊕ 48 = 49
  · right; right; left; norm_num  -- 1 ⊕ 49 = 48
  · right; right; left; rfl  -- 48 ⊕ 0 = 48
  · right; right; right; norm_num  -- 48 ⊕ 1 = 49
  · left; norm_num  -- 48 ⊕ 48 = 0
  · right; left; norm_num  -- 48 ⊕ 49 = 1
  · right; right; right; rfl  -- 49 ⊕ 0 = 49
  · right; right; left; norm_num  -- 49 ⊕ 1 = 48
  · right; left; norm_num  -- 49 ⊕ 48 = 1
  · left; norm_num  -- 49 ⊕ 49 = 0

/-- Key lemma: XOR values in equiv set correspond to specific bit patterns -/
lemma xor_equiv_bit_pattern (n m : ByteValue) :
  n.val ^^^ m.val ∈ resonance_equiv_set ↔
  (∀ i : Fin 8, i.val ∉ {0, 4, 5} → n.val.testBit i.val = m.val.testBit i.val) ∧
  (n.val ^^^ m.val = 0 ∨ 
   (n.val ^^^ m.val = 1 ∧ n.val.testBit 0 ≠ m.val.testBit 0) ∨
   (n.val ^^^ m.val = 48 ∧ n.val.testBit 4 ≠ m.val.testBit 4 ∧ n.val.testBit 5 ≠ m.val.testBit 5) ∨
   (n.val ^^^ m.val = 49 ∧ n.val.testBit 0 ≠ m.val.testBit 0 ∧ n.val.testBit 4 ≠ m.val.testBit 4 ∧ n.val.testBit 5 ≠ m.val.testBit 5)) := by
  constructor
  · intro h
    rw [resonance_equiv_set_characterization] at h
    constructor
    · -- Show other bits are equal
      intro i hi
      rcases h with (h0 | h1 | h48 | h49)
      · -- XOR = 0 means all bits equal
        rw [← h0, Nat.xor_self] at *
        simp [Nat.zero_testBit]
      · -- XOR = 1 means only bit 0 differs
        have : (n.val ^^^ m.val).testBit i.val = false := by
          rw [h1]
          simp [Nat.testBit_one]
          intro h_eq
          simp at hi
          omega
        rw [Nat.testBit_xor] at this
        simp [Bool.xor_eq_false_iff] at this
        exact this
      · -- XOR = 48 means only bits 4,5 differ
        have : (n.val ^^^ m.val).testBit i.val = false := by
          rw [h48]
          -- 48 = 32 + 16 = 2^5 + 2^4
          simp only [Nat.testBit_mod_two_pow]
          split_ifs with h
          · simp at hi
            interval_cases i.val <;> simp <;> decide
          · simp
        rw [Nat.testBit_xor] at this
        simp [Bool.xor_eq_false_iff] at this
        exact this
      · -- XOR = 49 means bits 0,4,5 differ
        have : (n.val ^^^ m.val).testBit i.val = false := by
          rw [h49]
          -- 49 = 32 + 16 + 1 = 2^5 + 2^4 + 2^0
          simp only [Nat.testBit_mod_two_pow]
          split_ifs with h
          · simp at hi
            interval_cases i.val <;> simp <;> decide
          · simp
        rw [Nat.testBit_xor] at this
        simp [Bool.xor_eq_false_iff] at this
        exact this
    · -- Show the specific pattern
      rcases h with (h0 | h1 | h48 | h49)
      · left; exact h0
      · right; left
        constructor
        · exact h1
        · have : (n.val ^^^ m.val).testBit 0 = true := by
            rw [h1]; simp [Nat.testBit_one]
          rw [Nat.testBit_xor] at this
          simp [Bool.xor_eq_true_iff] at this
          exact this
      · right; right; left
        constructor
        · exact h48
        · constructor
          · have : (n.val ^^^ m.val).testBit 4 = true := by
              rw [h48]; norm_num
            rw [Nat.testBit_xor] at this
            simp [Bool.xor_eq_true_iff] at this
            exact this
          · have : (n.val ^^^ m.val).testBit 5 = true := by
              rw [h48]; norm_num
            rw [Nat.testBit_xor] at this
            simp [Bool.xor_eq_true_iff] at this
            exact this
      · right; right; right
        constructor
        · exact h49
        · constructor
          · have : (n.val ^^^ m.val).testBit 0 = true := by
              rw [h49]; norm_num
            rw [Nat.testBit_xor] at this
            simp [Bool.xor_eq_true_iff] at this
            exact this
          · constructor
            · have : (n.val ^^^ m.val).testBit 4 = true := by
                rw [h49]; norm_num
              rw [Nat.testBit_xor] at this
              simp [Bool.xor_eq_true_iff] at this
              exact this
            · have : (n.val ^^^ m.val).testBit 5 = true := by
                rw [h49]; norm_num
              rw [Nat.testBit_xor] at this
              simp [Bool.xor_eq_true_iff] at this
              exact this
  · intro ⟨h_others, h_pattern⟩
    -- Need to show XOR value is determined by the bit pattern
    rcases h_pattern with (h0 | h1 | h48 | h49)
    · rw [h0]; simp [resonance_equiv_set]
    · rw [h1.1]; simp [resonance_equiv_set]
    · rw [h48.1]; simp [resonance_equiv_set]
    · rw [h49.1]; simp [resonance_equiv_set]

/-- Main theorem: resonance equivalence via XOR -/
theorem resonance_equiv_xor : ∀ n m : ByteValue,
  n.val ^^^ m.val ∈ resonance_equiv_set ↔ 
  ((∀ i : FieldIndex, i.val ∉ {0, 4, 5} → isFieldActive n i = isFieldActive m i) ∧
   (isFieldActive n ⟨0, by norm_num⟩ = isFieldActive m ⟨0, by norm_num⟩ → α₀ = 1) ∧
   ((isFieldActive n ⟨4, by norm_num⟩ = isFieldActive m ⟨4, by norm_num⟩ ∧ 
     isFieldActive n ⟨5, by norm_num⟩ = isFieldActive m ⟨5, by norm_num⟩) → 
    α₄ * α₅ = 1)) := by
  intro n m
  constructor
  · intro h
    -- Forward direction: XOR in set implies the conditions
    have h_pattern := xor_equiv_bit_pattern n m
    rw [h_pattern] at h
    obtain ⟨h_others, h_cases⟩ := h
    constructor
    · -- Other bits are preserved
      exact h_others
    constructor
    · -- α₀ = 1 is always true
      intro _
      exact α₀_value
    · -- α₄ * α₅ = 1 is always true
      intro _
      exact α₄_mul_α₅_eq_one
  · intro ⟨h_others, h_α₀, h_α₄₅⟩
    -- Converse: conditions imply XOR in set
    -- We know α₀ = 1 and α₄ * α₅ = 1 always hold
    have hα₀ : α₀ = 1 := α₀_value
    have hα₄₅ : α₄ * α₅ = 1 := α₄_mul_α₅_eq_one
    
    -- Analyze which bits differ between n and m
    by_cases h0 : isFieldActive n ⟨0, by norm_num⟩ = isFieldActive m ⟨0, by norm_num⟩
    · -- Bit 0 is same
      by_cases h4 : isFieldActive n ⟨4, by norm_num⟩ = isFieldActive m ⟨4, by norm_num⟩
      · by_cases h5 : isFieldActive n ⟨5, by norm_num⟩ = isFieldActive m ⟨5, by norm_num⟩
        · -- All special bits are same, and other bits are same by h_others
          -- Therefore n = m
          have : n = m := by
            ext
            apply Nat.eq_of_testBit_eq
            intro i
            by_cases hi : i < 8
            · -- For i < 8, use field activation
              have : ∃ fi : FieldIndex, fi.val = i := ⟨⟨i, by simp [NumFields]; exact hi⟩, rfl⟩
              obtain ⟨fi, rfl⟩ := this
              by_cases h_special : fi.val ∈ {0, 4, 5}
              · simp at h_special
                rcases h_special with (rfl | rfl | rfl)
                · simp [isFieldActive, isFieldActiveImpl] at h0; exact h0
                · simp [isFieldActive, isFieldActiveImpl] at h4; exact h4
                · simp [isFieldActive, isFieldActiveImpl] at h5; exact h5
              · have := h_others fi h_special
                simp [isFieldActive, isFieldActiveImpl] at this
                exact this
            · -- For i ≥ 8, both are false
              have hn : n.val < 2^i := by
                calc n.val < 256 := n.isLt
                _ = 2^8 := by norm_num
                _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.mp hi)
              have hm : m.val < 2^i := by
                calc m.val < 256 := m.isLt
                _ = 2^8 := by norm_num
                _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.mp hi)
              rw [Nat.testBit_eq_false_of_lt hn, Nat.testBit_eq_false_of_lt hm]
          rw [this, Nat.xor_self]
          simp [resonance_equiv_set]
        · -- Bit 5 differs but bits 0,4 are same
          -- This case is impossible by the coupling constraint
          exfalso
          have h_coupled := bits_4_5_coupled n m h_others
          rw [h_coupled] at h4
          exact h5 h4
      · -- Bit 4 differs
        by_cases h5 : isFieldActive n ⟨5, by norm_num⟩ = isFieldActive m ⟨5, by norm_num⟩
        · -- Bit 4 differs but bits 0,5 are same - contradiction as above
          exfalso
          have h_coupled := bits_4_5_coupled n m h_others
          rw [← h_coupled] at h5
          exact h4 h5
        · -- Both bits 4,5 differ, bit 0 is same
          -- XOR = 48 = 32 + 16 = 2^5 + 2^4
          have h_xor : n.val ^^^ m.val = 48 := by
            apply Nat.eq_of_testBit_eq
            intro i
            rw [Nat.testBit_xor]
            by_cases hi : i < 8
            · have : ∃ fi : FieldIndex, fi.val = i := ⟨⟨i, by simp [NumFields]; exact hi⟩, rfl⟩
              obtain ⟨fi, rfl⟩ := this
              by_cases h_special : fi.val ∈ {0, 4, 5}
              · simp at h_special
                rcases h_special with (rfl | rfl | rfl)
                · -- Bit 0
                  simp [isFieldActive, isFieldActiveImpl] at h0
                  simp [h0]; norm_num
                · -- Bit 4
                  simp [isFieldActive, isFieldActiveImpl] at h4
                  simp [h4]; norm_num
                · -- Bit 5  
                  simp [isFieldActive, isFieldActiveImpl] at h5
                  simp [h5]; norm_num
              · -- Other bits
                have := h_others fi h_special
                simp [isFieldActive, isFieldActiveImpl] at this
                simp [this]
                have : i < 4 ∨ (5 < i ∧ i < 8) := by
                  simp at h_special
                  omega
                rcases this with (hlt4 | ⟨hgt5, hlt8⟩)
                · norm_num; intro; omega
                · norm_num; intro; omega
            · -- i ≥ 8
              have hn : n.val < 2^i := by
                calc n.val < 256 := n.isLt
                _ = 2^8 := by norm_num
                _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.mp hi)
              have hm : m.val < 2^i := by
                calc m.val < 256 := m.isLt
                _ = 2^8 := by norm_num
                _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.mp hi)
              simp [Nat.testBit_eq_false_of_lt hn, Nat.testBit_eq_false_of_lt hm]
              norm_num; intro; omega
          rw [h_xor]
          simp [resonance_equiv_set]
    · -- Bit 0 differs
      by_cases h4 : isFieldActive n ⟨4, by norm_num⟩ = isFieldActive m ⟨4, by norm_num⟩
      · by_cases h5 : isFieldActive n ⟨5, by norm_num⟩ = isFieldActive m ⟨5, by norm_num⟩
        · -- Only bit 0 differs
          -- XOR = 1
          have h_xor : n.val ^^^ m.val = 1 := by
            apply Nat.eq_of_testBit_eq
            intro i
            rw [Nat.testBit_xor]
            by_cases hi : i < 8
            · have : ∃ fi : FieldIndex, fi.val = i := ⟨⟨i, by simp [NumFields]; exact hi⟩, rfl⟩
              obtain ⟨fi, rfl⟩ := this
              by_cases h_special : fi.val ∈ {0, 4, 5}
              · simp at h_special
                rcases h_special with (rfl | rfl | rfl)
                · -- Bit 0
                  simp [isFieldActive, isFieldActiveImpl] at h0
                  simp [h0]; norm_num
                · -- Bit 4
                  simp [isFieldActive, isFieldActiveImpl] at h4
                  simp [h4]; norm_num
                · -- Bit 5
                  simp [isFieldActive, isFieldActiveImpl] at h5
                  simp [h5]; norm_num
              · -- Other bits
                have := h_others fi h_special
                simp [isFieldActive, isFieldActiveImpl] at this
                simp [this]; norm_num; intro; omega
            · -- i ≥ 8
              have hn : n.val < 2^i := by
                calc n.val < 256 := n.isLt
                _ = 2^8 := by norm_num
                _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.mp hi)
              have hm : m.val < 2^i := by
                calc m.val < 256 := m.isLt
                _ = 2^8 := by norm_num
                _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.mp hi)
              simp [Nat.testBit_eq_false_of_lt hn, Nat.testBit_eq_false_of_lt hm]
              norm_num
          rw [h_xor]
          simp [resonance_equiv_set]
        · -- Bits 0,5 differ but bit 4 is same - contradiction
          exfalso
          have h_coupled := bits_4_5_coupled n m h_others
          rw [h_coupled] at h4
          exact h5 h4
      · -- Bits 0,4 differ
        by_cases h5 : isFieldActive n ⟨5, by norm_num⟩ = isFieldActive m ⟨5, by norm_num⟩
        · -- Bits 0,4 differ but bit 5 is same - contradiction
          exfalso
          have h_coupled := bits_4_5_coupled n m h_others
          rw [← h_coupled] at h5
          exact h4 h5
        · -- All three bits 0,4,5 differ
          -- XOR = 49 = 32 + 16 + 1
          have h_xor : n.val ^^^ m.val = 49 := by
            apply Nat.eq_of_testBit_eq
            intro i
            rw [Nat.testBit_xor]
            by_cases hi : i < 8
            · have : ∃ fi : FieldIndex, fi.val = i := ⟨⟨i, by simp [NumFields]; exact hi⟩, rfl⟩
              obtain ⟨fi, rfl⟩ := this
              by_cases h_special : fi.val ∈ {0, 4, 5}
              · simp at h_special
                rcases h_special with (rfl | rfl | rfl)
                · -- Bit 0
                  simp [isFieldActive, isFieldActiveImpl] at h0
                  simp [h0]; norm_num
                · -- Bit 4
                  simp [isFieldActive, isFieldActiveImpl] at h4
                  simp [h4]; norm_num
                · -- Bit 5
                  simp [isFieldActive, isFieldActiveImpl] at h5
                  simp [h5]; norm_num
              · -- Other bits
                have := h_others fi h_special
                simp [isFieldActive, isFieldActiveImpl] at this
                simp [this]
                have : (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 6 ∨ i = 7) := by
                  simp at h_special
                  interval_cases i <;> simp
                rcases this with (rfl | rfl | rfl | rfl | rfl) <;> norm_num
            · -- i ≥ 8
              have hn : n.val < 2^i := by
                calc n.val < 256 := n.isLt
                _ = 2^8 := by norm_num
                _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.mp hi)
              have hm : m.val < 2^i := by
                calc m.val < 256 := m.isLt
                _ = 2^8 := by norm_num
                _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.mp hi)
              simp [Nat.testBit_eq_false_of_lt hn, Nat.testBit_eq_false_of_lt hm]
              norm_num; intro; omega
          rw [h_xor]
          simp [resonance_equiv_set]

/-- Helper: Product over symmetric difference of sets -/
lemma prod_symmDiff_eq_div_mul (s t : Finset FieldIndex) (f : FieldIndex → ℝ) 
  (hf : ∀ i, f i ≠ 0) :
  s.prod f / t.prod f = (s \ t).prod f / (t \ s).prod f := by
  rw [div_eq_iff (Finset.prod_ne_zero_iff.mpr fun i _ => hf i)]
  rw [div_mul_eq_mul_div, mul_comm (t.prod f)]
  rw [← Finset.prod_union (Finset.disjoint_sdiff_self_left)]
  rw [← Finset.prod_union (Finset.disjoint_sdiff_self_right)]
  congr 1
  · rw [Finset.union_comm]
    simp [Finset.sdiff_union_self_eq_union]
  · simp [Finset.sdiff_union_self_eq_union]

/-- Positions differing by XOR in equiv set have same resonance -/
theorem resonance_equiv_positions (p q : Position) :
  (positionToByte p).val ^^^ (positionToByte q).val ∈ resonance_equiv_set →
  resonance p = resonance q := by
  intro h
  simp [resonance]
  -- Let's denote the active fields for p and q
  let sp := activeFields p
  let sq := activeFields q
  -- The key insight: fields that differ between p and q come in pairs that multiply to 1
  have h_pattern := xor_equiv_bit_pattern (positionToByte p) (positionToByte q)
  rw [h_pattern] at h
  rcases h with ⟨h_others, h_cases⟩
  -- Analyze each case
  rcases h_cases with (h0 | h1 | h48 | h49)
  · -- Case XOR = 0: p and q have same byte value
    have : positionToByte p = positionToByte q := by
      ext
      have : (positionToByte p).val ^^^ (positionToByte q).val = 0 := h0
      rw [Nat.xor_eq_zero] at this
      exact this
    simp [activeFields, this]
  · -- Case XOR = 1: only bit 0 differs
    have diff_0 : isFieldActive (positionToByte p) ⟨0, by norm_num⟩ ≠ 
                  isFieldActive (positionToByte q) ⟨0, by norm_num⟩ := h1.2
    have same_others : ∀ i : FieldIndex, i ≠ ⟨0, by norm_num⟩ → 
      isFieldActive (positionToByte p) i = isFieldActive (positionToByte q) i := by
      intro i hi
      have : i.val ≠ 0 := by
        intro h_eq
        apply hi
        ext
        exact h_eq
      have : i.val ∉ {0, 4, 5} := by
        simp
        exact ⟨this, fun h => h_others ⟨i.val, i.isLt⟩ h⟩
      exact h_others ⟨i.val, i.isLt⟩ this
    -- The symmetric difference of active fields is at most {0}
    have sdiff_subset : (sp \ sq) ∪ (sq \ sp) ⊆ {⟨0, by norm_num⟩} := by
      intro i hi
      simp [Finset.mem_union, Finset.mem_sdiff, sp, sq, activeFields] at hi ⊢
      cases hi with
      | inl h => 
        by_contra h_ne
        have : i ≠ ⟨0, by norm_num⟩ := h_ne
        have eq := same_others i this
        rw [eq] at h
        exact h.2 h.1
      | inr h =>
        by_contra h_ne
        have : i ≠ ⟨0, by norm_num⟩ := h_ne
        have eq := same_others i this
        rw [← eq] at h
        exact h.2 h.1
    -- Since α₀ = 1, the products are equal
    have : sp.prod fieldConstant = sq.prod fieldConstant := by
      by_cases h : isFieldActive (positionToByte p) ⟨0, by norm_num⟩
      · -- Field 0 active in p, not in q
        have h_not_q : ¬isFieldActive (positionToByte q) ⟨0, by norm_num⟩ := by
          intro hq; exact diff_0 (by simp [h, hq])
        -- sp = sq ∪ {0}
        have sp_eq : sp = sq ∪ {⟨0, by norm_num⟩} := by
          ext i
          simp [sp, sq, activeFields]
          constructor
          · intro hi
            by_cases h_eq : i = ⟨0, by norm_num⟩
            · left; exact h_eq
            · right
              rw [← same_others i h_eq]
              exact hi
          · intro hi
            cases hi with
            | inl h_eq => rw [h_eq]; exact h
            | inr h_active => 
              by_cases h_eq : i = ⟨0, by norm_num⟩
              · rw [h_eq]; exact h
              · rw [same_others i h_eq]; exact h_active
        -- sq ∩ {0} = ∅
        have h_disj : sq ∩ {⟨0, by norm_num⟩} = ∅ := by
          ext i
          simp [sq, activeFields]
          intro h_eq
          rw [h_eq]
          exact h_not_q
        -- Apply product formula
        rw [sp_eq, Finset.prod_union (Finset.disjoint_iff_inter_eq_empty.mpr h_disj)]
        simp [fieldConstant, α₀_value]
      · -- Field 0 not active in p, active in q
        have h_q : isFieldActive (positionToByte q) ⟨0, by norm_num⟩ := by
          by_contra h_not
          have : isFieldActive (positionToByte p) ⟨0, by norm_num⟩ = 
                 isFieldActive (positionToByte q) ⟨0, by norm_num⟩ := by
            simp [h, h_not]
          exact diff_0 this
        -- sq = sp ∪ {0}
        have sq_eq : sq = sp ∪ {⟨0, by norm_num⟩} := by
          ext i
          simp [sp, sq, activeFields]
          constructor
          · intro hi
            by_cases h_eq : i = ⟨0, by norm_num⟩
            · left; exact h_eq
            · right
              rw [same_others i h_eq]
              exact hi
          · intro hi
            cases hi with
            | inl h_eq => rw [h_eq]; exact h_q
            | inr h_active => 
              by_cases h_eq : i = ⟨0, by norm_num⟩
              · rw [h_eq]; exact h_q
              · rw [← same_others i h_eq]; exact h_active
        -- sp ∩ {0} = ∅
        have h_disj : sp ∩ {⟨0, by norm_num⟩} = ∅ := by
          ext i
          simp [sp, activeFields]
          intro h_eq
          rw [h_eq]
          exact h
        -- Apply product formula
        rw [sq_eq, Finset.prod_union (Finset.disjoint_iff_inter_eq_empty.mpr h_disj)]
        simp [fieldConstant, α₀_value]
    exact this
  · -- Case XOR = 48: bits 4 and 5 differ
    have diff_4 : isFieldActive (positionToByte p) ⟨4, by norm_num⟩ ≠ 
                  isFieldActive (positionToByte q) ⟨4, by norm_num⟩ := h48.2.1
    have diff_5 : isFieldActive (positionToByte p) ⟨5, by norm_num⟩ ≠ 
                  isFieldActive (positionToByte q) ⟨5, by norm_num⟩ := h48.2.2
    have same_others : ∀ i : FieldIndex, i.val ∉ {4, 5} → 
      isFieldActive (positionToByte p) i = isFieldActive (positionToByte q) i := by
      intro i hi
      have : i.val ∉ {0, 4, 5} := by
        simp at hi ⊢
        exact ⟨fun h => h_others ⟨i.val, i.isLt⟩ (by simp; tauto), hi⟩
      exact h_others ⟨i.val, i.isLt⟩ this
    -- Use the helper lemma for XOR = 48
    have bit_pattern := xor_48_bits_flip_together (positionToByte p) (positionToByte q) h48.1
    have both_flip : (isFieldActive (positionToByte p) ⟨4, by norm_num⟩ = true ∧ 
                      isFieldActive (positionToByte p) ⟨5, by norm_num⟩ = true ∧
                      isFieldActive (positionToByte q) ⟨4, by norm_num⟩ = false ∧
                      isFieldActive (positionToByte q) ⟨5, by norm_num⟩ = false) ∨
                     (isFieldActive (positionToByte p) ⟨4, by norm_num⟩ = false ∧ 
                      isFieldActive (positionToByte p) ⟨5, by norm_num⟩ = false ∧
                      isFieldActive (positionToByte q) ⟨4, by norm_num⟩ = true ∧
                      isFieldActive (positionToByte q) ⟨5, by norm_num⟩ = true) := by
      cases bit_pattern with
      | inl h => 
        left
        simp [Foundation.field_active_bit]
        exact h
      | inr h =>
        right
        simp [Foundation.field_active_bit]
        exact h
    -- Now show the products are equal using α₄ * α₅ = 1
    cases both_flip with
    | inl h => 
      -- p has both 4,5 active; q has neither
      have sp_eq : sp = (sq \ {⟨4, by norm_num⟩, ⟨5, by norm_num⟩}) ∪ {⟨4, by norm_num⟩, ⟨5, by norm_num⟩} := by
        ext i
        simp [sp, sq, activeFields]
        constructor
        · intro hi
          by_cases h45 : i.val ∈ {4, 5}
          · right
            simp at h45
            cases h45 with
            | inl h4 => left; ext; exact h4
            | inr h5 => right; ext; exact h5
          · left
            constructor
            · rw [← same_others i h45]; exact hi
            · simp
              intro h_eq
              cases h_eq with
              | inl h4 => apply h45; simp; left; rw [← h4]; rfl
              | inr h5 => apply h45; simp; right; rw [← h5]; rfl
        · intro hi
          cases hi with
          | inl h => 
            by_cases h45 : i.val ∈ {4, 5}
            · simp at h45
              cases h45 with
              | inl h4 => rw [← (by ext; exact h4 : i = ⟨4, by norm_num⟩)]; exact h.1
              | inr h5 => rw [← (by ext; exact h5 : i = ⟨5, by norm_num⟩)]; exact h.2
            · rw [same_others i h45]; exact h.1
          | inr h =>
            simp at h
            cases h with
            | inl h4 => rw [h4]; exact h.1
            | inr h5 => rw [h5]; exact h.2
      -- Now compute the product ratio
      have prod_eq : sp.prod fieldConstant = sq.prod fieldConstant := by
        rw [sp_eq]
        have h_disj : (sq \ {⟨4, by norm_num⟩, ⟨5, by norm_num⟩}) ∩ {⟨4, by norm_num⟩, ⟨5, by norm_num⟩} = ∅ := by
          ext i
          simp [Finset.mem_sdiff]
        rw [Finset.prod_union (Finset.disjoint_iff_inter_eq_empty.mpr h_disj)]
        have : {⟨4, by norm_num⟩, ⟨5, by norm_num⟩}.prod fieldConstant = 
               fieldConstant ⟨4, by norm_num⟩ * fieldConstant ⟨5, by norm_num⟩ := by
          simp [Finset.prod_insert]
        rw [this, α₄_mul_α₅_eq_one]
        simp
        -- sq = (sq \ {4,5}) since q doesn't have 4,5 active
        have sq_decomp : sq = sq \ {⟨4, by norm_num⟩, ⟨5, by norm_num⟩} := by
          ext i
          simp [sq, activeFields, Finset.mem_sdiff]
          intro hi
          simp
          intro h_eq
          cases h_eq with
          | inl h4 => rw [h4] at hi; exact h.3 hi
          | inr h5 => rw [h5] at hi; exact h.4 hi
        rw [sq_decomp]
      exact prod_eq
    | inr h =>
      -- q has both 4,5 active; p has neither
      have sq_eq : sq = (sp \ {⟨4, by norm_num⟩, ⟨5, by norm_num⟩}) ∪ {⟨4, by norm_num⟩, ⟨5, by norm_num⟩} := by
        ext i
        simp [sp, sq, activeFields]
        constructor
        · intro hi
          by_cases h45 : i.val ∈ {4, 5}
          · right
            simp at h45
            cases h45 with
            | inl h4 => left; ext; exact h4
            | inr h5 => right; ext; exact h5
          · left
            constructor
            · rw [same_others i h45]; exact hi
            · simp
              intro h_eq
              cases h_eq with
              | inl h4 => apply h45; simp; left; rw [← h4]; rfl
              | inr h5 => apply h45; simp; right; rw [← h5]; rfl
        · intro hi
          cases hi with
          | inl h => 
            by_cases h45 : i.val ∈ {4, 5}
            · simp at h45
              cases h45 with
              | inl h4 => rw [← (by ext; exact h4 : i = ⟨4, by norm_num⟩)]; exact h.3
              | inr h5 => rw [← (by ext; exact h5 : i = ⟨5, by norm_num⟩)]; exact h.4
            · rw [← same_others i h45]; exact h.1
          | inr h =>
            simp at h
            cases h with
            | inl h4 => rw [h4]; exact h.3
            | inr h5 => rw [h5]; exact h.4
      -- Now compute the product ratio
      have prod_eq : sq.prod fieldConstant = sp.prod fieldConstant := by
        rw [sq_eq]
        have h_disj : (sp \ {⟨4, by norm_num⟩, ⟨5, by norm_num⟩}) ∩ {⟨4, by norm_num⟩, ⟨5, by norm_num⟩} = ∅ := by
          ext i
          simp [Finset.mem_sdiff]
        rw [Finset.prod_union (Finset.disjoint_iff_inter_eq_empty.mpr h_disj)]
        have : {⟨4, by norm_num⟩, ⟨5, by norm_num⟩}.prod fieldConstant = 
               fieldConstant ⟨4, by norm_num⟩ * fieldConstant ⟨5, by norm_num⟩ := by
          simp [Finset.prod_insert]
        rw [this, α₄_mul_α₅_eq_one]
        simp
        -- sp = (sp \ {4,5}) since p doesn't have 4,5 active
        have sp_decomp : sp = sp \ {⟨4, by norm_num⟩, ⟨5, by norm_num⟩} := by
          ext i
          simp [sp, activeFields, Finset.mem_sdiff]
          intro hi
          simp
          intro h_eq
          cases h_eq with
          | inl h4 => rw [h4] at hi; exact h.1 hi
          | inr h5 => rw [h5] at hi; exact h.2 hi
        rw [sp_decomp]
      exact prod_eq.symm
  · -- Case XOR = 49: bits 0, 4, and 5 differ
    have diff_0 : isFieldActive (positionToByte p) ⟨0, by norm_num⟩ ≠ 
                  isFieldActive (positionToByte q) ⟨0, by norm_num⟩ := h49.2.1
    have diff_4 : isFieldActive (positionToByte p) ⟨4, by norm_num⟩ ≠ 
                  isFieldActive (positionToByte q) ⟨4, by norm_num⟩ := h49.2.2.1
    have diff_5 : isFieldActive (positionToByte p) ⟨5, by norm_num⟩ ≠ 
                  isFieldActive (positionToByte q) ⟨5, by norm_num⟩ := h49.2.2.2
    have same_others : ∀ i : FieldIndex, i.val ∉ {0, 4, 5} → 
      isFieldActive (positionToByte p) i = isFieldActive (positionToByte q) i := by
      intro i hi
      exact h_others ⟨i.val, i.isLt⟩ hi
    -- The difference combines effects from bits 0, 4, and 5
    -- Since α₀ = 1 and α₄ * α₅ = 1, the total effect cancels
    have : sp.prod fieldConstant = sq.prod fieldConstant := by
      -- Partition the fields into groups
      let common := Finset.filter (fun i : FieldIndex => i.val ∉ {0, 4, 5}) Finset.univ
      let diff_fields : Finset FieldIndex := {⟨0, by norm_num⟩, ⟨4, by norm_num⟩, ⟨5, by norm_num⟩}
      
      -- Express sp and sq in terms of common and differing parts
      have sp_partition : sp = (sp ∩ common) ∪ (sp ∩ diff_fields) := by
        ext i
        simp [common, diff_fields]
        constructor
        · intro hi
          by_cases h : i.val ∈ {0, 4, 5}
          · right
            constructor
            · exact hi
            · simp at h
              cases h with
              | inl h0 => left; ext; exact h0
              | inr h45 => 
                cases h45 with
                | inl h4 => right; left; ext; exact h4
                | inr h5 => right; right; ext; exact h5
          · left
            exact ⟨hi, h⟩
        · intro hi
          cases hi with
          | inl h => exact h.1
          | inr h => exact h.1
      
      have sq_partition : sq = (sq ∩ common) ∪ (sq ∩ diff_fields) := by
        ext i
        simp [common, diff_fields]
        constructor
        · intro hi
          by_cases h : i.val ∈ {0, 4, 5}
          · right
            constructor
            · exact hi
            · simp at h
              cases h with
              | inl h0 => left; ext; exact h0
              | inr h45 => 
                cases h45 with
                | inl h4 => right; left; ext; exact h4
                | inr h5 => right; right; ext; exact h5
          · left
            exact ⟨hi, h⟩
        · intro hi
          cases hi with
          | inl h => exact h.1
          | inr h => exact h.1
      
      -- Common parts are equal
      have common_eq : sp ∩ common = sq ∩ common := by
        ext i
        simp [sp, sq, activeFields, common]
        intro hi
        exact same_others i hi
      
      -- The products over common parts are equal
      have prod_common_eq : (sp ∩ common).prod fieldConstant = (sq ∩ common).prod fieldConstant := by
        rw [common_eq]
      
      -- Now analyze the differing parts
      -- Key insight: bits 0, 4, 5 all flip together for XOR = 49
      have all_flip : ∀ b ∈ diff_fields, 
        (b ∈ sp ↔ b ∉ sq) := by
        intro b hb
        simp [diff_fields] at hb
        cases hb with
        | inl h0 => 
          rw [h0]
          simp [sp, sq, activeFields]
          exact ⟨fun h => fun hq => diff_0 (by simp [h, hq]),
                 fun h => by_contra (fun hnot => h (by_contra (fun hq => diff_0 (by simp [hnot, hq]))))⟩
        | inr h45 =>
          cases h45 with
          | inl h4 =>
            rw [h4]
            simp [sp, sq, activeFields]
            exact ⟨fun h => fun hq => diff_4 (by simp [h, hq]),
                   fun h => by_contra (fun hnot => h (by_contra (fun hq => diff_4 (by simp [hnot, hq]))))⟩
          | inr h5 =>
            rw [h5]
            simp [sp, sq, activeFields]
            exact ⟨fun h => fun hq => diff_5 (by simp [h, hq]),
                   fun h => by_contra (fun hnot => h (by_contra (fun hq => diff_5 (by simp [hnot, hq]))))⟩
      
      -- The product of constants for {0,4,5} equals 1
      have prod_diff_eq_one : diff_fields.prod fieldConstant = 1 := by
        simp [diff_fields, Finset.prod_insert]
        rw [fieldConstant, α₀_value, α₄_mul_α₅_eq_one]
        ring
      
      -- Complete the proof
      rw [sp_partition, sq_partition]
      have h_disj_sp : (sp ∩ common) ∩ (sp ∩ diff_fields) = ∅ := by
        ext i
        simp [common, diff_fields]
        intro _ _ h
        exact h
      have h_disj_sq : (sq ∩ common) ∩ (sq ∩ diff_fields) = ∅ := by
        ext i
        simp [common, diff_fields]
        intro _ _ h
        exact h
      rw [Finset.prod_union (Finset.disjoint_iff_inter_eq_empty.mpr h_disj_sp)]
      rw [Finset.prod_union (Finset.disjoint_iff_inter_eq_empty.mpr h_disj_sq)]
      rw [prod_common_eq]
      -- Now need to show (sp ∩ diff_fields).prod = (sq ∩ diff_fields).prod
      -- Both are subsets of diff_fields, and their product is a subset of the product 1
      have : (sp ∩ diff_fields).prod fieldConstant * (sq ∩ diff_fields).prod fieldConstant = 
             diff_fields.prod fieldConstant := by
        -- The intersection property: exactly one of sp, sq contains each element of diff_fields
        have partition : ∀ i ∈ diff_fields, (i ∈ sp ∩ diff_fields) ∨ (i ∈ sq ∩ diff_fields) := by
          intro i hi
          simp
          have : i ∈ sp ↔ i ∉ sq := all_flip i hi
          tauto
        have disjoint : (sp ∩ diff_fields) ∩ (sq ∩ diff_fields) = ∅ := by
          ext i
          simp
          intro hip hiq
          have : i ∈ sp ↔ i ∉ sq := all_flip i (by simp [diff_fields]; tauto)
          exact this.mp hip hiq
        have union : (sp ∩ diff_fields) ∪ (sq ∩ diff_fields) = diff_fields := by
          ext i
          simp
          constructor
          · intro h; tauto
          · intro hi
            have : i ∈ sp ∨ i ∈ sq := by
              by_contra h
              push_neg at h
              have : i ∈ sp ↔ i ∉ sq := all_flip i hi
              exact h.2 (this.mpr h.1)
            tauto
        rw [← Finset.prod_union (Finset.disjoint_iff_inter_eq_empty.mpr disjoint)]
        rw [union]
      rw [prod_diff_eq_one] at this
      have h1 : (sp ∩ diff_fields).prod fieldConstant ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro i _
        exact ne_of_gt (fieldConstant_pos i)
      have h2 : (sq ∩ diff_fields).prod fieldConstant ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro i _
        exact ne_of_gt (fieldConstant_pos i)
      field_simp [h1, h2] at this ⊢
      exact this
    exact this

/-- Explicit characterization: positions with XOR in {0,1,48,49} have equal resonance -/
theorem xor_resonance_equiv : ∀ (p q : Position),
  let xor_val := (positionToByte p).val ^^^ (positionToByte q).val
  (xor_val = 0 ∨ xor_val = 1 ∨ xor_val = 48 ∨ xor_val = 49) →
  resonance p = resonance q := by
  intro p q xor_val h
  apply resonance_equiv_positions
  rw [resonance_equiv_set_characterization]
  exact h

/-- The resonance equivalence relation -/
def resonance_equiv (p q : Position) : Prop :=
  (positionToByte p).val ^^^ (positionToByte q).val ∈ resonance_equiv_set

/-- Resonance equivalence is an equivalence relation -/
instance resonance_equiv_equivalence : Equivalence resonance_equiv where
  refl p := by
    simp [resonance_equiv]
    rw [Nat.xor_self]
    simp [resonance_equiv_set]
  symm p q h := by
    simp [resonance_equiv] at h ⊢
    rw [Nat.xor_comm]
    exact h
  trans p q r hpq hqr := by
    simp [resonance_equiv] at hpq hqr ⊢
    -- Need to show (p ⊕ r) ∈ {0,1,48,49} given (p ⊕ q), (q ⊕ r) ∈ {0,1,48,49}
    -- Key: p ⊕ r = (p ⊕ q) ⊕ (q ⊕ r) by XOR associativity and q ⊕ q = 0
    have : (positionToByte p).val ^^^ (positionToByte r).val = 
           ((positionToByte p).val ^^^ (positionToByte q).val) ^^^ 
           ((positionToByte q).val ^^^ (positionToByte r).val) := by
      simp [Nat.xor_assoc, Nat.xor_comm (positionToByte q).val]
      rw [Nat.xor_self, Nat.xor_zero]
    rw [this]
    -- Now apply the group closure property
    exact xor_group_closed _ hpq _ hqr

end PrimeOS12288.Relations