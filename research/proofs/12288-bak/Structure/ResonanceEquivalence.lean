/-
  Structure.ResonanceEquivalence - Equivalence relation for resonance
  
  This module defines the resonance equivalence relation and proves
  it is indeed an equivalence relation with the key property that
  equivalent positions have the same resonance value.
-/

import Structure.ResonancePreservation
import Structure.FieldActivation
import Mathlib.Data.Finset.Basic

namespace Structure

open Basic Constants Relations

-- Define the equivalence relation
def resonance_equiv (n m : Fin 256) : Prop :=
  n.val ^^^ m.val ∈ resonance_preserving_xors

-- Prove it's an equivalence relation
lemma resonance_equiv_refl : Reflexive resonance_equiv := by
  intro n
  unfold resonance_equiv resonance_preserving_xors
  simp only [Finset.mem_insert, Finset.mem_singleton]
  left; left; left
  exact Nat.xor_self n.val

lemma resonance_equiv_symm : Symmetric resonance_equiv := by
  intro n m h
  unfold resonance_equiv at h ⊢
  rw [Nat.xor_comm]
  exact h

-- Helper: {0, 1, 48, 49} is closed under XOR
lemma preserving_xors_closed (a b : Nat) 
  (ha : a ∈ resonance_preserving_xors) (hb : b ∈ resonance_preserving_xors) :
  a ^^^ b ∈ resonance_preserving_xors := by
  unfold resonance_preserving_xors at ha hb ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb ⊢
  -- Check all 16 cases
  cases ha with
  | inl ha => cases ha with
    | inl ha => cases ha with
      | inl ha => -- a = 0
        subst ha
        simp only [Nat.zero_xor]
        exact hb
      | inr ha => -- a = 1
        subst ha
        cases hb with
        | inl hb => cases hb with
          | inl hb => cases hb with
            | inl hb => -- b = 0
              subst hb; simp; right; left; left; rfl
            | inr hb => -- b = 1
              subst hb; simp; left; left; left; rfl
          | inr hb => -- b = 48
            subst hb; simp; right; norm_num
        | inr hb => -- b = 49
          subst hb; simp; left; right; norm_num
    | inr ha => -- a = 48
      subst ha
      cases hb with
      | inl hb => cases hb with
        | inl hb => cases hb with
          | inl hb => -- b = 0
            subst hb; simp; left; right; rfl
          | inr hb => -- b = 1
            subst hb; simp; right; norm_num
        | inr hb => -- b = 48
          subst hb; simp; left; left; left; rfl
      | inr hb => -- b = 49
        subst hb; simp; right; left; left; norm_num
  | inr ha => -- a = 49
    subst ha
    cases hb with
    | inl hb => cases hb with
      | inl hb => cases hb with
        | inl hb => -- b = 0
          subst hb; simp; right; rfl
        | inr hb => -- b = 1
          subst hb; simp; left; right; norm_num
      | inr hb => -- b = 48
        subst hb; simp; right; left; left; norm_num
    | inr hb => -- b = 49
      subst hb; simp; left; left; left; rfl

lemma resonance_equiv_trans : Transitive resonance_equiv := by
  intro n m k hnm hmk
  unfold resonance_equiv at hnm hmk ⊢
  -- Use associativity of XOR and closure
  have : n.val ^^^ k.val = (n.val ^^^ m.val) ^^^ (m.val ^^^ k.val) := by
    rw [← Nat.xor_assoc, Nat.xor_assoc n.val, Nat.xor_self, Nat.xor_zero]
  rw [this]
  exact preserving_xors_closed _ _ hnm hmk

-- Equivalent positions have the same resonance
lemma equiv_same_resonance (n m : Fin 256) :
  resonance_equiv n m → resonance n = resonance m := by
  intro h
  unfold resonance_equiv resonance_preserving_xors at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  cases h with
  | inl h => cases h with
    | inl h => cases h with
      | inl h => 
        -- n XOR m = 0, so n = m
        have : n = m := by
          ext
          exact Nat.xor_left_inj.mp h
        rw [this]
      | inr h => 
        -- n XOR m = 1
        have : m = ⟨n.val ^^^ 1, by omega⟩ := by
          ext
          simp only [Fin.val_mk]
          rw [← h, Nat.xor_comm, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
        rw [this]
        exact xor_one_preserves_resonance n
    | inr h => 
      -- n XOR m = 48
      have : m = ⟨n.val ^^^ 48, by omega⟩ := by
          ext
          simp only [Fin.val_mk]
          rw [← h, Nat.xor_comm, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      rw [this]
      exact xor_48_preserves_resonance n
  | inr h => 
    -- n XOR m = 49 = 1 XOR 48
    have : m = ⟨n.val ^^^ 49, by omega⟩ := by
          ext
          simp only [Fin.val_mk]
          rw [← h, Nat.xor_comm, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    rw [this]
    -- 49 = 1 XOR 48, so apply both transformations
    have : n.val ^^^ 49 = (n.val ^^^ 1) ^^^ 48 := by
      rw [← Nat.xor_assoc]; norm_num
    rw [this]
    rw [← xor_48_preserves_resonance ⟨n.val ^^^ 1, by omega⟩]
    rw [← xor_one_preserves_resonance n]

-- The resonance of position n depends only on n mod 256
lemma resonance_mod_256 (n : Fin 12288) :
  resonance n = resonance ⟨n.val % 256, by omega⟩ := by
  unfold resonance activated_fields
  congr 1
  ext i
  simp only [List.mem_filter, List.mem_finRange, and_congr_right_iff]
  intro hi
  -- For bit positions < 8, n.testBit i = (n % 256).testBit i
  have h : n.val.testBit i.val = (n.val % 256).testBit i.val := by
    unfold Basic.Nat.testBit
    have : n.val % 256 = n.val % (2^8) := by norm_num
    rw [this]
    have shift_eq : (n.val >>> i.val) % 2 = ((n.val % 2^8) >>> i.val) % 2 := by
      have ⟨q, hq⟩ : ∃ q, n.val = q * 2^8 + n.val % 2^8 := by
        use n.val / 2^8
        exact (Nat.div_add_mod n.val (2^8)).symm
      rw [hq]
      have hi8 : i.val < 8 := i.isLt
      rw [Nat.add_shiftRight_eq]
      have h_even : 2 ∣ q * 2^(8 - i.val) := by
        apply Nat.dvd_mul_of_dvd_right
        apply Nat.pow_dvd_pow 2
        omega
      rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd h_even, zero_add, Nat.mod_mod_of_dvd]
      · rfl
      · norm_num
    exact shift_eq
  exact h

-- Since resonance only depends on n mod 256, we only need to check 256 values
lemma resonance_values_bounded :
  Finset.image resonance (Finset.univ : Finset (Fin 12288)) =
  Finset.image resonance (Finset.univ : Finset (Fin 256)) := by
  ext r
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro ⟨n, hn⟩
    use ⟨n.val % 256, by omega⟩
    rw [← hn, resonance_mod_256]
  · intro ⟨m, hm⟩
    use ⟨m.val, by omega⟩
    simp only [← hm]
    rw [resonance_mod_256]
    congr
    simp

end Structure