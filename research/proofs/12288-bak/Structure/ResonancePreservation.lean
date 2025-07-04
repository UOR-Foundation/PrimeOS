/-
  Structure.ResonancePreservation - Core lemmas about XOR preserving resonance
  
  This module proves the key lemmas showing that XOR with certain values
  preserves resonance due to field constant relationships.
-/

import Structure.FieldActivation
import Structure.XORHelpers
import Structure.ListProductHelpers
import Relations.UnityProduct
import Constants.Alpha0
import Mathlib.Data.Finset.Card

namespace Structure

open Basic Constants Relations

-- Key insight: XOR patterns that preserve resonance
def resonance_preserving_xors : Finset Nat := {0, 1, 48, 49}

-- Helper: activated fields relationship for XOR 1
lemma activated_fields_xor_1 (n : Fin 256) :
  activated_fields ⟨n.val ^^^ 1, by omega⟩ = 
  if n.val.testBit 0 then 
    (activated_fields n).filter (fun i => i.val ≠ 0)
  else 
    ⟨0, by norm_num⟩ :: activated_fields n := by
  unfold activated_fields
  ext i
  simp only [List.mem_filter, List.mem_finRange, List.mem_cons]
  constructor
  · intro ⟨hi_range, hi_test⟩
    split_ifs with h0
    · -- n has bit 0 set
      constructor
      · constructor
        · exact hi_range
        · unfold Basic.Nat.testBit at hi_test
          by_cases hi0 : i.val = 0
          · subst hi0
            rw [bit_0_xor_1, h0] at hi_test
            simp at hi_test
          · rw [bit_i_xor_1 _ _ hi0] at hi_test
            exact hi_test
      · exact fun h => h
    · -- n has bit 0 clear
      by_cases hi0 : i = 0
      · left; exact hi0
      · right
        constructor
        · exact hi_range
        · have : i.val ≠ 0 := by intro h; apply hi0; ext; exact h
          rw [bit_i_xor_1 _ _ this] at hi_test
          exact hi_test
  · intro h
    split_ifs with h0 at h
    · -- n has bit 0 set, n ^^^ 1 has bit 0 clear
      obtain ⟨⟨hi_range, hi_test⟩, hi_ne⟩ := h
      constructor
      · exact hi_range
      · by_cases hi0 : i.val = 0
        · subst hi0; simp at hi_ne
        · rw [bit_i_xor_1 _ _ hi0]; exact hi_test
    · -- n has bit 0 clear, n ^^^ 1 has bit 0 set
      cases h with
      | inl h => 
        subst h
        constructor
        · norm_num
        · rw [bit_0_xor_1, h0]; simp
      | inr h =>
        constructor
        · exact h.1
        · have : i.val ≠ 0 := by
            intro heq
            have : i = 0 := by ext; exact heq
            subst this
            simp at h
          rw [bit_i_xor_1 _ _ this]
          exact h.2

-- The key lemma: XOR with 1 preserves resonance (because α₀ = 1)
lemma xor_one_preserves_resonance (n : Fin 256) :
  resonance ⟨n.val ^^^ 1, by omega⟩ = resonance n := by
  unfold resonance
  rw [activated_fields_xor_1]
  split_ifs with h0
  · -- n has bit 0 set, so n ^^^ 1 doesn't
    -- activated_fields n contains 0, activated_fields (n ^^^ 1) doesn't
    have h_mem : ⟨0, by norm_num⟩ ∈ activated_fields n := by
      simp [activated_fields, h0]
    rw [← list_prod_erase_one]
    · congr 1
      ext i
      simp only [List.mem_map, List.mem_filter, List.mem_erase]
      constructor
      · intro ⟨j, ⟨hj, hj_ne⟩, hi⟩
        use j
        constructor
        · exact ⟨hj, fun h => hj_ne h.symm⟩
        · exact hi
      · intro ⟨j, ⟨hj, hj_ne⟩, hi⟩
        use j
        subst hi
        exact ⟨⟨hj.1, hj_ne⟩, rfl⟩
    · rw [α₀_eq_one]; rfl
    · simp only [List.mem_map]
      use ⟨0, by norm_num⟩
      exact ⟨h_mem, rfl⟩
  · -- n has bit 0 clear, so n ^^^ 1 has it set
    -- activated_fields (n ^^^ 1) = 0 :: activated_fields n
    rw [List.map_cons, List.prod_cons]
    simp only [α, α₀_eq_one, one_mul]

-- Helper: When both bits 4 and 5 flip together, we multiply/divide by α₄ and α₅
lemma activated_fields_xor_48_case (n : Fin 256) (h4 : n.val.testBit 4) (h5 : n.val.testBit 5) :
  (activated_fields ⟨n.val ^^^ 48, by omega⟩).map α = 
  ((activated_fields n).filter (fun i => i.val ≠ 4 ∧ i.val ≠ 5)).map α := by
  unfold activated_fields
  ext x
  simp only [List.mem_map, List.mem_filter, List.mem_finRange]
  constructor
  · intro ⟨i, ⟨hi_lt, hi_test⟩, hx⟩
    by_cases hi4 : i.val = 4
    · -- i = 4, but bit 4 is flipped in n ^^^ 48
      subst hi4
      rw [xor_48_bits] at hi_test
      simp [h4] at hi_test
    by_cases hi5 : i.val = 5
    · -- i = 5, but bit 5 is flipped in n ^^^ 48
      subst hi5  
      rw [xor_48_bits] at hi_test
      simp [h5] at hi_test
    · -- i ≠ 4 and i ≠ 5
      use i
      constructor
      · constructor
        · constructor
          · exact hi_lt
          · rw [xor_48_bits] at hi_test
            simp [hi4, hi5] at hi_test
            exact hi_test
        · exact ⟨hi4, hi5⟩
      · exact hx
  · intro ⟨i, ⟨⟨hi_lt, hi_test⟩, ⟨hi4, hi5⟩⟩, hx⟩
    use i
    constructor
    · constructor
      · exact hi_lt
      · rw [xor_48_bits]
        simp [hi4, hi5]
        exact hi_test
    · exact hx

-- Helper: Split activated fields into those involving bits 4,5 and others
lemma split_activated_fields_4_5 (n : Fin 256) :
  ∃ (others : List (Fin 8)) (with_4_5 : List (Fin 8)),
    (∀ i ∈ others, i.val ≠ 4 ∧ i.val ≠ 5) ∧
    (∀ i ∈ with_4_5, i.val = 4 ∨ i.val = 5) ∧
    activated_fields n = others ++ with_4_5 ∧
    (activated_fields n).map α |>.prod = (others.map α).prod * (with_4_5.map α).prod := by
  use (activated_fields n).filter (fun i => i.val ≠ 4 ∧ i.val ≠ 5)
  use (activated_fields n).filter (fun i => i.val = 4 ∨ i.val = 5)
  constructor
  · intro i hi
    simp only [List.mem_filter] at hi
    exact hi.2
  constructor
  · intro i hi
    simp only [List.mem_filter] at hi
    exact hi.2
  constructor
  · ext i
    simp only [List.mem_append, List.mem_filter]
    constructor
    · intro hi
      by_cases h : i.val = 4 ∨ i.val = 5
      · right; exact ⟨hi, h⟩
      · left; exact ⟨hi, by push_neg at h ⊢; exact h⟩
    · intro h
      cases h with
      | inl h => exact h.1
      | inr h => exact h.1
  · rw [← List.prod_append]
    congr
    rw [List.map_append]

-- Simplified: XOR with 48 preserves resonance
lemma xor_48_preserves_resonance (n : Fin 256) :
  resonance ⟨n.val ^^^ 48, by omega⟩ = resonance n := by
  -- Key insight: XOR 48 toggles bits 4 and 5 together
  -- Since α 4 * α 5 = 1, this preserves the product
  have unity : α 4 * α 5 = 1 := unity_product
  
  unfold resonance
  -- Let's work with the change in activated fields
  -- XOR 48 flips bits 4 and 5, leaving others unchanged
  
  -- First, establish relationship between activated fields
  have h_fields : ∀ i : Fin 8, i ∈ activated_fields ⟨n.val ^^^ 48, by omega⟩ ↔ 
    if i.val = 4 then ¬(n.val.testBit 4)
    else if i.val = 5 then ¬(n.val.testBit 5)  
    else n.val.testBit i.val := by
    intro i
    simp [activated_fields]
    constructor
    · intro ⟨_, h⟩
      split_ifs with h4 h5
      · subst h4
        rw [xor_48_bits] at h
        simp at h
        exact h
      · subst h5
        rw [xor_48_bits] at h
        simp at h
        exact h
      · rw [xor_48_bits] at h
        simp [h4, h5] at h
        exact h
    · intro h
      constructor
      · exact i.isLt
      · split_ifs at h with h4 h5
        · subst h4
          rw [xor_48_bits]
          simp [h]
        · subst h5
          rw [xor_48_bits]
          simp [h]
        · rw [xor_48_bits]
          simp [h4, h5, h]
  
  -- Now prove the products are equal by considering all cases
  by_cases h4 : n.val.testBit 4
  · by_cases h5 : n.val.testBit 5
    · -- Case: both bits 4,5 are set in n
      -- After XOR 48: both cleared
      -- Product loses α 4 * α 5 = 1
      have h_remove : (activated_fields n).map α |>.prod = 
        α 4 * α 5 * ((activated_fields ⟨n.val ^^^ 48, by omega⟩).map α |>.prod) := by
        -- n has 4,5 activated; n XOR 48 doesn't
        have h4_in : ⟨4, by norm_num⟩ ∈ activated_fields n := by
          simp [activated_fields, h4]
        have h5_in : ⟨5, by norm_num⟩ ∈ activated_fields n := by
          simp [activated_fields, h5]
        have h4_out : ⟨4, by norm_num⟩ ∉ activated_fields ⟨n.val ^^^ 48, by omega⟩ := by
          intro h_in
          rw [h_fields] at h_in
          simp [h4] at h_in
        have h5_out : ⟨5, by norm_num⟩ ∉ activated_fields ⟨n.val ^^^ 48, by omega⟩ := by
          intro h_in
          rw [h_fields] at h_in
          simp [h5] at h_in
        -- The difference is exactly α 4 * α 5
        have h_diff : activated_fields n = 
          ⟨4, by norm_num⟩ :: ⟨5, by norm_num⟩ :: 
          (activated_fields n).filter (fun i => i.val ≠ 4 ∧ i.val ≠ 5) := by
          ext i
          simp [List.mem_cons, List.mem_filter]
          constructor
          · intro hi
            by_cases hi4 : i = ⟨4, by norm_num⟩
            · left; exact hi4
            · by_cases hi5 : i = ⟨5, by norm_num⟩
              · right; left; exact hi5
              · right; right
                constructor
                · exact hi
                · push_neg
                  constructor
                  · intro h; apply hi4; ext; exact h
                  · intro h; apply hi5; ext; exact h
          · intro h
            cases h with
            | inl h => subst h; exact h4_in
            | inr h => cases h with
              | inl h => subst h; exact h5_in
              | inr h => exact h.1
        have h_same : (activated_fields n).filter (fun i => i.val ≠ 4 ∧ i.val ≠ 5) =
          activated_fields ⟨n.val ^^^ 48, by omega⟩ := by
          ext i
          simp [List.mem_filter]
          constructor
          · intro ⟨hi, hne⟩
            rw [h_fields]
            split_ifs with hi4 hi5
            · subst hi4; simp at hne
            · subst hi5; simp at hne
            · simp [activated_fields] at hi
              exact hi.2
          · intro hi
            constructor
            · simp [activated_fields]
              rw [h_fields] at hi
              split_ifs at hi with hi4 hi5
              · subst hi4
                constructor
                · norm_num
                · exact h4
              · subst hi5
                constructor 
                · norm_num
                · exact h5
              · exact ⟨i.isLt, hi⟩
            · push_neg
              constructor
              · intro h
                rw [h_fields] at hi
                simp [h] at hi
                exact absurd h4 hi
              · intro h
                rw [h_fields] at hi
                split_ifs at hi with hi4
                · contradiction
                · simp [h] at hi
                  exact absurd h5 hi
        rw [h_diff]
        simp [List.map_cons, List.prod_cons, h_same]
        ring
      rw [unity] at h_remove
      simp at h_remove
      exact h_remove.symm
    · -- Case: bit 4 set, bit 5 clear in n
      -- After XOR 48: bit 4 clear, bit 5 set
      -- Product exchanges α 4 for α 5, but α 5 = 1/α 4
      have h_inv : α 5 = (α 4)⁻¹ := by
        rw [← one_div, ← unity]
        field_simp
      -- The activated fields change by swapping 4 and 5
      have h4_in : ⟨4, by norm_num⟩ ∈ activated_fields n := by
        simp [activated_fields, h4]
      have h5_out : ⟨5, by norm_num⟩ ∉ activated_fields n := by
        simp [activated_fields, h5]
      have h4_out : ⟨4, by norm_num⟩ ∉ activated_fields ⟨n.val ^^^ 48, by omega⟩ := by
        intro h_in
        rw [h_fields] at h_in
        simp [h4] at h_in
      have h5_in : ⟨5, by norm_num⟩ ∈ activated_fields ⟨n.val ^^^ 48, by omega⟩ := by
        rw [h_fields]
        simp [h5]
      -- Express the change in product
      have h_prod_n : (activated_fields n).map α |>.prod = 
        α 4 * ((activated_fields n).filter (fun i => i.val ≠ 4)).map α |>.prod := by
        rw [← list_prod_erase_of_mem _ _ h4_in]
        congr
        ext i
        simp [List.mem_erase, List.mem_filter]
        constructor
        · intro ⟨hne, hi⟩
          exact ⟨hi, by intro h; apply hne; ext; exact h⟩
        · intro ⟨hi, hne⟩
          constructor
          · intro h; apply hne; cases h; rfl
          · exact hi
      have h_prod_xor : (activated_fields ⟨n.val ^^^ 48, by omega⟩).map α |>.prod = 
        α 5 * ((activated_fields ⟨n.val ^^^ 48, by omega⟩).filter (fun i => i.val ≠ 5)).map α |>.prod := by
        rw [← list_prod_erase_of_mem _ _ h5_in]
        congr
        ext i
        simp [List.mem_erase, List.mem_filter]
        constructor
        · intro ⟨hne, hi⟩
          exact ⟨hi, by intro h; apply hne; ext; exact h⟩
        · intro ⟨hi, hne⟩
          constructor
          · intro h; apply hne; cases h; rfl
          · exact hi
      -- The filtered lists are the same (excluding 4 from n, excluding 5 from n^^48)
      have h_same : (activated_fields n).filter (fun i => i.val ≠ 4) =
        (activated_fields ⟨n.val ^^^ 48, by omega⟩).filter (fun i => i.val ≠ 5) := by
        ext i
        simp [List.mem_filter]
        constructor
        · intro ⟨hi, hne⟩
          constructor
          · rw [h_fields]
            split_ifs with hi4 hi5
            · contradiction
            · subst hi5
              simp [activated_fields] at hi
              exact absurd hi.2 h5
            · simp [activated_fields] at hi
              exact hi.2
          · by_cases hi5 : i.val = 5
            · subst hi5
              simp [activated_fields] at hi
              exact absurd hi.2 h5
            · exact hi5
        · intro ⟨hi, hne⟩
          constructor
          · simp [activated_fields]
            rw [h_fields] at hi
            split_ifs at hi with hi4 hi5
            · subst hi4
              exact ⟨by norm_num, h4⟩
            · contradiction
            · exact ⟨i.isLt, hi⟩
          · intro hi4
            rw [h_fields] at hi
            simp [hi4] at hi
            exact absurd h4 hi
      rw [h_prod_n, h_prod_xor, h_same, h_inv]
      simp
  · by_cases h5 : n.val.testBit 5
    · -- Case: bit 4 clear, bit 5 set in n
      -- Similar to previous case with roles swapped
      have h_inv : α 4 = (α 5)⁻¹ := by
        have : α 5 * α 4 = 1 := by rw [mul_comm, unity]
        rw [← one_div, ← this]
        field_simp
      -- After XOR 48: bit 4 set, bit 5 clear
      have h4_out : ⟨4, by norm_num⟩ ∉ activated_fields n := by
        simp [activated_fields, h4]
      have h5_in : ⟨5, by norm_num⟩ ∈ activated_fields n := by
        simp [activated_fields, h5]
      have h4_in : ⟨4, by norm_num⟩ ∈ activated_fields ⟨n.val ^^^ 48, by omega⟩ := by
        rw [h_fields]
        simp [h4]
      have h5_out : ⟨5, by norm_num⟩ ∉ activated_fields ⟨n.val ^^^ 48, by omega⟩ := by
        intro h_in
        rw [h_fields] at h_in
        simp [h5] at h_in
      -- Similar proof structure
      have h_prod_n : (activated_fields n).map α |>.prod = 
        α 5 * ((activated_fields n).filter (fun i => i.val ≠ 5)).map α |>.prod := by
        rw [← list_prod_erase_of_mem _ _ h5_in]
        congr
        ext i
        simp [List.mem_erase, List.mem_filter]
      have h_prod_xor : (activated_fields ⟨n.val ^^^ 48, by omega⟩).map α |>.prod = 
        α 4 * ((activated_fields ⟨n.val ^^^ 48, by omega⟩).filter (fun i => i.val ≠ 4)).map α |>.prod := by
        rw [← list_prod_erase_of_mem _ _ h4_in]
        congr
        ext i
        simp [List.mem_erase, List.mem_filter]
      have h_same : (activated_fields n).filter (fun i => i.val ≠ 5) =
        (activated_fields ⟨n.val ^^^ 48, by omega⟩).filter (fun i => i.val ≠ 4) := by
        ext i
        simp [List.mem_filter]
        constructor
        · intro ⟨hi, hne⟩
          constructor
          · rw [h_fields]
            split_ifs with hi4 hi5
            · subst hi4
              simp [activated_fields] at hi
              exact absurd hi.2 h4
            · contradiction
            · simp [activated_fields] at hi
              exact hi.2
          · by_cases hi4 : i.val = 4
            · subst hi4
              simp [activated_fields] at hi
              exact absurd hi.2 h4
            · exact hi4
        · intro ⟨hi, hne⟩
          constructor
          · simp [activated_fields]
            rw [h_fields] at hi
            split_ifs at hi with hi4 hi5
            · contradiction
            · subst hi5
              exact ⟨by norm_num, h5⟩
            · exact ⟨i.isLt, hi⟩
          · intro hi5
            rw [h_fields] at hi
            split_ifs at hi with hi4
            · contradiction
            · simp [hi5] at hi
              exact absurd h5 hi
      rw [h_prod_n, h_prod_xor, h_same, h_inv]
      simp
    · -- Case: both bits 4,5 clear in n
      -- After XOR 48: both set
      -- Product gains α 4 * α 5 = 1
      have h4_out : ⟨4, by norm_num⟩ ∉ activated_fields n := by
        simp [activated_fields, h4]
      have h5_out : ⟨5, by norm_num⟩ ∉ activated_fields n := by
        simp [activated_fields, h5]
      have h4_in : ⟨4, by norm_num⟩ ∈ activated_fields ⟨n.val ^^^ 48, by omega⟩ := by
        rw [h_fields]
        simp [h4]
      have h5_in : ⟨5, by norm_num⟩ ∈ activated_fields ⟨n.val ^^^ 48, by omega⟩ := by
        rw [h_fields]
        simp [h5]
      -- Express the difference
      have h_add : (activated_fields ⟨n.val ^^^ 48, by omega⟩).map α |>.prod = 
        α 4 * α 5 * ((activated_fields n).map α |>.prod) := by
        have h_same : activated_fields n = 
          (activated_fields ⟨n.val ^^^ 48, by omega⟩).filter (fun i => i.val ≠ 4 ∧ i.val ≠ 5) := by
          ext i
          simp [List.mem_filter]
          constructor
          · intro hi
            constructor
            · rw [h_fields]
              split_ifs with hi4 hi5
              · subst hi4
                simp [activated_fields] at hi
                exact absurd hi.2 h4
              · subst hi5
                simp [activated_fields] at hi
                exact absurd hi.2 h5
              · simp [activated_fields] at hi
                exact hi.2
            · push_neg
              constructor
              · intro h
                subst h
                contradiction
              · intro h
                subst h
                contradiction
          · intro ⟨hi, hne⟩
            simp [activated_fields]
            rw [h_fields] at hi
            split_ifs at hi with hi4 hi5
            · contradiction
            · contradiction
            · exact ⟨i.isLt, hi⟩
        have h_diff : activated_fields ⟨n.val ^^^ 48, by omega⟩ = 
          ⟨4, by norm_num⟩ :: ⟨5, by norm_num⟩ :: activated_fields n := by
          ext i
          simp [List.mem_cons]
          constructor
          · intro hi
            by_cases hi4 : i = ⟨4, by norm_num⟩
            · left; exact hi4
            · by_cases hi5 : i = ⟨5, by norm_num⟩
              · right; left; exact hi5
              · right; right
                rw [← h_same]
                simp [List.mem_filter]
                exact ⟨hi, by push_neg; exact ⟨by intro h; apply hi4; ext; exact h, 
                                                by intro h; apply hi5; ext; exact h⟩⟩
          · intro h
            cases h with
            | inl h => subst h; exact h4_in
            | inr h => cases h with
              | inl h => subst h; exact h5_in
              | inr h => 
                rw [← h_same] at h
                simp [List.mem_filter] at h
                exact h.1
        rw [h_diff]
        simp [List.map_cons, List.prod_cons]
        ring
      rw [unity] at h_add
      simp at h_add
      exact h_add

end Structure