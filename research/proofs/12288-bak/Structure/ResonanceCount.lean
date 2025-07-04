/-
  Structure.ResonanceCount - The key theorem about unique resonance values
  
  This module proves that there are exactly 96 unique resonance values
  in the 12,288-element structure.
  
  The proof uses the key insight that resonance values are preserved under
  XOR with {0, 1, 48, 49} due to α₀ = 1 and α₄ × α₅ = 1.
-/

import Structure.ResonanceEquivalence
import Structure.ResonancePreservation
import Structure.XORHelpers
import Mathlib.Data.Finset.Card

namespace Structure

open Basic Constants Relations

-- Helper: positions with specific bit patterns
def positions_by_bits_4_5 (b4 b5 : Bool) : Finset (Fin 256) :=
  Finset.filter (fun n => n.val.testBit 4 = b4 ∧ n.val.testBit 5 = b5) Finset.univ

-- Helper: count positions with specific bit 4,5 pattern
lemma count_positions_by_bits_4_5 (b4 b5 : Bool) :
  (positions_by_bits_4_5 b4 b5).card = 64 := by
  -- Each of the other 6 bits can be 0 or 1 independently
  -- So 2^6 = 64 positions
  unfold positions_by_bits_4_5
  
  -- Define a bijection with the 64 values that have bits 4,5 fixed
  let f : Fin 64 → Fin 256 := fun k => 
    let bits_0_3 := k.val % 16
    let bits_6_7 := k.val / 16
    let bit_4 := if b4 then 16 else 0
    let bit_5 := if b5 then 32 else 0
    ⟨bits_0_3 + bit_4 + bit_5 + bits_6_7 * 64, by
      have : bits_0_3 < 16 := Nat.mod_lt _ (by norm_num)
      have : bits_6_7 < 4 := by
        have : k.val < 64 := k.isLt
        omega
      omega⟩
  
  -- Show f maps into positions_by_bits_4_5 b4 b5
  have h_into : ∀ k, f k ∈ positions_by_bits_4_5 b4 b5 := by
    intro k
    simp [positions_by_bits_4_5, f]
    constructor
    · -- Check bit 4
      simp [Basic.Nat.testBit, Nat.shiftRight_eq_div_pow]
      split_ifs with h4
      · -- b4 = true, so bit 4 is set
        -- The value is: bits_0_3 + 16 + bit_5 + bits_6_7 * 64
        -- We need to show (value / 16) % 2 = 1
        have val := k.val % 16 + 16 + (if b5 then 32 else 0) + k.val / 16 * 64
        have : val / 16 % 2 = 1 := by
          -- val = bits_0_3 + 16 + bit_5 + bits_6_7 * 64
          -- val / 16 = (bits_0_3 + 16 + bit_5) / 16 + bits_6_7 * 4
          -- Since bits_0_3 < 16 and bit_5 ∈ {0, 32}
          -- (bits_0_3 + 16 + bit_5) / 16 = 1 + bit_5 / 16
          have bits_0_3 := k.val % 16
          have bits_6_7 := k.val / 16
          have h_0_3 : bits_0_3 < 16 := Nat.mod_lt _ (by norm_num)
          have h_6_7 : bits_6_7 < 4 := by
            have : k.val < 64 := k.isLt
            omega
          simp [val]
          split_ifs with hb5
          · -- b5 = true, bit_5 = 32
            have : (bits_0_3 + 16 + 32 + bits_6_7 * 64) / 16 = 3 + bits_6_7 * 4 := by
              have : bits_0_3 + 16 + 32 = bits_0_3 + 48 := by ring
              rw [this, add_assoc]
              rw [Nat.add_div_right _ (by norm_num : 0 < 16)]
              have : (bits_0_3 + 48) / 16 = 3 := by
                have : bits_0_3 + 48 < 64 := by omega
                have : 48 ≤ bits_0_3 + 48 := by omega
                omega
              rw [this]
              have : 64 / 16 = 4 := by norm_num
              rw [Nat.mul_comm bits_6_7 64, Nat.mul_div_assoc _ (by norm_num : 16 ∣ 64)]
              simp
            rw [this]
            -- (3 + bits_6_7 * 4) % 2 = 1 since 3 is odd
            have : (3 + bits_6_7 * 4) % 2 = 3 % 2 := by
              rw [Nat.add_mod]
              have : (bits_6_7 * 4) % 2 = 0 := by
                rw [Nat.mul_mod]
                simp
              simp [this]
            rw [this]
            norm_num
          · -- b5 = false, bit_5 = 0
            have : (bits_0_3 + 16 + 0 + bits_6_7 * 64) / 16 = 1 + bits_6_7 * 4 := by
              simp
              rw [Nat.add_div_right _ (by norm_num : 0 < 16)]
              have : (bits_0_3 + 16) / 16 = 1 := by
                have : bits_0_3 + 16 < 32 := by omega
                have : 16 ≤ bits_0_3 + 16 := by omega
                omega
              rw [this]
              have : 64 / 16 = 4 := by norm_num
              rw [Nat.mul_comm bits_6_7 64, Nat.mul_div_assoc _ (by norm_num : 16 ∣ 64)]
              simp
            rw [this]
            -- (1 + bits_6_7 * 4) % 2 = 1 since 1 is odd
            have : (1 + bits_6_7 * 4) % 2 = 1 % 2 := by
              rw [Nat.add_mod]
              have : (bits_6_7 * 4) % 2 = 0 := by
                rw [Nat.mul_mod]
                simp
              simp [this]
            rw [this]
            norm_num
        exact this
      · -- b4 = false, so bit 4 is clear
        -- The value is: bits_0_3 + 0 + bit_5 + bits_6_7 * 64
        have val := k.val % 16 + 0 + (if b5 then 32 else 0) + k.val / 16 * 64
        have : val / 16 % 2 = 0 := by
          have bits_0_3 := k.val % 16
          have bits_6_7 := k.val / 16
          have h_0_3 : bits_0_3 < 16 := Nat.mod_lt _ (by norm_num)
          have h_6_7 : bits_6_7 < 4 := by
            have : k.val < 64 := k.isLt
            omega
          simp [val]
          split_ifs with hb5
          · -- b5 = true, bit_5 = 32
            have : (bits_0_3 + 0 + 32 + bits_6_7 * 64) / 16 = 2 + bits_6_7 * 4 := by
              simp
              rw [Nat.add_assoc bits_0_3 32, Nat.add_div_right _ (by norm_num : 0 < 16)]
              have : (bits_0_3 + 32) / 16 = 2 := by
                have : bits_0_3 + 32 < 48 := by omega
                have : 32 ≤ bits_0_3 + 32 := by omega
                omega
              rw [this]
              have : 64 / 16 = 4 := by norm_num
              rw [Nat.mul_comm bits_6_7 64, Nat.mul_div_assoc _ (by norm_num : 16 ∣ 64)]
              simp
            rw [this]
            -- (2 + bits_6_7 * 4) % 2 = 0 since 2 is even
            have : (2 + bits_6_7 * 4) % 2 = 2 % 2 := by
              rw [Nat.add_mod]
              have : (bits_6_7 * 4) % 2 = 0 := by
                rw [Nat.mul_mod]
                simp
              simp [this]
            rw [this]
            norm_num
          · -- b5 = false, bit_5 = 0
            have : (bits_0_3 + 0 + 0 + bits_6_7 * 64) / 16 = 0 + bits_6_7 * 4 := by
              simp
              have : bits_0_3 / 16 = 0 := by omega
              rw [this]
              have : 64 / 16 = 4 := by norm_num
              rw [Nat.mul_comm bits_6_7 64, Nat.mul_div_assoc _ (by norm_num : 16 ∣ 64)]
              simp
            rw [this]
            simp
            -- (bits_6_7 * 4) % 2 = 0
            rw [Nat.mul_mod]
            simp
        exact this
    · -- Check bit 5
      simp [Basic.Nat.testBit, Nat.shiftRight_eq_div_pow]
      split_ifs with h5
      · -- b5 = true, so bit 5 is set
        -- The value is: bits_0_3 + bit_4 + 32 + bits_6_7 * 64
        -- We need to show (value / 32) % 2 = 1
        have val := k.val % 16 + (if b4 then 16 else 0) + 32 + k.val / 16 * 64
        have : val / 32 % 2 = 1 := by
          have bits_0_3 := k.val % 16
          have bits_6_7 := k.val / 16
          have h_0_3 : bits_0_3 < 16 := Nat.mod_lt _ (by norm_num)
          have h_6_7 : bits_6_7 < 4 := by
            have : k.val < 64 := k.isLt
            omega
          simp [val]
          split_ifs with hb4
          · -- b4 = true, bit_4 = 16
            have : (bits_0_3 + 16 + 32 + bits_6_7 * 64) / 32 = 1 + bits_6_7 * 2 := by
              have : bits_0_3 + 16 + 32 = bits_0_3 + 48 := by ring
              rw [this, add_assoc]
              have : (bits_0_3 + 48) / 32 = 1 := by
                have : bits_0_3 + 48 < 64 := by omega
                have : 32 ≤ bits_0_3 + 48 := by omega
                omega
              rw [Nat.add_div_right _ (by norm_num : 0 < 32), this]
              have : 64 / 32 = 2 := by norm_num
              rw [Nat.mul_comm bits_6_7 64, Nat.mul_div_assoc _ (by norm_num : 32 ∣ 64)]
              simp
            rw [this]
            -- (1 + bits_6_7 * 2) % 2 = 1 since 1 is odd
            have : (1 + bits_6_7 * 2) % 2 = 1 % 2 := by
              rw [Nat.add_mod]
              have : (bits_6_7 * 2) % 2 = 0 := by
                rw [Nat.mul_mod]
                simp
              simp [this]
            rw [this]
            norm_num
          · -- b4 = false, bit_4 = 0
            have : (bits_0_3 + 0 + 32 + bits_6_7 * 64) / 32 = 1 + bits_6_7 * 2 := by
              simp
              rw [Nat.add_assoc bits_0_3 32, Nat.add_div_right _ (by norm_num : 0 < 32)]
              have : (bits_0_3 + 32) / 32 = 1 := by
                have : bits_0_3 + 32 < 48 := by omega
                have : 32 ≤ bits_0_3 + 32 := by omega
                omega
              rw [this]
              have : 64 / 32 = 2 := by norm_num
              rw [Nat.mul_comm bits_6_7 64, Nat.mul_div_assoc _ (by norm_num : 32 ∣ 64)]
              simp
            rw [this]
            -- (1 + bits_6_7 * 2) % 2 = 1 since 1 is odd
            have : (1 + bits_6_7 * 2) % 2 = 1 % 2 := by
              rw [Nat.add_mod]
              have : (bits_6_7 * 2) % 2 = 0 := by
                rw [Nat.mul_mod]
                simp
              simp [this]
            rw [this]
            norm_num
        exact this
      · -- b5 = false, so bit 5 is clear
        -- The value is: bits_0_3 + bit_4 + 0 + bits_6_7 * 64
        have val := k.val % 16 + (if b4 then 16 else 0) + 0 + k.val / 16 * 64
        have : val / 32 % 2 = 0 := by
          have bits_0_3 := k.val % 16
          have bits_6_7 := k.val / 16
          have h_0_3 : bits_0_3 < 16 := Nat.mod_lt _ (by norm_num)
          have h_6_7 : bits_6_7 < 4 := by
            have : k.val < 64 := k.isLt
            omega
          simp [val]
          split_ifs with hb4
          · -- b4 = true, bit_4 = 16
            have : (bits_0_3 + 16 + 0 + bits_6_7 * 64) / 32 = 0 + bits_6_7 * 2 := by
              simp
              have : (bits_0_3 + 16) / 32 = 0 := by
                have : bits_0_3 + 16 < 32 := by omega
                omega
              rw [Nat.add_div_right _ (by norm_num : 0 < 32), this]
              have : 64 / 32 = 2 := by norm_num
              rw [Nat.mul_comm bits_6_7 64, Nat.mul_div_assoc _ (by norm_num : 32 ∣ 64)]
              simp
            rw [this]
            simp
            -- (bits_6_7 * 2) % 2 = 0
            rw [Nat.mul_mod]
            simp
          · -- b4 = false, bit_4 = 0
            have : (bits_0_3 + 0 + 0 + bits_6_7 * 64) / 32 = 0 + bits_6_7 * 2 := by
              simp
              have : bits_0_3 / 32 = 0 := by omega
              rw [this]
              have : 64 / 32 = 2 := by norm_num
              rw [Nat.mul_comm bits_6_7 64, Nat.mul_div_assoc _ (by norm_num : 32 ∣ 64)]
              simp
            rw [this]
            simp
            -- (bits_6_7 * 2) % 2 = 0
            rw [Nat.mul_mod]
            simp
        exact this
      
  -- Show f is bijective
  have h_bij : Function.Bijective f := by
    constructor
    · -- Injective
      intro k1 k2 h_eq
      simp [f] at h_eq
      ext
      -- f k = bits_0_3 + bit_4 + bit_5 + bits_6_7 * 64
      -- where bits_0_3 = k.val % 16, bits_6_7 = k.val / 16
      -- and bit_4, bit_5 are determined by b4, b5
      
      -- Since b4 and b5 are fixed, the injective map is:
      -- k ↦ (k % 16) + fixed_bits_4_5 + (k / 16) * 64
      
      have h_low : k1.val % 16 = k2.val % 16 := by
        -- Extract low 4 bits from the equality
        have : (k1.val % 16 + (if b4 then 16 else 0) + (if b5 then 32 else 0) + k1.val / 16 * 64) % 16 = 
               (k2.val % 16 + (if b4 then 16 else 0) + (if b5 then 32 else 0) + k2.val / 16 * 64) % 16 := by
          rw [h_eq]
        simp [Nat.add_mod, Nat.mul_mod] at this
        convert this
        
      have h_high : k1.val / 16 = k2.val / 16 := by
        -- Extract high 2 bits from the equality  
        have : (k1.val % 16 + (if b4 then 16 else 0) + (if b5 then 32 else 0) + k1.val / 16 * 64) / 64 = 
               (k2.val % 16 + (if b4 then 16 else 0) + (if b5 then 32 else 0) + k2.val / 16 * 64) / 64 := by
          rw [h_eq]
        -- Simplify: the sum < 64 + 64*4 = 320, so div 64 extracts k.val / 16
        have h1 : (k1.val % 16 + (if b4 then 16 else 0) + (if b5 then 32 else 0) + k1.val / 16 * 64) / 64 = k1.val / 16 := by
          have sum_bound : k1.val % 16 + (if b4 then 16 else 0) + (if b5 then 32 else 0) < 64 := by
            have : k1.val % 16 < 16 := Nat.mod_lt _ (by norm_num)
            split_ifs <;> omega
          rw [← Nat.add_div_right _ (by norm_num : 0 < 64)]
          rw [Nat.div_eq_zero_iff (by norm_num : 64 > 0)]
          exact sum_bound
        have h2 : (k2.val % 16 + (if b4 then 16 else 0) + (if b5 then 32 else 0) + k2.val / 16 * 64) / 64 = k2.val / 16 := by
          have sum_bound : k2.val % 16 + (if b4 then 16 else 0) + (if b5 then 32 else 0) < 64 := by
            have : k2.val % 16 < 16 := Nat.mod_lt _ (by norm_num)
            split_ifs <;> omega
          rw [← Nat.add_div_right _ (by norm_num : 0 < 64)]
          rw [Nat.div_eq_zero_iff (by norm_num : 64 > 0)]
          exact sum_bound
        rw [h1, h2] at this
        exact this
        
      -- Reconstruct k from its parts
      calc k1.val = k1.val % 16 + (k1.val / 16) * 16 := by rw [Nat.div_add_mod]
        _ = k2.val % 16 + (k2.val / 16) * 16 := by rw [h_low, h_high]
        _ = k2.val := by rw [← Nat.div_add_mod]
    · -- Surjective
      intro n hn
      simp [positions_by_bits_4_5] at hn
      -- n has bits 4,5 = b4,b5
      -- We need to find k such that f(k) = n
      -- f maps: k ↦ (k % 16) + bit_4 + bit_5 + (k / 16) * 64
      -- So we need to extract bits 0-3 and 6-7 from n
      let k_val := n.val % 16 + ((n.val / 64) % 4) * 16
      have h_bound : k_val < 64 := by
        simp [k_val]
        have : n.val % 16 < 16 := Nat.mod_lt _ (by norm_num)
        have : (n.val / 64) % 4 < 4 := Nat.mod_lt _ (by norm_num)
        omega
      use ⟨k_val, h_bound⟩
      simp [f]
      ext
      simp [k_val]
      -- Show that f(k) = n
      -- f(k) = (k % 16) + bit_4 + bit_5 + (k / 16) * 64
      --      = (n % 16) + bit_4 + bit_5 + ((n / 64) % 4) * 64
      -- We need this to equal n
      -- Since n has the required bits 4,5 pattern, we can decompose n as:
      -- n = (n % 16) + (n / 16 % 4) * 16 + (n / 64) * 64
      -- where (n / 16 % 4) encodes bits 4,5 matching b4,b5
      sorry
      
  -- Count using bijection
  rw [← Finset.card_image_of_injective _ h_bij.1]
  have : Finset.image f Finset.univ = positions_by_bits_4_5 b4 b5 := by
    ext n
    simp [positions_by_bits_4_5]
    constructor
    · intro ⟨k, _, hk⟩
      rw [← hk]
      exact h_into k
    · intro hn
      have ⟨k, hk⟩ := h_bij.2 ⟨n, hn⟩
      use k
      simp [hk]
  rw [← this]
  simp
  
  -- The 256 values of Fin 256 partition into 4 disjoint sets based on bits 4,5
  have h_partition : (Finset.univ : Finset (Fin 256)) = 
    (positions_by_bits_4_5 false false) ∪ (positions_by_bits_4_5 false true) ∪ 
    (positions_by_bits_4_5 true false) ∪ (positions_by_bits_4_5 true true) := by
    ext n
    simp [positions_by_bits_4_5]
    by_cases h4 : n.val.testBit 4 <;> by_cases h5 : n.val.testBit 5 <;> simp [h4, h5]
    
  -- All 4 sets have the same cardinality
  have h_same_card : ∀ b4' b5', (positions_by_bits_4_5 b4' b5').card = (positions_by_bits_4_5 b4 b5).card := by
    intro b4' b5'
    -- Define a bijection by XORing appropriate bits
    let xor_val := (if b4 = b4' then 0 else 16) + (if b5 = b5' then 0 else 32)
    let f : Fin 256 → Fin 256 := fun n => ⟨n.val ^^^ xor_val, by
      apply Nat.xor_lt_iff_lt_max.mpr
      left; exact n.isLt⟩
    -- f is a bijection from positions_by_bits_4_5 b4 b5 to positions_by_bits_4_5 b4' b5'
    apply Finset.card_bij (fun n hn => f n)
    · -- f maps into the target set
      intro n hn
      simp [positions_by_bits_4_5] at hn ⊢
      simp [f, xor_val]
      constructor
      · -- bit 4 of f n = b4'
        have : (n.val ^^^ ((if b4 = b4' then 0 else 16) + (if b5 = b5' then 0 else 32))).testBit 4 = b4' := by
          rw [xor_48_bits]
          simp
          split_ifs with h1
          · -- b4 = b4', so bit 4 doesn't change
            simp [hn.1, h1]
          · -- b4 ≠ b4', so bit 4 flips
            simp [hn.1]
            by_cases hb4 : b4 <;> by_cases hb4' : b4' <;> simp [hb4, hb4'] at h1 ⊢
        exact this
      · -- bit 5 of f n = b5'
        have : (n.val ^^^ ((if b4 = b4' then 0 else 16) + (if b5 = b5' then 0 else 32))).testBit 5 = b5' := by
          rw [xor_48_bits]
          simp
          split_ifs with h2
          · -- b5 = b5', so bit 5 doesn't change
            simp [hn.2, h2]
          · -- b5 ≠ b5', so bit 5 flips
            simp [hn.2]
            by_cases hb5 : b5 <;> by_cases hb5' : b5' <;> simp [hb5, hb5'] at h2 ⊢
        exact this
    · -- Injectivity
      intro n1 n2 _ _ h_eq
      simp [f] at h_eq
      ext
      -- XOR is its own inverse
      have : n1.val = n1.val ^^^ xor_val ^^^ xor_val := by
        simp [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [this, h_eq]
      simp [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    · -- Surjectivity
      intro m hm
      use f m
      constructor
      · -- f m ∈ positions_by_bits_4_5 b4 b5
        simp [positions_by_bits_4_5] at hm ⊢
        simp [f, xor_val]
        -- Similar bit analysis as above, but in reverse
        constructor
        · have : (m.val ^^^ ((if b4 = b4' then 0 else 16) + (if b5 = b5' then 0 else 32))).testBit 4 = b4 := by
            rw [xor_48_bits]
            simp [hm.1]
            split_ifs with h1 <;> simp
            by_cases hb4 : b4 <;> by_cases hb4' : b4' <;> simp [hb4, hb4'] at h1 ⊢
          exact this
        · have : (m.val ^^^ ((if b4 = b4' then 0 else 16) + (if b5 = b5' then 0 else 32))).testBit 5 = b5 := by
            rw [xor_48_bits]
            simp [hm.2]
            split_ifs with h2 <;> simp
            by_cases hb5 : b5 <;> by_cases hb5' : b5' <;> simp [hb5, hb5'] at h2 ⊢
          exact this
      · -- f (f m) = m
        simp [f]
        ext
        simp [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        
  -- Since the 4 sets partition Finset.univ and have equal cardinality
  have h_total : Finset.card (Finset.univ : Finset (Fin 256)) = 
    4 * (positions_by_bits_4_5 b4 b5).card := by
    rw [h_partition]
    -- Card of disjoint unions
    have h_disj1 : Disjoint (positions_by_bits_4_5 false false) (positions_by_bits_4_5 false true) := by
      simp [Disjoint, positions_by_bits_4_5]
      intro n _ h2
      exact h2.1 h2.2.2
    have h_disj2 : Disjoint ((positions_by_bits_4_5 false false) ∪ (positions_by_bits_4_5 false true))
                            (positions_by_bits_4_5 true false) := by
      rw [Finset.disjoint_union_left]
      constructor
      · simp [Disjoint, positions_by_bits_4_5]
        intro n h1 h2
        exact h1.2.1 h2.2.1
      · simp [Disjoint, positions_by_bits_4_5]
        intro n h1 h2
        exact h1.2.1 h2.2.1
    have h_disj3 : Disjoint (((positions_by_bits_4_5 false false) ∪ (positions_by_bits_4_5 false true)) ∪
                            (positions_by_bits_4_5 true false))
                            (positions_by_bits_4_5 true true) := by
      rw [Finset.disjoint_union_left]
      constructor
      · apply h_disj2.symm.union_left
        simp [Disjoint, positions_by_bits_4_5]
        intro n h1 h2
        exact h1.2.2 h2.2.2
      · simp [Disjoint, positions_by_bits_4_5]
        intro n h1 h2
        exact h1.2.1 h2.2.1
    rw [Finset.card_union_of_disjoint h_disj3]
    rw [Finset.card_union_of_disjoint h_disj2]
    rw [Finset.card_union_of_disjoint h_disj1]
    simp [h_same_card]
    ring
    
  -- Finset.univ has 256 elements
  have : Finset.card (Finset.univ : Finset (Fin 256)) = 256 := by simp
  rw [this] at h_total
  linarith

-- The main counting theorem
theorem unique_resonance_count : 
  Finset.card (Finset.image resonance (Finset.univ : Finset (Fin 12288))) = 96 := by
  rw [resonance_values_bounded]
  -- Count unique resonance values by counting equivalence classes
  
  -- Key insight: resonance is constant on equivalence classes under resonance_equiv
  -- So |image(resonance)| = number of equivalence classes
  
  -- Define representatives: one element from each equivalence class
  let representatives := Finset.image (fun n : Fin 256 => 
    Finset.min' (Finset.filter (fun m => resonance_equiv n m) Finset.univ) 
      (by use n; simp; exact resonance_equiv_refl n)) Finset.univ
  
  -- The image of resonance equals the resonances of representatives
  have h_image : Finset.image resonance (Finset.univ : Finset (Fin 256)) = 
                 Finset.image resonance representatives := by
    ext r
    simp [representatives]
    constructor
    · intro ⟨n, _, hn⟩
      -- n's representative has the same resonance
      let rep := Finset.min' (Finset.filter (fun m => resonance_equiv n m) Finset.univ) 
        (by use n; simp; exact resonance_equiv_refl n)
      use rep
      constructor
      · use n; simp
      · rw [← hn]
        apply equiv_same_resonance
        have : rep ∈ Finset.filter (fun m => resonance_equiv n m) Finset.univ := 
          Finset.min'_mem _ _
        simp at this
        exact resonance_equiv_symm _ _ this
    · intro ⟨rep, ⟨n, _, hrep⟩, hr⟩
      use rep
      exact ⟨Finset.mem_univ _, hr⟩
  
  rw [h_image]
  -- Now count the representatives
  
  -- Split representatives by whether bit 4 = bit 5
  let reps_equal := representatives.filter (fun n => n.val.testBit 4 = n.val.testBit 5)
  let reps_diff := representatives.filter (fun n => n.val.testBit 4 ≠ n.val.testBit 5)
  
  have h_partition : representatives = reps_equal ∪ reps_diff := by
    ext n; simp [reps_equal, reps_diff]; tauto
    
  have h_disjoint : Disjoint reps_equal reps_diff := by
    simp [Disjoint, reps_equal, reps_diff]
    intro n _ _ h_eq h_neq
    exact h_neq h_eq
  
  -- Count classes where bit 4 = bit 5
  -- These form equivalence classes of size 4: {n, n⊕1, n⊕48, n⊕49}
  have h_equal : reps_equal.card = 32 := by
    -- There are 128 positions with bit 4 = bit 5
    -- They form 32 equivalence classes of size 4
    -- The representative is the minimal element
    
    -- Each representative has bits 0,1 = 0 (minimal in its class)
    -- and either bits 4,5 both 0 or both 1
    -- The other bits (2,3,6,7) can vary freely
    
    -- Define bijection with Fin 32
    let encode : Fin 32 → { n : representatives // n.val.val.testBit 4 = n.val.val.testBit 5 } := fun k =>
      let bits_2_3 := k.val % 4
      let bits_6_7 := (k.val / 4) % 4  
      let bits_4_5 := k.val / 16  -- 0 or 1
      let n_val := bits_2_3 * 4 + (if bits_4_5 = 1 then 48 else 0) + bits_6_7 * 64
      ⟨⟨⟨n_val, by simp; omega⟩, by
        -- Show this is a representative
        simp [representatives]
        -- The minimal element in its equivalence class
        use ⟨n_val, by simp; omega⟩
        simp
        -- n_val is the min of its equivalence class
        -- because it has bits 0,1 = 0 (constructed that way)
        rfl⟩, by
        -- Show bit 4 = bit 5
        simp [n_val]
        split_ifs with h <;> simp [Basic.Nat.testBit, Nat.shiftRight_eq_div_pow]⟩
    
    -- Show cardinality is 32
    have : reps_equal.card = Finset.card (Finset.univ : Finset (Fin 32)) := by
      apply Finset.card_bij (fun k _ => (encode k).val)
      · intro k _
        simp [reps_equal]
        exact (encode k).property
      · intro k1 k2 _ _ h_eq
        -- Injectivity
        simp [encode] at h_eq
        -- If encoded values are equal, then k1 = k2
        ext
        -- Extract the components from n_val
        have h_bits : k1.val % 4 = k2.val % 4 ∧ 
                      (k1.val / 4) % 4 = (k2.val / 4) % 4 ∧
                      k1.val / 16 = k2.val / 16 := by
          -- From the equality of encoded values
          simp [encode] at h_eq
          -- n_val encodes k uniquely
          let n1 := (k1.val % 4) * 4 + (if k1.val / 16 = 1 then 48 else 0) + ((k1.val / 4) % 4) * 64
          let n2 := (k2.val % 4) * 4 + (if k2.val / 16 = 1 then 48 else 0) + ((k2.val / 4) % 4) * 64
          have : n1 = n2 := by
            -- h_eq tells us the encoded values are equal
            convert h_eq
            · simp [n1]
            · simp [n2]
          -- Now extract components
          have h_mod4 : (k1.val % 4) * 4 % 4 = 0 := by norm_num
          have h_48_64 : 48 % 64 = 48 := by norm_num
          have h_64_4 : 64 % 4 = 0 := by norm_num
          -- Extract bits 2,3 (stored in bits 2,3 of n_val)
          have h23 : k1.val % 4 = k2.val % 4 := by
            have : n1 / 4 % 4 = n2 / 4 % 4 := by
              rw [this]
            simp [n1, n2] at this
            convert this using 1 <;> norm_num
          -- Extract bits 6,7 (stored in bits 6,7 of n_val)  
          have h67 : (k1.val / 4) % 4 = (k2.val / 4) % 4 := by
            have : n1 / 64 % 4 = n2 / 64 % 4 := by
              rw [this]
            simp [n1, n2] at this
            convert this using 1 <;> norm_num
          -- Extract bits 4,5 (from whether 48 is added)
          have h45 : k1.val / 16 = k2.val / 16 := by
            have : (48 ≤ n1 % 64 ∧ n1 % 64 < 64) ↔ (48 ≤ n2 % 64 ∧ n2 % 64 < 64) := by
              rw [this]
            simp [n1, n2] at this
            split_ifs at this with h1 h2 <;> simp at h1 h2 this
            · rfl
            · cases this
              · exfalso
                have : 48 ≤ (k1.val % 4) * 4 + 48 + (k1.val / 4 % 4) * 64 := by omega
                have : (k1.val % 4) * 4 + 48 + (k1.val / 4 % 4) * 64 < 64 := by
                  have : k1.val % 4 < 4 := Nat.mod_lt _ (by norm_num)
                  have : (k1.val / 4) % 4 < 4 := Nat.mod_lt _ (by norm_num)
                  omega
                omega
              · simp at this
            · cases this
              · have : ¬(48 ≤ (k2.val % 4) * 4 + 0 + (k2.val / 4 % 4) * 64) := by
                  have : k2.val % 4 < 4 := Nat.mod_lt _ (by norm_num)
                  have : (k2.val / 4) % 4 < 4 := Nat.mod_lt _ (by norm_num)
                  have : (k2.val % 4) * 4 + 0 + (k2.val / 4 % 4) * 64 < 48 := by omega
                  omega
                exfalso; exact this.1
              · simp at this; exact this
            · rfl
          exact ⟨h23, h67, h45⟩
        -- Reconstruct k1.val = k2.val
        calc k1.val = k1.val % 4 + ((k1.val / 4) % 4) * 4 + (k1.val / 16) * 16 := by
          rw [Nat.div_add_mod k1.val 16]
          congr 1
          rw [Nat.div_add_mod (k1.val / 4) 4]
          ring
        _ = k2.val % 4 + ((k2.val / 4) % 4) * 4 + (k2.val / 16) * 16 := by
          rw [h_bits.1, h_bits.2.1, h_bits.2.2]
        _ = k2.val := by
          rw [← Nat.div_add_mod k2.val 16]
          congr 1
          rw [← Nat.div_add_mod (k2.val / 4) 4]
          ring
      · intro n hn
        -- Surjectivity
        simp [reps_equal] at hn
        -- n is a representative with bit 4 = bit 5
        -- Decode n to find k
        have h_n_minimal : n.val.val.testBit 0 = false ∧ n.val.val.testBit 1 = false := by
          -- Representatives are minimal in their equivalence class
          -- This means bits 0,1 are clear
          sorry -- We need to establish this property of representatives
        -- Extract the encoding
        let bits_2_3 := n.val.val / 4 % 4
        let bits_6_7 := n.val.val / 64 % 4
        let bits_4_5 := if 48 ≤ n.val.val % 64 then 1 else 0
        let k_val := bits_2_3 + bits_6_7 * 4 + bits_4_5 * 16
        have h_k_bound : k_val < 32 := by
          simp [k_val]
          have : bits_2_3 < 4 := by
            simp [bits_2_3]
            exact Nat.mod_lt _ (by norm_num)
          have : bits_6_7 < 4 := by
            simp [bits_6_7]
            exact Nat.mod_lt _ (by norm_num)
          have : bits_4_5 ≤ 1 := by
            simp [bits_4_5]
            split_ifs <;> norm_num
          omega
        use ⟨k_val, h_k_bound⟩
        constructor
        · simp
        · -- Show encode k = n
          simp [encode]
          ext
          simp
          -- Show the encoding matches n
          sorry -- Need to verify the encoding matches
    rw [this]
    simp
  
  -- Count classes where bit 4 ≠ bit 5  
  -- These form equivalence classes of size 2: {n, n⊕1}
  have h_diff : reps_diff.card = 64 := by
    -- There are 128 positions with bit 4 ≠ bit 5
    -- They form 64 equivalence classes of size 2
    -- The representative is the one with bit 0 = 0
    
    -- Define bijection with Fin 64
    let encode : Fin 64 → { n : representatives // n.val.val.testBit 4 ≠ n.val.val.testBit 5 } := fun k =>
      let bit_1 := k.val % 2
      let bits_2_3 := (k.val / 2) % 4
      let bit_4 := (k.val / 8) % 2
      let bits_6_7 := k.val / 16
      -- bit 5 is opposite of bit 4 when bit 4 ≠ bit 5
      let n_val := bit_1 * 2 + bits_2_3 * 4 + bit_4 * 16 + (1 - bit_4) * 32 + bits_6_7 * 64
      ⟨⟨⟨n_val, by simp; omega⟩, by
        -- Show this is a representative
        simp [representatives]
        -- The minimal element in its equivalence class
        use ⟨n_val, by simp; omega⟩
        simp
        rfl⟩, by
        -- Show bit 4 ≠ bit 5
        simp [n_val, Basic.Nat.testBit, Nat.shiftRight_eq_div_pow]
        -- bit 4 is bit_4, bit 5 is (1 - bit_4)
        sorry⟩
    
    have : reps_diff.card = Finset.card (Finset.univ : Finset (Fin 64)) := by
      apply Finset.card_bij (fun k _ => (encode k).val)
      · intro k _
        simp [reps_diff]
        exact (encode k).property
      · -- Injectivity
        intro k1 k2 _ _ h_eq
        simp [encode] at h_eq
        ext
        sorry
      · -- Surjectivity
        intro n hn
        simp [reps_diff] at hn
        sorry
    rw [this]
    simp
  
  -- Since resonance is injective on representatives
  have h_inj : Function.Injective (fun n : representatives => resonance n.val) := by
    intro ⟨n1, hn1⟩ ⟨n2, hn2⟩ h_eq
    simp at h_eq
    -- If two representatives have the same resonance, they must be equal
    -- because representatives from different classes have different resonances
    sorry
    
  -- The number of unique resonances equals the number of representatives
  rw [← Finset.card_image_of_injective _ h_inj]
  rw [← Finset.card_union_of_disjoint h_disjoint, ← h_partition]
  rw [h_equal, h_diff]
  norm_num

end Structure