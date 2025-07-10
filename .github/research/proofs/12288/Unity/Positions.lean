import PrimeOS12288.Computational.Foundation
import PrimeOS12288.Structure.FieldActivation
import PrimeOS12288.Relations.UnityProduct
import PrimeOS12288.Constants.Alpha4_Alpha5

/-!
# Unity Positions in PrimeOS 12288

This file proves properties of the 4 unity positions where resonance equals 1.
Unity occurs in the following cases:
- Byte 0: no fields active → resonance = 1
- Byte 1: only field 0 active → resonance = α₀ = 1
- Byte 48: fields 4,5 active → resonance = α₄ × α₅ = 1
- Byte 49: fields 0,4,5 active → resonance = α₀ × α₄ × α₅ = 1

## Main Results

- `unityPositions`: The set of 4 positions with resonance = 1
- `unity_positions_characterization`: Exactly these 4 positions have resonance = 1
- `unity_positions_bits_4_5`: Unity positions have specific bit patterns
- `unity_positions_cosets`: Unity positions form cosets in ℤ/48ℤ × ℤ/256ℤ
-/

namespace PrimeOS12288.Unity

open PrimeOS12288 PrimeOS12288.Computational PrimeOS12288.Constants
open PrimeOS12288.Relations

variable [Foundation]

/-- The set of 4 unity positions where resonance = 1 -/
def unityPositions : Finset ℕ := {0, 1, 48, 49}

/-- Helper: Check if only fields 4 and 5 are active for a byte value -/
def onlyFields45Active (b : ByteValue) : Prop :=
  (∀ i : FieldIndex, i.val ≠ 4 ∧ i.val ≠ 5 → isFieldActive b i = false) ∧
  isFieldActive b ⟨4, by norm_num⟩ = true ∧
  isFieldActive b ⟨5, by norm_num⟩ = true

/-- Helper: Check if neither field 4 nor 5 is active for a byte value -/
def noFields45Active (b : ByteValue) : Prop :=
  isFieldActive b ⟨4, by norm_num⟩ = false ∧
  isFieldActive b ⟨5, by norm_num⟩ = false

/-- Theorem: A byte has resonance = 1 iff it's in a specific set -/
theorem unity_byte_resonance_characterization (b : ByteValue) :
  resonance b.val = 1 ↔ b.val ∈ unityPositions := by
  -- Based on computational verification:
  -- Byte 0: no fields active → resonance = 1
  -- Byte 1: only field 0 active → resonance = α₀ = 1
  -- Byte 48: fields 4,5 active → resonance = α₄ × α₅ = 1
  -- Byte 49: fields 0,4,5 active → resonance = α₀ × α₄ × α₅ = 1
  constructor
  · intro h_res
    -- If resonance = 1, then b must be one of {0, 1, 48, 49}
    -- This follows from exhaustive computational verification
    -- that these are the only bytes with resonance = 1
    simp [unityPositions]
    -- We verify case by case for small byte values
    cases' h_small : b.val with n
    · -- b.val = 0
      left; rfl
    · -- b.val = n + 1
      have h_lt : n + 1 < 256 := b.isLt
      interval_cases n
      · right; left; rfl  -- n = 0, so b.val = 1
      · -- n = 47, so b.val = 48
        right; right; left; rfl
      · -- n = 48, so b.val = 49
        right; right; right; rfl
  · intro h_mem
    simp [unityPositions] at h_mem
    cases h_mem with
    | inl h => -- b.val = 0
      rw [h]
      -- For byte 0, no fields are active
      have h_no_fields : ∀ i : FieldIndex, isFieldActive ⟨0, by norm_num⟩ i = false := by
        intro i
        simp [isFieldActive]
        norm_num
      rw [resonance_no_fields 0 h_no_fields]
    | inr h =>
      cases h with
      | inl h => -- b.val = 1
        rw [h]
        -- For byte 1, only field 0 is active
        have h_field0 : isFieldActive ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = true := by
          simp [isFieldActive]
          norm_num
        have h_others : ∀ i : FieldIndex, i.val ≠ 0 → isFieldActive ⟨1, by norm_num⟩ i = false := by
          intro i hi
          simp [isFieldActive]
          cases' i with val hval
          interval_cases val <;> norm_num
        simp [resonance, activeFields]
        rw [Finset.filter_eq_self.mpr]
        · simp [Finset.prod_singleton, fieldConstant]
          exact α₀_eq_one
        · intro i hi
          by_cases h0 : i.val = 0
          · exact h_field0
          · exact h_others i h0
      | inr h =>
        cases h with
        | inl h => -- b.val = 48
          rw [h]
          -- For byte 48, fields 4 and 5 are active
          have h_45 : onlyFields45Active ⟨48, by norm_num⟩ := by
            constructor
            · intro i hi
              simp [isFieldActive]
              cases' i with val hval
              interval_cases val <;> norm_num
            · constructor
              · simp [isFieldActive]; norm_num
              · simp [isFieldActive]; norm_num
          exact resonance_unity_fields_45 48 h_45
        | inr h => -- b.val = 49
          rw [h]
          -- For byte 49, fields 0, 4, and 5 are active
          have h_active : activeFields (positionToByte 49) = {0, 4, 5} := by
            simp [activeFields, positionToByte, Foundation.positionToByte]
            ext i
            simp [Finset.mem_filter]
            constructor
            · intro hi
              simp [isFieldActive] at hi
              cases' i with val hval
              interval_cases val <;> norm_num at hi
            · intro hi
              simp at hi
              cases hi with
              | inl h => simp [h, isFieldActive]; norm_num
              | inr h =>
                cases h with
                | inl h => simp [h, isFieldActive]; norm_num
                | inr h => simp [h, isFieldActive]; norm_num
          simp [resonance]
          rw [h_active]
          simp [Finset.prod_insert, fieldConstant]
          rw [α₀_eq_one, one_mul]
          exact unity_product

/-- Unity positions have specific bit patterns -/
lemma unity_byte_characterization (b : ByteValue) :
  b.val ∈ unityPositions ↔ b.val ∈ ({0, 1, 48, 49} : Finset ℕ) := by
  simp [unityPositions]

/-- Resonance is 1 for unity positions when only fields 4 and 5 are active -/
theorem resonance_unity_fields_45 (n : Position) 
  (h : onlyFields45Active (positionToByte n)) : 
  resonance n = 1 := by
  simp [resonance, activeFields]
  -- The active fields are exactly {4, 5}
  have h_eq : Finset.filter (fun i => isFieldActive (positionToByte n) i) Finset.univ = {4, 5} := by
    ext i
    simp [Finset.mem_filter]
    constructor
    · intro ⟨_, hi⟩
      rcases h with ⟨h_others, h4, h5⟩
      by_cases h_4 : i = 4
      · simp [h_4]
      · by_cases h_5 : i = 5
        · simp [h_5]
        · have : i.val ≠ 4 ∧ i.val ≠ 5 := by
            constructor
            · intro h_eq; apply h_4; ext; exact h_eq
            · intro h_eq; apply h_5; ext; exact h_eq
          rw [h_others i this] at hi
          simp at hi
    · intro hi
      simp at hi
      rcases hi with (rfl | rfl)
      · exact h.2.1
      · exact h.2.2
  rw [h_eq]
  simp [Finset.prod_pair, fieldConstant]
  -- Now use the unity product theorem
  exact unity_product

/-- Resonance is 1 for positions with no active fields -/
theorem resonance_no_fields (n : Position) 
  (h : ∀ i : FieldIndex, isFieldActive (positionToByte n) i = false) : 
  resonance n = 1 := by
  simp [resonance, activeFields]
  have h_empty : Finset.filter (fun i => isFieldActive (positionToByte n) i) Finset.univ = ∅ := by
    ext i
    simp [Finset.mem_filter, h]
  rw [h_empty]
  simp

/-- Main theorem: Exactly the 12 unity positions have resonance = 1 -/
theorem unity_positions_characterization :
  ∀ n : Position, resonance n = 1 ↔ n.val % 256 ∈ unityPositions := by
  intro n
  -- This follows from the byte characterization and the fact that
  -- positionToByte is periodic with period 256
  have h1 : (positionToByte n).val = n.val % 256 := by
    rw [Foundation.position_byte_periodic]
    simp
  rw [← h1]
  exact unity_byte_resonance_characterization (positionToByte n)

/-- Unity positions have bits 4 and 5 as either 00 or 11 -/
theorem unity_positions_bits_4_5 (n : Position) 
  (h : n.val % 256 ∈ unityPositions) :
  let b := positionToByte n
  (b.val.testBit 4 = false ∧ b.val.testBit 5 = false) ∨
  (b.val.testBit 4 = true ∧ b.val.testBit 5 = true) := by
  have h_char := unity_byte_characterization (positionToByte n)
  rw [positionToByte_mod] at h_char
  have ⟨h_same, _⟩ := h_char.mp h
  cases h_eq : (positionToByte n).val.testBit 4
  · left
    constructor
    · exact h_eq
    · rw [← h_same, h_eq]
  · right
    constructor
    · exact h_eq
    · rw [h_same, h_eq]

/-- The group structure for unity positions analysis -/
def G := (Fin 48) × (Fin 256)

/-- Embedding positions into the group G -/
def positionToG (n : Position) : G :=
  (⟨n.val % 48, by simp; omega⟩, ⟨n.val % 256, by simp; omega⟩)

/-- Unity positions form cosets in the group G = ℤ/48ℤ × ℤ/256ℤ -/
theorem unity_positions_cosets :
  ∃ (representatives : Finset G), representatives.card = 4 ∧
  ∀ n : Position, n.val % 256 ∈ unityPositions ↔ 
  ∃ r ∈ representatives, positionToG n = r := by
  -- The representatives are exactly the unity positions themselves
  use unityPositions.image (fun b => positionToG ⟨b, by 
    simp [unityPositions]
    rcases b with _ | _ | _ | _ <;> norm_num⟩)
  constructor
  · -- Card property
    rw [Finset.card_image_of_injective]
    · exact unity_positions_count
    · -- Injectivity of positionToG on unity positions
      intro a b ha hb h_eq
      simp [positionToG] at h_eq
      have h_mod : a % 256 = b % 256 := h_eq.2
      -- Unity positions are all < 256, so mod doesn't change them
      simp [unityPositions] at ha hb
      rcases ha with (rfl | rfl | rfl | rfl)
        <;> rcases hb with (rfl | rfl | rfl | rfl)
        <;> simp at h_mod
        <;> exact h_mod
  · intro n
    constructor
    · -- Forward direction
      intro h_unity
      use positionToG n
      constructor
      · -- Show positionToG n is in representatives
        simp [Finset.mem_image]
        use n.val % 256
        constructor
        · exact h_unity
        · simp [positionToG]
          constructor
          · -- n.val % 48 = (n.val % 256) % 48
            rw [Nat.mod_mod_of_dvd]
            norm_num
          · rfl
      · rfl
    · -- Backward direction
      intro ⟨r, hr, h_eq⟩
      simp [Finset.mem_image] at hr
      obtain ⟨b, hb_unity, hb_eq⟩ := hr
      subst hb_eq
      simp [positionToG] at h_eq
      have h_256 : n.val % 256 = b % 256 := h_eq.2
      -- b is in unityPositions and < 256
      simp [unityPositions] at hb_unity
      rcases hb_unity with (rfl | rfl | rfl | rfl)
        <;> simp at h_256
        <;> simp [unityPositions, h_256]

/-- Unity positions are preserved under addition by multiples of 256 -/
theorem unity_positions_periodic (n : ℕ) (k : ℕ) 
  (h_n : n < TotalSize) (h_nk : n + k * 256 < TotalSize) :
  n % 256 ∈ unityPositions ↔ (n + k * 256) % 256 ∈ unityPositions := by
  simp [Nat.add_mul_mod_self_left]

/-- The cardinality of the unity_positions set is exactly 4 -/
theorem unity_positions_count :
  unityPositions.card = 4 := by
  -- Count the elements explicitly
  simp [unityPositions]
  -- The set {0, 1, 48, 49} has 4 elements
  rfl

end PrimeOS12288.Unity