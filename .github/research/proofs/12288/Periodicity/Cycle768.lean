import PrimeOS12288.Axioms.Page
import PrimeOS12288.Computational.Foundation
import PrimeOS12288.Conservation.BitFlip
import PrimeOS12288.Structure.FieldActivation

/-!
# 768-Element Periodicity of Resonance Values

This module proves that resonance values repeat with period 768, which is the
least common multiple of the page size (48) and field period (256).

## Main Results

- `resonance_periodic_768`: resonance(n) = resonance(n + 768)
- `cycle_size_lcm`: 768 = lcm(48, 256)
- `conservation_over_cycle`: Conservation laws hold over each 768-cycle
- `cycle_decomposition_12_64`: 768 = 12 × 64
- `cycle_decomposition_16_48`: 768 = 16 × 48

The 768-cycle emerges from the interaction of two fundamental periods:
- Byte pattern repeats every 256 positions (field period)
- Page structure repeats every 48 positions (page size)
-/

namespace PrimeOS12288.Periodicity

open PrimeOS12288
open PrimeOS12288.Computational

variable [Foundation]

/-! ## Basic cycle properties -/

/-- The cycle size is 768 -/
lemma cycle_768 : cycle_size = 768 := by
  rw [cycle_size_eq]

/-- 768 equals lcm(48, 256) -/
theorem cycle_size_lcm : cycle_size = Nat.lcm page_size field_period := by
  rw [page_size_eq, field_period_eq, cycle_size_eq]
  norm_num

/-- 768 decomposes as 12 × 64 -/
theorem cycle_decomposition_12_64 : cycle_size = 12 * 64 := by
  rw [cycle_size_eq]
  norm_num

/-- 768 decomposes as 16 × 48 -/
theorem cycle_decomposition_16_48 : cycle_size = 16 * page_size := by
  rw [page_size_eq, cycle_size_eq]
  norm_num

/-- 768 decomposes as 3 × 256 -/
theorem cycle_decomposition_3_256 : cycle_size = 3 * field_period := by
  rw [field_period_eq, cycle_size_eq]
  norm_num

/-! ## Periodicity of byte values -/

/-- Byte values repeat with period 256 -/
theorem byte_periodic (n : ℕ) : 
    positionToByte ⟨n % TotalSize, Nat.mod_lt n (by norm_num : 0 < TotalSize)⟩ = 
    positionToByte ⟨(n + field_period) % TotalSize, Nat.mod_lt (n + field_period) (by norm_num : 0 < TotalSize)⟩ := by
  have h := Foundation.position_byte_periodic
  simp only [h]
  congr 1
  -- Show that n % 256 = (n + 256) % 256
  rw [field_period_eq]
  simp [Nat.add_mod]

/-- Byte values repeat with period 768 -/
theorem byte_periodic_768 (n : ℕ) (h : n < TotalSize) : 
    positionToByte ⟨n, h⟩ = 
    positionToByte ⟨(n + cycle_size) % TotalSize, Nat.mod_lt (n + cycle_size) (by norm_num : 0 < TotalSize)⟩ := by
  have h_period := Foundation.position_byte_periodic
  simp only [h_period]
  congr 1
  -- 768 is a multiple of 256, so adding 768 doesn't change n % 256
  rw [cycle_decomposition_3_256, field_period_eq]
  simp [Nat.add_mod, Nat.mul_mod]

/-! ## Periodicity of active fields -/

/-- Active fields repeat with period 768 -/
theorem activeFields_periodic_768 (n : ℕ) (h : n < TotalSize) :
    activeFields ⟨n, h⟩ = 
    activeFields ⟨(n + cycle_size) % TotalSize, Nat.mod_lt (n + cycle_size) (by norm_num : 0 < TotalSize)⟩ := by
  unfold activeFields
  congr 1
  exact byte_periodic_768 n h

/-! ## Main periodicity theorem -/

/-- Resonance values repeat with period 768 -/
theorem resonance_periodic_768 (n : Position) :
    resonance n = resonance ⟨(n.val + cycle_size) % TotalSize, by
      apply Nat.mod_lt
      norm_num⟩ := by
  unfold resonance
  congr 1
  -- Active fields are the same due to periodicity
  have h : n.val < TotalSize := n.isLt
  exact activeFields_periodic_768 n.val h

/-- Alternative formulation: resonance is 768-periodic as a function on ℕ -/
theorem resonance_periodic_768_nat (n : ℕ) (h1 : n < TotalSize) (h2 : n + cycle_size < TotalSize) :
    resonance ⟨n, h1⟩ = resonance ⟨n + cycle_size, h2⟩ := by
  have : (n + cycle_size) % TotalSize = n + cycle_size := by
    apply Nat.mod_eq_of_lt h2
  rw [← this]
  exact resonance_periodic_768 ⟨n, h1⟩

/-! ## Conservation over cycles -/

/-- Sum of resonances over one complete cycle -/
noncomputable def cycle_sum (start : ℕ) : ℝ :=
  Finset.sum (Finset.range cycle_size) fun i =>
    if h : start + i < TotalSize then
      resonance ⟨start + i, h⟩
    else
      0

/-- General periodicity: positions with same remainder mod cycle_size have equal resonance -/
theorem resonance_mod_cycle (n m : ℕ) (hn : n < TotalSize) (hm : m < TotalSize) :
    n % cycle_size = m % cycle_size → resonance ⟨n, hn⟩ = resonance ⟨m, hm⟩ := by
  intro h_mod
  -- Express n and m in terms of cycle_size
  have n_decomp : n = (n / cycle_size) * cycle_size + (n % cycle_size) := Nat.div_add_mod n cycle_size
  have m_decomp : m = (m / cycle_size) * cycle_size + (m % cycle_size) := Nat.div_add_mod m cycle_size
  
  -- Since n % cycle_size = m % cycle_size, let's call this common value r
  let r := n % cycle_size
  have hr : r = m % cycle_size := h_mod
  have hr_lt : r < cycle_size := Nat.mod_lt n (by norm_num : 0 < cycle_size)
  
  -- Rewrite n and m
  rw [n_decomp, ← hr] at hn ⊢
  rw [m_decomp, ← hr] at hm ⊢
  
  -- Now apply periodicity repeatedly
  -- First, show that resonance at position r + k*cycle_size equals resonance at r
  have h_periodic : ∀ k : ℕ, k * cycle_size + r < TotalSize → 
    resonance ⟨k * cycle_size + r, by assumption⟩ = resonance ⟨r, by
      calc r < cycle_size := hr_lt
      _ = 768 := cycle_size_eq
      _ < 12288 := by norm_num
      _ = TotalSize := by rfl⟩ := by
    intro k hk
    induction k with
    | zero => simp
    | succ k' ih =>
      have hk' : k' * cycle_size + r < TotalSize := by
        calc k' * cycle_size + r < k' * cycle_size + cycle_size := by omega
        _ = (k' + 1) * cycle_size := by ring
        _ ≤ (k' + 1) * cycle_size + r := by omega
        _ < TotalSize := hk
      
      have h_step : (k' + 1) * cycle_size + r = (k' * cycle_size + r) + cycle_size := by ring
      rw [h_step]
      rw [← resonance_periodic_768_nat (k' * cycle_size + r) hk' hk]
      exact ih hk'
  
  -- Apply this to both n and m
  have hn_form : n = n / cycle_size * cycle_size + r := by
    rw [n_decomp]
    congr
  have hm_form : m = m / cycle_size * cycle_size + r := by  
    rw [m_decomp, hr]
  
  rw [← hn_form] at hn
  rw [← hm_form] at hm
  
  exact (h_periodic (n / cycle_size) hn).trans (h_periodic (m / cycle_size) hm).symm

/-- The sum of resonances is the same for each complete 768-cycle -/
theorem cycle_sum_invariant (start : ℕ) (h : start + cycle_size ≤ TotalSize) :
    cycle_sum start = cycle_sum 0 := by
  unfold cycle_sum
  
  -- Key insight: We'll show that the multiset of resonance values in any cycle
  -- is the same as the multiset in the first cycle, just in a different order.
  -- Since addition is commutative, the sums are equal.
  
  -- First, simplify the if-then-else conditions
  have h_if_start : ∀ i ∈ Finset.range cycle_size, start + i < TotalSize := by
    intro i hi
    simp only [Finset.mem_range] at hi
    calc start + i < start + cycle_size := by omega
    _ ≤ TotalSize := h
  
  have h_if_zero : ∀ i ∈ Finset.range cycle_size, i < TotalSize := by
    intro i hi
    simp only [Finset.mem_range] at hi
    calc i < cycle_size := hi
    _ = 768 := cycle_size_eq
    _ < 12288 := by norm_num
    _ = TotalSize := by rfl
  
  -- Rewrite both sums without the if-then-else
  simp_rw [dif_pos (h_if_start _), dif_pos (h_if_zero _)]
  
  -- Define a bijection from positions in cycle starting at start
  -- to positions in cycle starting at 0
  let f : Fin cycle_size → Fin cycle_size := fun i => 
    ⟨(start + i) % cycle_size, Nat.mod_lt _ (by norm_num : 0 < cycle_size)⟩
  
  -- Show that f is a bijection
  have h_bij : Function.Bijective f := by
    constructor
    · -- Injective
      intro i j h_eq
      simp [f] at h_eq
      -- From (start + i) % cycle_size = (start + j) % cycle_size
      -- and i, j < cycle_size, we need to show i = j
      have : (start + i.val) % cycle_size = (start + j.val) % cycle_size := by
        exact Fin.val_injective h_eq
      rw [Nat.add_mod, Nat.add_mod] at this
      have hi_mod : i.val % cycle_size = i.val := Nat.mod_eq_of_lt i.isLt
      have hj_mod : j.val % cycle_size = j.val := Nat.mod_eq_of_lt j.isLt
      rw [hi_mod, hj_mod] at this
      -- So (start % cycle_size + i.val) % cycle_size = (start % cycle_size + j.val) % cycle_size
      have h_bound_i : start % cycle_size + i.val < 2 * cycle_size := by
        have : start % cycle_size < cycle_size := Nat.mod_lt _ (by norm_num : 0 < cycle_size)
        omega
      have h_bound_j : start % cycle_size + j.val < 2 * cycle_size := by
        have : start % cycle_size < cycle_size := Nat.mod_lt _ (by norm_num : 0 < cycle_size)
        omega
      -- Consider cases
      by_cases hi_small : start % cycle_size + i.val < cycle_size
      · by_cases hj_small : start % cycle_size + j.val < cycle_size
        · -- Both are small
          rw [Nat.mod_eq_of_lt hi_small, Nat.mod_eq_of_lt hj_small] at this
          have : i.val = j.val := by omega
          exact Fin.ext this
        · -- i small, j large
          have : cycle_size ≤ start % cycle_size + j.val := by omega
          rw [Nat.mod_eq_of_lt hi_small, Nat.mod_eq_sub_mod h_bound_j] at this
          simp [Nat.mod_eq_of_lt (by norm_num : cycle_size < 2 * cycle_size)] at this
          -- start % cycle_size + i.val = start % cycle_size + j.val - cycle_size
          have : i.val + cycle_size = j.val := by omega
          -- But this is impossible since j.val < cycle_size
          omega
      · -- i large
        have : cycle_size ≤ start % cycle_size + i.val := by omega
        by_cases hj_small : start % cycle_size + j.val < cycle_size
        · -- i large, j small
          rw [Nat.mod_eq_sub_mod h_bound_i, Nat.mod_eq_of_lt hj_small] at this
          simp [Nat.mod_eq_of_lt (by norm_num : cycle_size < 2 * cycle_size)] at this
          -- start % cycle_size + i.val - cycle_size = start % cycle_size + j.val
          have : j.val + cycle_size = i.val := by omega
          -- But this is impossible since i.val < cycle_size
          omega
        · -- Both are large
          have : cycle_size ≤ start % cycle_size + j.val := by omega
          rw [Nat.mod_eq_sub_mod h_bound_i, Nat.mod_eq_sub_mod h_bound_j] at this
          simp [Nat.mod_eq_of_lt (by norm_num : cycle_size < 2 * cycle_size)] at this * 
          have : i.val = j.val := by omega
          exact Fin.ext this
    · -- Surjective
      intro j
      -- We need to find i such that (start + i) % cycle_size = j
      -- Let i = (j - start % cycle_size) % cycle_size
      let i_val := if j.val ≥ start % cycle_size then 
                     j.val - start % cycle_size 
                   else 
                     j.val + cycle_size - start % cycle_size
      have hi_lt : i_val < cycle_size := by
        simp [i_val]
        split_ifs with h_ge
        · -- j.val ≥ start % cycle_size
          have : start % cycle_size < cycle_size := Nat.mod_lt _ (by norm_num : 0 < cycle_size)
          omega
        · -- j.val < start % cycle_size
          have : start % cycle_size < cycle_size := Nat.mod_lt _ (by norm_num : 0 < cycle_size)
          omega
      use ⟨i_val, hi_lt⟩
      simp [f]
      ext
      simp [i_val]
      split_ifs with h_ge
      · -- j.val ≥ start % cycle_size
        rw [Nat.add_mod]
        have : start % cycle_size + (j.val - start % cycle_size) = j.val := by omega
        rw [this]
        exact Nat.mod_eq_of_lt j.isLt
      · -- j.val < start % cycle_size
        rw [Nat.add_mod]
        have h_eq : start % cycle_size + (j.val + cycle_size - start % cycle_size) = j.val + cycle_size := by
          omega
        rw [h_eq, Nat.add_mod]
        simp [Nat.mod_eq_of_lt j.isLt]
  
  -- Now we use the bijection to reindex the sum
  -- The sum over start..start+cycle_size equals the sum over the image of f
  have h_reindex : Finset.sum (Finset.range cycle_size) (fun i => resonance ⟨start + i, h_if_start i (Finset.mem_range.mpr (Fin.is_lt ⟨i, by simp [Finset.mem_range]⟩))⟩) = 
                   Finset.sum (Finset.univ : Finset (Fin cycle_size)) (fun j => resonance ⟨j.val, h_if_zero j.val (by simp [Finset.mem_range]; exact j.isLt)⟩) := by
    -- Use that f is a bijection and resonance is periodic
    rw [← Finset.sum_bij (fun i _ => f i) _ _ _ _]
    · -- Show equality of terms
      intro a ha
      simp only [Finset.mem_range] at ha
      simp [f]
      -- We need to show: resonance ⟨start + a, _⟩ = resonance ⟨(start + a) % cycle_size, _⟩
      apply resonance_mod_cycle
      rfl
    · -- f maps from range to univ
      intro a ha
      simp [f]
      exact Finset.mem_univ _
    · -- f is injective on range
      intro a₁ a₂ ha₁ ha₂ h_eq
      simp only [Finset.mem_range] at ha₁ ha₂
      have : f ⟨a₁, ha₁⟩ = f ⟨a₂, ha₂⟩ := by
        simp [f] at h_eq ⊢
        exact h_eq
      have : ⟨a₁, ha₁⟩ = ⟨a₂, ha₂⟩ := Function.Injective.eq_iff h_bij.1 this
      exact Fin.val_injective this
    · -- f is surjective from range to univ
      intro b hb
      obtain ⟨a, ha_eq⟩ := h_bij.2 b
      use a.val
      constructor
      · simp [Finset.mem_range]; exact a.isLt
      · simp [f] at ha_eq
        simp [f]
        exact Fin.val_injective ha_eq
  
  -- Convert the sum over Fin cycle_size back to sum over range
  have h_univ_range : Finset.sum (Finset.univ : Finset (Fin cycle_size)) (fun j => resonance ⟨j.val, h_if_zero j.val (by simp [Finset.mem_range]; exact j.isLt)⟩) =
                      Finset.sum (Finset.range cycle_size) (fun i => resonance ⟨i, h_if_zero i (by simp [Finset.mem_range])⟩) := by
    rw [← Finset.sum_bij (fun j _ => j.val) _ _ _ _]
    · simp
    · intro j _; simp [Finset.mem_range]; exact j.isLt
    · intro j₁ j₂ _ _ h_eq; exact Fin.ext h_eq
    · intro i hi
      simp only [Finset.mem_range] at hi
      use ⟨i, hi⟩
      simp
  
  rw [h_reindex, h_univ_range]

/-- XOR conservation holds over each cycle -/
theorem xor_conservation_cycle (a b : Position) 
    (ha : a.val < cycle_size) (hb : b.val < cycle_size) :
    resonance a * resonance b = resonance (xorPositions a b) * resonance ⟨0, by norm_num⟩ := by
  -- Apply the general XOR conservation law from Conservation.BitFlip
  -- The hypotheses ha and hb ensure we're working within a single cycle,
  -- but they're not needed for the conservation law itself
  -- Since 0 : Position is coerced to ⟨0, by norm_num⟩, this follows directly
  exact xor_conservation a b

/-! ## Cycle structure -/

/-- Position within a cycle -/
def positionInCycle (n : Position) : CyclePosition :=
  ⟨n.val % cycle_size, Nat.mod_lt n.val (by norm_num : 0 < cycle_size)⟩

/-- Cycle number for a position -/
def cycleNumber (n : Position) : ℕ :=
  n.val / cycle_size

/-- Decomposition of position into cycle and offset -/
theorem position_cycle_decompose (n : Position) :
    n.val = cycleNumber n * cycle_size + (positionInCycle n).val := by
  unfold cycleNumber positionInCycle
  exact Nat.div_add_mod n.val cycle_size

/-- Resonance depends only on position within cycle -/
theorem resonance_depends_only_on_cycle_position (n : Position) :
    resonance n = resonance ⟨(positionInCycle n).val, by
      have h := (positionInCycle n).isLt
      simp [CyclePosition] at h
      rw [cycle_size_eq] at h
      norm_num
      exact h⟩ := by
  -- Use the decomposition and periodicity
  have decomp := position_cycle_decompose n
  -- Apply periodicity cycleNumber n times
  
  -- Let's denote the position within cycle for clarity
  let pos_in_cycle := (positionInCycle n).val
  let cycle_num := cycleNumber n
  
  -- We have n.val = cycle_num * cycle_size + pos_in_cycle from decomp
  rw [← decomp]
  
  -- We'll show by induction on cycle_num that
  -- resonance ⟨cycle_num * cycle_size + pos_in_cycle, _⟩ = resonance ⟨pos_in_cycle, _⟩
  
  -- First, we need to establish that pos_in_cycle < TotalSize
  have h_pos_lt : pos_in_cycle < TotalSize := by
    calc pos_in_cycle < cycle_size := (positionInCycle n).isLt
    _ = 768 := cycle_size_eq
    _ < 12288 := by norm_num
    _ = TotalSize := by rfl
  
  -- Now proceed by induction on cycle_num
  suffices h : ∀ k : ℕ, k * cycle_size + pos_in_cycle < TotalSize → 
    resonance ⟨k * cycle_size + pos_in_cycle, by assumption⟩ = resonance ⟨pos_in_cycle, h_pos_lt⟩ by
    exact h cycle_num n.isLt
  
  intro k hk
  induction k with
  | zero => 
    -- Base case: 0 * cycle_size + pos_in_cycle = pos_in_cycle
    simp
  | succ k' ih =>
    -- Inductive step: show resonance at (k'+1) * cycle_size + pos_in_cycle
    -- equals resonance at pos_in_cycle
    
    -- First establish that k' * cycle_size + pos_in_cycle < TotalSize
    have hk' : k' * cycle_size + pos_in_cycle < TotalSize := by
      calc k' * cycle_size + pos_in_cycle < k' * cycle_size + cycle_size := by
        exact Nat.add_lt_add_left (positionInCycle n).isLt _
      _ = (k' + 1) * cycle_size := by ring
      _ ≤ (k' + 1) * cycle_size + pos_in_cycle := by omega
      _ < TotalSize := hk
    
    -- Rewrite (k'+1) * cycle_size + pos_in_cycle as (k' * cycle_size + pos_in_cycle) + cycle_size
    have h_succ : (k' + 1) * cycle_size + pos_in_cycle = (k' * cycle_size + pos_in_cycle) + cycle_size := by
      ring
    
    rw [h_succ]
    
    -- Apply resonance_periodic_768_nat
    rw [← resonance_periodic_768_nat (k' * cycle_size + pos_in_cycle) hk' hk]
    
    -- Apply inductive hypothesis
    exact ih hk'

/-! ## Implications for the full system -/

/-- The number of complete cycles in the full system -/
def num_complete_cycles : ℕ := TotalSize / cycle_size

/-- The full system contains exactly 16 complete cycles -/
theorem num_cycles_eq_16 : num_complete_cycles = 16 := by
  unfold num_complete_cycles
  rw [cycle_size_eq]
  norm_num

/-- Total resonance sum equals 16 times the cycle sum -/
theorem total_resonance_sum :
    (Finset.sum Finset.univ fun n : Position => resonance n) = 
    16 * cycle_sum 0 := by
  -- The system decomposes into 16 complete cycles
  -- Each cycle contributes the same sum due to cycle_sum_invariant
  
  -- First, establish that TotalSize = 16 * cycle_size
  have h_total : TotalSize = 16 * cycle_size := by
    rw [cycle_size_eq]
    norm_num
  
  -- We'll partition the 12288 positions into 16 cycles, each starting at k * cycle_size
  -- and use the fact that each cycle has the same sum
  
  -- Express the total sum as a sum of cycle sums
  have h_partition : (Finset.sum Finset.univ fun n : Position => resonance n) =
                     Finset.sum (Finset.range 16) fun k => cycle_sum (k * cycle_size) := by
    -- We'll show the positions can be partitioned into 16 disjoint cycles
    -- Position n belongs to cycle k where k = n.val / cycle_size
    
    -- First, convert Position sum to sum over naturals
    have h_conv : (Finset.sum Finset.univ fun n : Position => resonance n) =
                  Finset.sum (Finset.range TotalSize) fun n => 
                    resonance ⟨n, by simp [Finset.mem_range]⟩ := by
      rw [← Finset.sum_bij (fun p _ => p.val) _ _ _ _]
      · intro a ha
        simp [Finset.mem_range]
        exact a.isLt
      · intros; simp
      · intro a b ha hb h_eq
        exact Fin.ext h_eq
      · intro b hb
        simp [Finset.mem_range] at hb
        use ⟨b, hb⟩
        simp [Finset.mem_univ]
    
    rw [h_conv]
    
    -- Now partition the range TotalSize into 16 chunks of size cycle_size
    have h_chunks : Finset.range TotalSize = 
                    Finset.biUnion (Finset.range 16) fun k => 
                      Finset.image (fun i => k * cycle_size + i) (Finset.range cycle_size) := by
      ext n
      simp [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
      constructor
      · intro hn
        -- n < TotalSize, so we can write n = k * cycle_size + i
        -- where k = n / cycle_size and i = n % cycle_size
        use n / cycle_size
        constructor
        · rw [h_total] at hn
          exact Nat.div_lt_iff_lt_mul (by norm_num : 0 < cycle_size) |>.mpr hn
        · use n % cycle_size
          constructor
          · exact Nat.mod_lt n (by norm_num : 0 < cycle_size)
          · exact (Nat.div_add_mod n cycle_size).symm
      · intro ⟨k, hk, i, hi, h_eq⟩
        rw [← h_eq, h_total]
        calc k * cycle_size + i 
          < k * cycle_size + cycle_size := by omega
          _ = (k + 1) * cycle_size := by ring
          _ ≤ 16 * cycle_size := by
            apply Nat.mul_le_mul_right
            omega
    
    -- The biUnion is disjoint
    have h_disj : (Finset.range 16).PairwiseDisjoint fun k => 
                    Finset.image (fun i => k * cycle_size + i) (Finset.range cycle_size) := by
      intro k hk l hl hne
      simp [Finset.disjoint_iff_ne, Finset.mem_image, Finset.mem_range]
      intro i hi j hj
      intro h_eq
      -- If k * cycle_size + i = l * cycle_size + j and k ≠ l, derive contradiction
      have h_lt_i : i < cycle_size := hi
      have h_lt_j : j < cycle_size := hj
      -- From k * cycle_size + i = l * cycle_size + j
      -- we get (k - l) * cycle_size = j - i (if k > l) or (l - k) * cycle_size = i - j
      by_cases h : k < l
      · have : l * cycle_size + j = k * cycle_size + i := h_eq.symm
        have : (l - k) * cycle_size + j = i := by omega
        have : (l - k) * cycle_size ≤ i := by omega
        have : cycle_size ≤ i := by
          have : 1 ≤ l - k := by omega
          calc cycle_size = 1 * cycle_size := by ring
          _ ≤ (l - k) * cycle_size := by
            apply Nat.mul_le_mul_right
            exact this
          _ ≤ i := by assumption
        omega
      · push_neg at h
        have : l < k := by omega
        have : k * cycle_size + i = l * cycle_size + j := h_eq
        have : (k - l) * cycle_size + i = j := by omega
        have : (k - l) * cycle_size ≤ j := by omega
        have : cycle_size ≤ j := by
          have : 1 ≤ k - l := by omega
          calc cycle_size = 1 * cycle_size := by ring
          _ ≤ (k - l) * cycle_size := by
            apply Nat.mul_le_mul_right
            exact this
          _ ≤ j := by assumption
        omega
    
    -- Now use sum_biUnion_disjoint
    rw [h_chunks, Finset.sum_biUnion h_disj]
    congr 1
    ext k
    -- Show that sum over k-th chunk equals cycle_sum (k * cycle_size)
    unfold cycle_sum
    rw [← Finset.sum_bij (fun i _ => i) _ _ _ _]
    · intro i hi
      simp [Finset.mem_image, Finset.mem_range] at hi ⊢
      exact hi
    · intro i hi
      simp [Finset.mem_range] at hi
      have h_sum : k * cycle_size + i < TotalSize := by
        rw [h_total]
        calc k * cycle_size + i 
          < k * cycle_size + cycle_size := by omega
          _ = (k + 1) * cycle_size := by ring
          _ ≤ 16 * cycle_size := by
            apply Nat.mul_le_mul_right
            simp [Finset.mem_range] at hk
            omega
      simp [dif_pos h_sum]
    · intro a b ha hb h_eq
      simp [Finset.mem_range] at ha hb
      exact h_eq
    · intro b hb
      simp [Finset.mem_image, Finset.mem_range] at hb
      obtain ⟨i, hi, rfl⟩ := hb
      use i
      simp [Finset.mem_range, hi]
  
  rw [h_partition]
  
  -- Now use cycle_sum_invariant to show all cycle sums equal cycle_sum 0
  simp_rw [cycle_sum_invariant _ _]
  · simp [Finset.sum_const, Finset.card_range]
  
  -- Prove the hypothesis for cycle_sum_invariant
  intro k hk
  simp [Finset.mem_range] at hk
  rw [h_total]
  calc k * cycle_size + cycle_size
    = (k + 1) * cycle_size := by ring
    _ ≤ 16 * cycle_size := by
      apply Nat.mul_le_mul_right
      omega

end PrimeOS12288.Periodicity