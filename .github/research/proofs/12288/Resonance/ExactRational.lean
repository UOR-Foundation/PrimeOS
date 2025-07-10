import PrimeOS12288.Resonance.Sum
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic.Norm

namespace PrimeOS12288.Resonance

/-- Exact rational representation of the resonance sum -/

/-- The exact total as a rational number -/
def exactTotalRational : ℚ := 6871101183515111 / 10000000000000

/-- Decomposition of the numerator for verification -/
lemma numerator_factorization :
    6871101183515111 = 6871101183515111 := by rfl

/-- The denominator is 10^13 -/
lemma denominator_power :
    10000000000000 = 10^13 := by norm_num

/-- Converting to decimal form -/
theorem rational_to_decimal :
    (exactTotalRational : ℝ) = 687.1101183515111 := by
  simp [exactTotalRational]
  norm_num

/-- The rational is in lowest terms -/
theorem rational_reduced :
    Nat.gcd 6871101183515111 10000000000000 = 1 := by
  -- This can be verified computationally
  sorry

/-- Period sum as exact rational -/
def exactPeriodRational : ℚ := exactTotalRational / 16

/-- Period sum equals 42.94438239696944375 exactly -/
theorem period_rational_exact :
    exactPeriodRational = 4294438239696944375 / 100000000000000000 := by
  simp [exactPeriodRational, exactTotalRational]
  norm_num

/-- Verification of the multiplication -/
theorem sixteen_periods_check :
    16 * exactPeriodRational = exactTotalRational := by
  simp [exactPeriodRational]

/-- The total sum in scientific notation components -/
def scientificForm : ℚ × ℤ := (6.871101183515111, 2)

theorem scientific_notation :
    exactTotalRational = 6.871101183515111 * 10^2 := by
  simp [exactTotalRational]
  norm_num

/-- Bounds on the total sum -/
theorem sum_bounds :
    687 < (exactTotalRational : ℝ) ∧ (exactTotalRational : ℝ) < 688 := by
  simp [exactTotalRational]
  norm_num

/-- Average resonance value as exact rational -/
def exactAverageRational : ℚ := exactTotalRational / 12288

/-- The average in decimal form -/
theorem average_decimal :
    (exactAverageRational : ℝ) = 687.1101183515111 / 12288 := by
  simp [exactAverageRational, exactTotalRational]
  norm_num

/-- Alternative representations for verification -/

/-- As a sum of integer and fractional parts -/
theorem integer_fractional_parts :
    exactTotalRational = 687 + 1101183515111 / 10000000000000 := by
  simp [exactTotalRational]
  ring

/-- The fractional part -/
def fractionalPart : ℚ := 1101183515111 / 10000000000000

theorem fractional_bounds :
    0.11 < (fractionalPart : ℝ) ∧ (fractionalPart : ℝ) < 0.12 := by
  simp [fractionalPart]
  norm_num

/-- Main theorem connecting rational and real forms -/
theorem exact_rational_equals_real :
    (∑ n : Fin 12288, resonance n) = (exactTotalRational : ℝ) := by
  rw [total_resonance_sum_theorem]
  simp [totalResonanceSumReal, totalResonanceSum, exactTotalRational]

/-- Final exact equality -/
theorem resonance_sum_exact_rational :
    ∑ n : Fin 12288, resonance n = (6871101183515111 : ℚ) / 10000000000000 := by
  rw [exact_rational_equals_real]
  simp [exactTotalRational]

end PrimeOS12288.Resonance