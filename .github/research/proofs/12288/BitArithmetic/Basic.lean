/-!
# Bit Arithmetic Infrastructure for PrimeOS 12288 Proofs

This layer provides bit manipulation properties needed for the proof system.
It extends the Computational Foundation with specific bit arithmetic theorems.
-/

import PrimeOS12288.Basic.Types
import PrimeOS12288.Computational.Foundation

namespace PrimeOS12288.BitArithmetic

open PrimeOS12288 PrimeOS12288.Computational

/-- Interface for bit arithmetic properties -/
class Basic extends Foundation where
  /-- Bit testing equivalence with division and modulo -/
  testBit_eq_one_iff : ∀ (n i : ℕ), n.testBit i ↔ (n / 2^i) % 2 = 1
  
  /-- Bit is false if number is less than power of 2 -/
  testBit_eq_false_of_lt : ∀ {n i : ℕ}, n < 2^i → ¬n.testBit i
  
  /-- Key decomposition for 8-bit values using bits 4 and 5 -/
  nat_decompose_bits_4_5 : ∀ (n : ℕ) (h : n < 256),
    n = (n % 16) + ((n / 16) % 4) * 16 + (n / 64) * 64
    
  /-- XOR bit testing property -/
  xor_testBit : ∀ (a b i : ℕ), (a ^^^ b).testBit i = (a.testBit i != b.testBit i)
  
  /-- Bit 4 and 5 extraction -/
  bits_4_5_eq_div_16_mod_4 : ∀ (n : ℕ) (h : n < 256),
    (n.testBit 4, n.testBit 5) = ((n / 16) % 2 = 1, (n / 32) % 2 = 1)

variable [Basic]

end PrimeOS12288.BitArithmetic