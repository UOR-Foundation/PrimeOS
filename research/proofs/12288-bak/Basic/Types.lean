/-
  Basic.Types - Fundamental type definitions
  
  This module provides basic type definitions and utilities needed
  for the structural properties.
-/

namespace Basic

-- Helper to test if a bit is set
def Nat.testBit (n : Nat) (i : Nat) : Bool :=
  (n >>> i) % 2 = 1

end Basic