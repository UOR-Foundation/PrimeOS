import Constants.Alpha0
import Constants.Alpha1
import Constants.Alpha2
import Constants.Alpha3
import Constants.Pi
import Constants.Alpha4_Alpha5
import Constants.Alpha6_Alpha7
import Constants.Distinctness
import Constants.All

/-!
# Test Layer 1: Constants
This file tests that all constants can be imported and used together.
It depends on Layer 0 (Axioms).
-/

open PrimeOS12288.Constants

-- Test that we can reference all constants
#check α₀
#check α₁
#check α₂
#check α₃
#check π
#check α₄
#check α₅
#check α₆
#check α₇
#check fieldConstant

-- Test key properties
#check α₀_eq_one
#check α₁_gt_one
#check α₁_bounds
#check α₂_gt_one
#check α₂_bounds
#check α₂_lt_two
#check α₃_eq_half
#check α₄_mul_α₅
#check α₄_bounds
#check α₅_bounds
#check α₆_lt_one
#check α₇_lt_one
#check all_positive
#check fieldConstant_injective

-- Test distinctness theorems
#check α₀_ne_α₁
#check α₁_ne_α₂
#check α₄_ne_α₅
#check α₆_ne_α₇