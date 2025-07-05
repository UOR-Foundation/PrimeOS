import Axioms.Unity
import Axioms.Binary  
import Axioms.Golden
import Axioms.Growth
import Axioms.Circular
import Axioms.System
import Axioms.Page

/-!
# Test Layer 0: Axioms
This file tests that all axioms can be imported and used together.
-/

open PrimeOS12288.Axioms

-- Test that we can reference all axioms
#check unity_exists
#check binary_exists
#check golden_exists
#check golden_bounds
#check golden_unique
#check tribonacci_exists
#check tribonacci_bounds
#check tribonacci_unique
#check pi_exists
#check system_constants_exist
#check page_size
#check page_size_eq
#check field_period
#check field_period_eq
#check cycle_size
#check cycle_size_eq