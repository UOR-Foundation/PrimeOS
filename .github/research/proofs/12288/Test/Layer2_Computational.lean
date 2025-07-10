import Computational.Foundation
import Computational.FoundationImpl

/-!
# Test Layer 2: Computational Foundation
This file tests the computational foundation layer.
It depends on Basic.Types, Constants, and Page axioms.
-/

open PrimeOS12288.Computational

-- Test that we have the Foundation instance
#check Foundation.positionToByte
#check Foundation.isFieldActive
#check activeFields
#check resonance

-- Test basic computations
example : Position := ⟨0, by norm_num⟩
example : Position := ⟨12287, by norm_num⟩

-- Test that implementation is available
variable [Foundation]
#check position_decompose