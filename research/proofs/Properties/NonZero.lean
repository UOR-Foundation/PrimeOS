/-
  Properties.NonZero - All field constants are non-zero
  
  This module proves that all 8 field constants are non-zero,
  which follows immediately from their positivity.
-/

import Properties.Positivity

namespace Properties

open Constants

theorem all_nonzero : ∀ i : Fin 8, α i ≠ 0 := by
  intro i
  exact ne_of_gt (all_positive i)

end Properties