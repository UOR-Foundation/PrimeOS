/-
  Constants.All - Aggregate all field constants
  
  This module imports all individual constant definitions and
  defines the field constant function α : Fin 8 → ℝ.
-/

-- Import all constants
import Constants.Alpha0
import Constants.Alpha1
import Constants.Alpha2
import Constants.Alpha3
import Constants.Alpha4_Alpha5
import Constants.Alpha6_Alpha7

namespace Constants

-- Define the field constant function
noncomputable def α : Fin 8 → ℝ
| 0 => α₀
| 1 => α₁
| 2 => α₂
| 3 => α₃
| 4 => α₄
| 5 => α₅
| 6 => α₆
| 7 => α₇

end Constants