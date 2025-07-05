/-
  Main entry point for PrimeOS12288 proof library
  This file imports all modules to enable `lake build` to build everything
-/

-- Level 0: Axioms
import Axioms.Unity
import Axioms.Binary
import Axioms.Golden
import Axioms.Growth
import Axioms.Circular
import Axioms.System
import Axioms.Page

-- Level 1: Constants
import Constants.Alpha0
import Constants.Alpha1
import Constants.Alpha2
import Constants.Alpha3
import Constants.Pi
import Constants.Alpha4_Alpha5
import Constants.Alpha6_Alpha7
import Constants.All

-- Foundation
import Basic.Types

-- Level 2: Computational Foundation
import Computational.Foundation
import Computational.FoundationImpl

-- Level 3: Bit Arithmetic
import BitArithmetic.Basic
import BitArithmetic.BasicImpl

-- Level 4: Properties
import Properties.Positivity
import Properties.NonZero
import Properties.Equations

-- Level 5: Relations
import Relations.UnityProduct
import Relations.PiEncoding
import Relations.Ordering
import Relations.Distinctness
import Relations.ResonanceEquivalence

-- Level 6: Structure
import Structure.FieldActivation
import Structure.ResonanceCount

-- Level 7: Resonance
import Resonance.Distribution
import Resonance.Sum

-- Level 8: Conservation
import Conservation.BitFlip

-- Level 9: Uniqueness
import Uniqueness.SystemDetermination

-- Extended Theorems
import Unity.Positions
import Periodicity.Cycle768
import Automorphisms.Group2048
import Factorization.Perfect