import Lake
open Lake DSL

package «PrimeOS12288» where
  -- add package configuration options here

lean_lib «PrimeOS12288» where
  -- add library configuration options here
  srcDir := "."
  roots := #[`Axioms, `Constants, `Properties, `Relations, `Basic, `Structure,
            `Computational, `BitArithmetic, `Conservation, `Resonance, `Uniqueness,
            `Unity, `Periodicity, `Automorphisms, `Factorization]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"