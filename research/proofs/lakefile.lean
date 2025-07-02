import Lake
open Lake DSL

package «PrimeOS» where
  -- add package configuration options here

lean_lib «PrimeOS» where
  -- add library configuration options here
  srcDir := "."
  roots := #[`Axioms, `Constants, `Properties, `Relations, `Basic, `Fields, `Test, `Structure]

@[default_target]
lean_exe «primeos» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"