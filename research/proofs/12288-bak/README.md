# PrimeOS Lean Proofs

This directory contains the complete Lean 4 formalization of the 12,288-element mathematical structure.

## Overview

The proofs establish from first principles:
- The existence and uniqueness of the structure
- All 96 unique resonance values
- Perfect conservation laws
- Symmetry group properties
- Quantum mechanical interpretations

## Directory Structure

```
proofs/
├── Basic/          # Fundamental types and operations
├── Fields/         # Field constants and properties
├── Resonance/      # Resonance calculations and spectrum
├── Structure/      # Pages, cycles, and symmetry
├── Conservation/   # Conservation laws and invariants
├── Computation/    # Algorithms and complexity
└── Main/           # Existence and uniqueness theorems
```

## Getting Started

1. Install Lean 4: https://leanprover.github.io/lean4/doc/setup.html
2. Clone this repository
3. Run `lake build` in the proofs directory

## Module Dependencies

See `lean-proof-plan.md` for the complete dependency graph and module specifications.

## Key Results

- **Theorem**: The structure has exactly 96 unique resonance values
- **Theorem**: Total resonance sum equals 687.1101183515111
- **Theorem**: Perfect circulation conservation at all prescribed scales
- **Theorem**: The structure is unique up to isomorphism

## Usage

Import specific modules as needed:

```lean
import PrimeOS.Basic.Types
import PrimeOS.Resonance.Core
import PrimeOS.Conservation.Circulation
```

Or import all main results:

```lean
import PrimeOS.Main.Properties
```

## Contributing

Please ensure all proofs:
1. Build without errors
2. Include appropriate documentation
3. Have unit tests where applicable
4. Follow the established naming conventions

## License

This mathematical formalization is part of the PrimeOS project.