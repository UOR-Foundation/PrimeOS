# CCM Coherence

Implementation of Axiom A1 of Coherence-Centric Mathematics: the coherence inner product and metric structure through Clifford algebra.

## Overview

This crate provides:
- **Clifford Algebra Generation**: Create Clifford algebras Cl(n) for n-dimensional vector spaces
- **Coherence Inner Product**: The fundamental metric ⟨⟨·,·⟩⟩ satisfying grade orthogonality
- **Grade Decomposition**: Project elements onto specific grades
- **Geometric Operations**: Geometric, wedge, and inner products
- **Optimization**: Coherence minimization algorithms
- **Rotor Group**: Even subalgebra and rotation operators
- **Sparse & Lazy Evaluation**: Memory-efficient representations

## Mathematical Foundation

The coherence inner product satisfies:
1. **Positive-definiteness**: ⟨⟨σ,σ⟩⟩ ≥ 0 with equality iff σ = 0
2. **Conjugate symmetry**: ⟨⟨σ,τ⟩⟩ = ⟨⟨τ,σ⟩⟩*
3. **Linearity**: ⟨⟨aσ + bτ, ρ⟩⟩ = a⟨⟨σ,ρ⟩⟩ + b⟨⟨τ,ρ⟩⟩
4. **Grade orthogonality**: ⟨⟨σᵢ,τⱼ⟩⟩ = 0 for i ≠ j

## Quick Start

```rust
use ccm_coherence::{CliffordAlgebra, CliffordElement, coherence_norm};

// Create 3D Clifford algebra
let algebra = CliffordAlgebra::<f64>::generate(3)?;

// Create basis vectors
let e1 = CliffordElement::<f64>::basis_vector(0, 3)?;
let e2 = CliffordElement::<f64>::basis_vector(1, 3)?;

// Compute geometric product
let e12 = algebra.geometric_product(&e1, &e2)?;

// Check coherence norm
let norm = coherence_norm(&e12);
assert!((norm - 1.0).abs() < 1e-10);
```

## Features

### Core Operations

- **Clifford Elements**: Complex-valued elements with 2^n components
- **Products**: Geometric, wedge (∧), inner (·), and scalar products
- **Grade Operations**: Extract or project onto specific grades
- **Involutions**: Grade reversal, grade involution, Clifford conjugation

### Advanced Features

- **Sparse Representation**: Efficient storage for elements with few non-zero components
- **Lazy Evaluation**: Generate basis elements on demand for large algebras
- **Coherence Minimization**: Find minimal norm elements subject to constraints
- **Rotor Group**: Spin(n) group for rotations

### Memory Efficiency

For an n-dimensional space:
- Dense representation: 2^n complex numbers per element
- Sparse representation: Only non-zero components stored
- Lazy evaluation: Basis elements generated on demand

## Examples

### Basic Clifford Algebra
```rust
// Create basis blade e₁ ∧ e₂
let e12 = CliffordElement::basis_blade(&[0, 1], 3)?;

// Grade projection
let grade2_part = element.grade_projection(2);
```

### Rotations with Rotors
```rust
use ccm_coherence::rotor::Rotor;

// Create rotor from bivector (rotation angle θ in e₁e₂ plane)
let mut bivector = CliffordElement::zero(3);
bivector.set_component(3, Complex::new(theta/2.0, 0.0))?;
let rotor = Rotor::from_bivector(&bivector, &algebra)?;

// Apply rotation to vector
let rotated = rotor.apply_to_vector(&vector, &algebra)?;
```

### Coherence Minimization
```rust
use ccm_coherence::optimization::{minimize_with_grades, MinimizationOptions};

// Minimize norm keeping only even grades
let result = minimize_with_grades(
    &element,
    vec![0, 2, 4],  // even grades
    MinimizationOptions::default(),
)?;
```

## Integration with CCM

This crate implements the metric structure (Axiom A1) that combines with:
- `ccm-embedding`: Field structure and resonance (Axiom A2)
- `ccm-symmetry`: Group actions preserving coherence (Axiom A3)
- `ccm-core`: Unified interface bringing all three together

## Performance Considerations

- Use sparse representation when elements have < 10% non-zero components
- Use lazy evaluation for dimensions n > 8 to avoid memory explosion
- Grade operations are O(2^n) but can be parallelized
- Geometric product is O(4^n) for dense elements, O(k²) for k non-zero components

## References

- Geometric Algebra for Physicists (Doran & Lasenby)
- Clifford Algebras and Spinors (Lounesto)
- CLAUDE.md: CCM mathematical specification