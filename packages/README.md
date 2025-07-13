# CCM Packages Overview

This directory contains the modular implementation of Coherence-Centric Mathematics (CCM), organized according to the three fundamental axioms and their applications.

## Architecture

CCM is built on three mathematical axioms, each generating a complete algebraic structure:

1. **Coherence Inner Product** (Axiom A1) → Metric structure
2. **Minimal Embedding** (Axiom A2) → Field structure  
3. **Symmetry Group Action** (Axiom A3) → Transformation structure

## Package Structure

### Core Infrastructure

#### ccm-core
The foundational types and unified API that all other packages build upon.
- Shared data types (BitWord, mathematical utilities, errors)
- Unified CCM trait interface
- Integration point for the three mathematical structures

### Mathematical Generators

#### ccm-embedding
Implements Axiom A2: Minimal embedding of mathematical objects.
- **Alpha Generator**: Field constants with unity constraint
- **Resonance Algebra**: R(b) = ∏ α_i^{b_i} and derived properties
- **Embedding Operations**: Minimal norm representations

#### ccm-coherence  
Implements Axiom A1: Coherence inner product and metric structure.
- **Clifford Algebra Generator**: 2^n dimensional geometric algebra
- **Grade Decomposition**: Grade-wise operations and projections
- **Coherence Metric**: Inner product ⟨⟨·,·⟩⟩ and induced norm

#### ccm-symmetry
Implements Axiom A3: Group actions preserving CCM structure.
- **Symmetry Group Generator**: Lie group structure
- **Orbit Analysis**: Orbit-stabilizer decomposition
- **Invariant Theory**: Preserved quantities under group action

## Mathematical Unity

The key insight of CCM is that these three structures are not independent:
- Unity constraint in embedding ↔ Grade orthogonality in coherence
- Klein groups in resonance ↔ Subgroups in symmetry  
- Conservation laws ↔ Invariant measures

The ccm-core package provides the unified interface where these three mathematical structures work together to enable:
- Efficient data encoding (BJC codec)
- Integer factorization
- Quantum neural networks
- Other applications of coherence minimization

## Development Status

- ✅ **ccm-core**: Foundational types and unified API complete
- ✅ **ccm-embedding**: Alpha generator and resonance algebra complete
- ✅ **ccm-coherence**: Clifford algebra, coherence metric, and optimization complete
- ✅ **ccm-symmetry**: Group actions, Lie algebra, and invariant theory complete

## Usage

Applications should depend on `ccm-core` and use the unified `CCMCore` trait to access all mathematical operations. The individual mathematical packages (embedding, coherence, symmetry) are implementation details that applications typically won't need to reference directly.

```rust
use ccm_core::{CCMCore, StandardCCM};

let ccm = StandardCCM::new();
// Use unified interface for all operations
```

## References

See individual package spec.md files for detailed mathematical specifications and implementation requirements.