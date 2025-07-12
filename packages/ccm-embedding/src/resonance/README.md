# Resonance Algebra Module

This module implements the complete resonance algebra for Coherence-Centric Mathematics (CCM), supporting arbitrary bit lengths from 8 bits to theoretical infinity.

## Overview

The resonance function R: {0,1}^n → ℝ⁺ is defined as:

```
R(b) = ∏_{i=0}^{n-1} α_i^{b_i}
```

Where:
- `b` is an n-bit pattern
- `b_i` is the i-th bit of b
- `α = (α₀, α₁, ..., α_{n-1})` are positive real field constants
- Unity constraint: `α_{n-2} × α_{n-1} = 1`

## Scaling Properties

### Bit Length Support

| Scale | Range | Implementation Strategy | Memory Usage |
|-------|-------|------------------------|--------------|
| Small | n ≤ 8 | Direct u8 operations | 1 byte |
| Medium | 8 < n ≤ 64 | BitWord with single u64 | 8 bytes |
| Large | 64 < n ≤ 1024 | BitWord with multiple u64s | n/8 bytes |
| Huge | n > 1024 | BitWord with Vec<u64> | n/8 bytes + overhead |

### Algorithm Complexity

| Operation | Small n (≤20) | Large n (>20) | Notes |
|-----------|---------------|---------------|--------|
| Resonance computation | O(n) | O(n) | Linear in bit count |
| Klein group operations | O(1) | O(1) | Always 4 members |
| Resonance classes | O(2^n) | O(sampling) | Sampling for large n |
| Unity positions | O(2^n) | O(sampling) | Strategic sampling |
| Inverse resonance | O(2^{n-2}) | O(heuristic) | Various strategies |
| Conservation sums | O(3×2^n) | O(sampling) | Mathematical properties |
| Homomorphic subgroups | O(n²) | O(n²) | Pair checking |

## Core Components

### 1. Basic Resonance (`mod.rs`)

The fundamental resonance computation with:
- **Direct computation**: For small popcounts (≤32 set bits)
- **Log-domain computation**: For large popcounts or extreme values
- **Overflow protection**: Automatic switching to log domain

```rust
// Example: Computing resonance for large bit pattern
let word = BitWord::from_hex("FFFFFFFFFFFFFFFF"); // 64 bits set
let r = word.r(&alpha); // Automatically uses log domain
```

### 2. Resonance Classes (`classes.rs`)

Equivalence classes under Klein group action:
- **Klein groups**: 4-element groups formed by XORing last 2 bits
- **Class count**: Exactly `3 × 2^{n-2}` unique resonances (with unity constraint)
- **Sampling**: For n > 20, uses strategic sampling instead of exhaustive enumeration

```rust
// Get resonance spectrum efficiently
let spectrum = BitWord::resonance_spectrum(&alpha);
// Returns up to 10000 samples for large n
```

### 3. Conservation Laws (`conservation.rs`)

Mathematical conservation properties:
- **Cycle length**: `3 × 2^n` for complete conservation
- **Sum conservation**: Total resonance over full cycle is constant
- **Current conservation**: `∑ J(i) = 0` where `J(i) = R(i+1) - R(i)`

For large n:
- Uses sampling with appropriate scaling factors
- Leverages mathematical properties instead of exhaustive computation

### 4. Homomorphic Properties (`homomorphic.rs`)

XOR-resonance homomorphism `R(a ⊕ b) = R(a) × R(b)` holds only for special subgroups:
- **Trivial**: {0}
- **Single bit**: {0, 2^i} where α_i² = 1
- **Unity pair**: Subgroups using bits where `α_i × α_j = 1`
- **Klein V₄**: Maximal subgroup using unity constraint bits

### 5. Unity Structure (`unity.rs`)

Positions where R(b) = 1:
- **Unity positions**: Actual bit patterns with resonance 1.0
- **Klein groups with unity**: Groups containing unity elements
- **Distribution**: Varies with alpha values

For large n:
- Samples strategic positions
- Uses Klein structure to identify patterns

### 6. Gradient Operations (`gradient.rs`)

Optimization in resonance space:
- **Bit gradient**: `∂R/∂bit_i = R(b) × ln(α_i) × (-1)^{b_i}`
- **Gradient search**: Hill climbing to target resonance
- **Multi-start**: Parallel searches from different starting points

### 7. Inverse Resonance (`inverse.rs`)

Finding bit patterns with specific resonance:
- **Small n (≤20)**: Exhaustive search through Klein representatives
- **Medium n (≤40)**: Meet-in-the-middle algorithm
- **Large n**: 
  - Gradient-guided search
  - Sample-based approximation
  - Branch-and-bound with pruning

## Usage Patterns

### Basic Usage

```rust
use ccm_embedding::{AlphaVec, Resonance};
use ccm_core::BitWord;

// Generate alpha for 256-bit system
let alpha = AlphaVec::<f64>::for_bit_length(256)?;

// Compute resonance
let word = BitWord::from_bytes(&data);
let r = word.r(&alpha);
```

### Finding Patterns

```rust
use ccm_embedding::InverseResonance;

// Find patterns with specific resonance
let target = 100.0;
let patterns = BitWord::find_by_resonance(target, &alpha, 0.01)?;

// All results are Klein minima
for pattern in patterns {
    assert!(pattern.is_klein_minimum(&alpha));
}
```

### Conservation Verification

```rust
use ccm_embedding::ResonanceConservation;

// Verify conservation over appropriate cycle
let result = BitWord::verify_conservation(&alpha);
assert!(result.is_conserved);
```

### Large-Scale Operations

```rust
// For 1024-bit patterns
let alpha_1024 = AlphaVec::<f64>::for_bit_length(1024)?;

// Operations automatically use efficient algorithms
let classes = BitWord::resonance_spectrum(&alpha_1024); // Samples
let unity = BitWord::unity_positions(&alpha_1024, 1000); // Strategic points
```

## Performance Considerations

### Memory Usage

- **Alpha vectors**: O(n) storage for n bits
- **BitWord**: O(n/64) u64s for n bits
- **Resonance classes**: Sampled representation for large n

### Numerical Stability

- **Log domain**: Automatic for large products
- **Overflow detection**: Before each multiplication
- **Precision limits**: f64 sufficient for n ≤ 53 set bits

### Optimization Strategies

1. **Klein representatives**: Reduce search space by factor of 4
2. **Sampling**: Statistical approximation for large spaces
3. **Parallel computation**: Multi-start searches, independent samples
4. **Mathematical properties**: Use theoretical results instead of computation

## Mathematical Guarantees

1. **Resonance positivity**: R(b) > 0 for all b
2. **Unity constraint**: α_{n-2} × α_{n-1} = 1 always satisfied
3. **Klein group structure**: Always exactly 4 members
4. **Conservation laws**: Hold to numerical precision
5. **Homomorphic property**: Exact for identified subgroups

## Limitations and Tradeoffs

### Exact vs Approximate

- **Small n**: All operations are exact
- **Large n**: Some operations use sampling/approximation
- **Tradeoff**: Scalability vs completeness

### Time vs Space

- **Caching**: Not used to minimize memory
- **Recomputation**: Preferred over storage
- **Streaming**: Possible for conservation sums

### Numerical Precision

- **f32**: Not recommended (insufficient precision)
- **f64**: Standard choice, good for most applications
- **f128**: Future support for extreme precision needs

## Future Extensions

1. **GPU Acceleration**: Parallel resonance computation
2. **Symbolic Computation**: Exact resonance algebra
3. **Quantum Algorithms**: Superposition of resonances
4. **Distributed Computing**: Large-scale resonance analysis
5. **Hardware Implementation**: FPGA/ASIC for real-time processing

## References

- CLAUDE.md: Mathematical foundations and proofs
- Resonance Algebra Formalization: Complete mathematical treatment
- CCM Specification: Integration with coherence and symmetry