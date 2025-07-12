# Resonance Module Specification

**Version**: 1.0  
**Status**: Normative  
**Part of**: ccm-primitives v1.0+

## Overview

This specification defines the complete Resonance Algebra module for CCM (Coherence-Centric Mathematics). The module provides all resonance-related computations, algebraic structures, and mathematical properties required for efficient implementation of CCM algorithms, including but not limited to the BJC codec.

## Module Structure

```
resonance/
├── mod.rs              // Core Resonance trait (existing)
├── inverse.rs          // Inverse resonance mapping
├── classes.rs          // Resonance equivalence classes
├── conservation.rs     // Conservation laws and currents
├── homomorphic.rs      // Homomorphic subgroups
├── gradient.rs         // Resonance gradients and optimization
├── unity.rs            // Unity positions and harmonic centers
├── automorphism.rs     // Group actions on resonance space
├── window.rs           // Window alignment patterns
├── modular.rs          // Modular arithmetic properties
├── quantum.rs          // Quantum resonance operators (optional)
└── entropy.rs          // Information theoretic measures
```

## Core Traits and Types

### 1. Base Resonance Trait (existing, enhanced)

```rust
/// Core trait for resonance computation
pub trait Resonance<P: Float> {
    /// Compute resonance value R(b) = ∏ α_i^{b_i}
    fn r(&self, alpha: &AlphaVec<P>) -> P;
    
    /// Get Klein group members (up to 4 elements)
    fn class_members(&self) -> [Self; 4]
    where
        Self: Sized + Copy;
    
    /// NEW: Get Klein group representative (first N-2 bits)
    fn klein_representative(&self) -> Self
    where
        Self: Sized + Copy;
    
    /// NEW: Check if this is the Klein minimum
    fn is_klein_minimum(&self, alpha: &AlphaVec<P>) -> bool
    where
        Self: Sized + Copy;
}
```

### 2. Inverse Resonance Mapping

```rust
/// Trait for inverse resonance operations
pub trait InverseResonance<P: Float> {
    type Output;
    
    /// Find all values with given resonance that are Klein minima
    fn find_by_resonance(
        target: P,
        alpha: &AlphaVec<P>,
        tolerance: P,
    ) -> Result<Vec<Self::Output>, CcmError>;
    
    /// Decompose resonance into constituent alpha factors
    fn factor_resonance(
        r: P,
        alpha: &AlphaVec<P>,
    ) -> Result<Vec<Vec<usize>>, CcmError>;
    
    /// Solve the subset sum problem in log domain
    fn solve_log_subset_sum(
        target_log: P,
        log_alphas: &[P],
        tolerance: P,
    ) -> Vec<Vec<usize>>;
}
```

### 3. Resonance Classes

```rust
/// Resonance equivalence class information
#[derive(Debug, Clone)]
pub struct ResonanceClass<P: Float> {
    pub id: u8,                    // Class ID [0..95] for 8-bit
    pub representative: P,         // Canonical resonance value
    pub size: u8,                  // Number of Klein groups (2 or 4)
    pub members: Vec<u64>,         // Klein group representatives
}

/// Trait for resonance class operations
pub trait ResonanceClasses<P: Float> {
    /// Get the complete resonance spectrum
    fn resonance_spectrum(alpha: &AlphaVec<P>) -> Vec<P>;
    
    /// Map resonance value to its equivalence class
    fn resonance_class(r: P, alpha: &AlphaVec<P>) -> Option<ResonanceClass<P>>;
    
    /// Get class size distribution
    fn class_distribution(alpha: &AlphaVec<P>) -> ClassDistribution;
    
    /// Check if alpha values produce exactly 96 classes (for N=8)
    fn verify_class_count(alpha: &AlphaVec<P>, expected: usize) -> bool;
}

#[derive(Debug, Clone)]
pub struct ClassDistribution {
    pub total_classes: usize,
    pub size_2_count: usize,
    pub size_4_count: usize,
}
```

### 4. Conservation Laws

```rust
/// Resonance conservation and current
pub trait ResonanceConservation<P: Float> {
    /// Compute sum over a contiguous block
    fn resonance_sum(
        start: usize,
        count: usize,
        alpha: &AlphaVec<P>,
    ) -> P;
    
    /// Verify 768-cycle conservation law
    fn verify_conservation(alpha: &AlphaVec<P>) -> ConservationResult<P>;
    
    /// Compute resonance current J(n) = R(n+1) - R(n)
    fn resonance_current(n: usize, alpha: &AlphaVec<P>) -> P;
    
    /// Find current extrema
    fn current_extrema(alpha: &AlphaVec<P>, range: usize) -> CurrentExtrema;
}

#[derive(Debug)]
pub struct ConservationResult<P: Float> {
    pub sum: P,
    pub expected: P,           // 687.110133051847 for standard 8-bit
    pub error: P,
    pub is_conserved: bool,
}

#[derive(Debug)]
pub struct CurrentExtrema {
    pub max_position: usize,
    pub max_value: f64,
    pub min_position: usize,
    pub min_value: f64,
}
```

### 5. Homomorphic Subgroups

```rust
/// Homomorphic properties under XOR
pub trait HomomorphicResonance<P: Float> {
    /// Find all homomorphic bit pairs (where α_i * α_j = 1)
    fn find_homomorphic_pairs(alpha: &AlphaVec<P>) -> Vec<(usize, usize)>;
    
    /// Get all XOR-homomorphic subgroups
    fn homomorphic_subgroups(alpha: &AlphaVec<P>) -> Vec<HomomorphicSubgroup>;
    
    /// Check if a set of bits forms a homomorphic subgroup
    fn is_homomorphic_subset(bits: &[usize], alpha: &AlphaVec<P>) -> bool;
}

#[derive(Debug, Clone)]
pub struct HomomorphicSubgroup {
    pub generator: u64,
    pub elements: Vec<u64>,
    pub order: usize,
}
```

### 6. Resonance Gradients

```rust
/// Gradient and optimization operations
pub trait ResonanceGradient<P: Float> {
    /// Compute gradient with respect to bit flips
    fn bit_gradient(&self, alpha: &AlphaVec<P>) -> Vec<P>;
    
    /// Find steepest ascent/descent direction
    fn steepest_direction(
        &self,
        alpha: &AlphaVec<P>,
        maximize: bool,
    ) -> Option<usize>;
    
    /// Gradient-guided search from starting point
    fn gradient_search(
        start: Self,
        target: P,
        alpha: &AlphaVec<P>,
        max_steps: usize,
    ) -> Result<Self, CcmError>
    where
        Self: Sized;
}
```

### 7. Unity Structure

```rust
/// Unity positions and harmonic centers
pub trait UnityStructure {
    /// Find all positions where R = 1
    fn unity_positions<P: Float>(
        alpha: &AlphaVec<P>,
        range: usize,
    ) -> Vec<usize>;
    
    /// Check if value is near unity (within tolerance)
    fn is_near_unity<P: Float>(r: P, tolerance: P) -> bool;
    
    /// Get the standard unity positions for 8-bit
    fn standard_unity_positions() -> [usize; 12] {
        [0, 1, 48, 49, 256, 257, 304, 305, 512, 513, 560, 561]
    }
}
```

### 8. Automorphism Actions

```rust
/// Group actions on resonance space
pub trait AutomorphismAction {
    /// Apply automorphism of Z/nZ
    fn apply_automorphism(&self, phi: &Automorphism) -> Self;
    
    /// Find automorphisms preserving resonance
    fn resonance_preserving_auts<P: Float>(
        alpha: &AlphaVec<P>,
    ) -> Vec<Automorphism>;
}

#[derive(Debug, Clone)]
pub struct Automorphism {
    pub multiplier: u64,
    pub offset: u64,
    pub modulus: u64,
}
```

### 9. Window Alignment

```rust
/// Window alignment for factorization
pub trait WindowAlignment<P: Float> {
    /// Find alignment windows that may reveal factors
    fn find_alignment_windows(
        &self,
        alpha: &AlphaVec<P>,
        max_window_size: usize,
    ) -> Vec<AlignmentWindow>;
    
    /// Check if window exhibits factor structure
    fn check_factor_alignment(
        &self,
        window: &AlignmentWindow,
        alpha: &AlphaVec<P>,
    ) -> Option<FactorHint>;
}

#[derive(Debug)]
pub struct AlignmentWindow {
    pub start: usize,
    pub length: usize,
    pub resonance_sum: f64,
}

#[derive(Debug)]
pub struct FactorHint {
    pub confidence: f64,
    pub potential_factors: Vec<(u64, u64)>,
}
```

### 10. Information Theory

```rust
/// Information theoretic measures
pub trait ResonanceEntropy<P: Float> {
    /// Compute resonance entropy (bits of information)
    fn resonance_entropy(alpha: &AlphaVec<P>) -> P;
    
    /// Compression ratio achieved by resonance classes
    fn compression_ratio(alpha: &AlphaVec<P>) -> f64;
    
    /// Mutual information between bit positions
    fn bit_mutual_information(
        i: usize,
        j: usize,
        alpha: &AlphaVec<P>,
    ) -> P;
}
```

## Implementation Requirements

### Performance

1. **Caching**: Implementations SHOULD cache frequently computed values:
   - Resonance spectrum for repeated lookups
   - Unity positions
   - Homomorphic subgroups

2. **Parallelization**: Where applicable, implementations SHOULD:
   - Use parallel iterators for spectrum computation
   - Parallelize gradient computations
   - Use SIMD for bit operations

### Numerical Stability

1. **Log Domain**: Use log-domain computation when:
   - Resonance values exceed 10^100
   - More than 32 bits are set
   - Gradients involve large quotients

2. **Tolerance**: All floating-point comparisons MUST use appropriate tolerance:
   - Relative: `|a - b| / max(|a|, |b|) < ε`
   - Absolute: `|a - b| < ε` when near zero

### Error Handling

All operations that can fail MUST return `Result<T, CcmError>` with appropriate error variants:
- `SearchExhausted`: No solution found within limits
- `FpRange`: Numerical overflow/underflow
- `InvalidInput`: Invalid parameters
- `NotImplemented`: For optional features

## Feature Flags

```toml
[features]
# Core features (always enabled)
default = ["inverse", "classes", "conservation"]

# Extended features
full = ["gradient", "homomorphic", "unity", "automorphism", "window", "entropy"]

# Optional features
quantum = ["quantum-ops"]     # Quantum resonance operators
parallel = ["rayon"]          # Parallel computation
cache = ["lru"]              # LRU caching for expensive operations
```

## Testing Requirements

Each submodule MUST include tests verifying:

1. **Correctness**: Results match theoretical predictions
2. **Edge Cases**: Handle N=1, N=64, empty inputs
3. **Numerical Stability**: Large/small resonance values
4. **Performance**: Complete in reasonable time for N ≤ 32
5. **Conservation**: All conservation laws hold

## Examples

```rust
use ccm_primitives::resonance::{
    Resonance, InverseResonance, ResonanceClasses,
    ResonanceConservation, HomomorphicResonance
};

// Find all byte values with resonance ≈ π
let candidates = u8::find_by_resonance(
    std::f64::consts::PI,
    &alpha,
    1e-10
)?;

// Verify conservation law
let conservation = u8::verify_conservation(&alpha);
assert!(conservation.is_conserved);

// Find homomorphic subgroups
let subgroups = u8::homomorphic_subgroups(&alpha);
assert_eq!(subgroups.len(), 5); // Always 5 for proper unity constraint
```

## Version History

- 1.0: Initial specification covering complete Resonance Algebra

---

*End of Resonance Module Specification v1.0*