# Coherence-Based Page Specification

## Overview

Pages in CCM represent equivalence classes in the embedding space, organized by coherence properties rather than combinatorial enumeration. This specification defines how pages emerge from the mathematical structure of CCM.

## Mathematical Foundation

### Page Definition

A **coherence page** is an equivalence class of bit patterns under the coherence metric, defined by:

1. **Primary Structure**: Resonance value classes
2. **Secondary Structure**: Klein group orbits  
3. **Tertiary Structure**: Symmetry group actions (future)

### Key Properties

For an n-bit system:
- Number of resonance classes: `3 × 2^(n-2)` for n ≥ 3
- Klein group size: 4 (using last two bits for unity constraint)
- Maximum pages: `12 × 2^(n-2)` (resonance classes × Klein subdivisions)

### Page Indexing

Pages are indexed using a two-level scheme:
```
page_index = (resonance_class_index << 2) | klein_orbit_index
```

Where:
- `resonance_class_index`: Position in sorted list of unique resonance values
- `klein_orbit_index`: Position within Klein group (0-3)

## Core Types

### PageStructure

Represents the page configuration for a given bit length:

```rust
struct PageStructure<P: Float> {
    /// Number of bits
    bit_length: usize,
    
    /// Sorted list of unique resonance values
    resonance_values: Vec<P>,
    
    /// Mapping from resonance value to class index
    resonance_map: BTreeMap<OrdFloat<P>, usize>,
    
    /// Total number of pages
    total_pages: usize,
}
```

### ResonancePage

Represents a single coherence page:

```rust
struct ResonancePage<P: Float> {
    /// Page index
    index: usize,
    
    /// Resonance value for this page
    resonance: P,
    
    /// Klein orbit position (0-3)
    klein_orbit: u8,
    
    /// Canonical representative
    representative: BitWord,
}
```

## Operations

### 1. Page Index Calculation

Given a bit pattern, compute its page index:

```rust
fn coherence_page(pattern: &BitWord, alpha: &AlphaVec<P>) -> usize {
    // Step 1: Compute resonance value
    let resonance = pattern.r(alpha);
    
    // Step 2: Find resonance class index via binary search
    let resonance_class = find_resonance_class(resonance);
    
    // Step 3: Determine Klein orbit position
    let klein_orbit = klein_orbit_position(pattern);
    
    // Step 4: Combine into page index
    (resonance_class << 2) | klein_orbit
}
```

### 2. Page Membership

Find all patterns in a given page:

```rust
fn page_members(page_index: usize, structure: &PageStructure<P>) -> Vec<BitWord> {
    // Step 1: Extract resonance class and Klein orbit
    let resonance_class = page_index >> 2;
    let klein_orbit = page_index & 0b11;
    
    // Step 2: Get target resonance value
    let resonance = structure.resonance_values[resonance_class];
    
    // Step 3: Find all patterns with this resonance
    // (Using inverse resonance techniques)
    
    // Step 4: Filter to specific Klein orbit
}
```

### 3. Page Representative

Find the canonical representative of a page:

```rust
fn page_representative(page_index: usize) -> BitWord {
    // The representative is the Klein minimum
    // within the resonance class
}
```

## Resonance Class Enumeration

### Algorithm for Computing All Resonance Values

For n-bit patterns:

1. **Generate representative patterns**:
   - One representative per Klein equivalence class
   - Total representatives: `2^(n-2)` patterns

2. **Compute resonance for each**:
   - Apply resonance formula with alpha values
   - Klein group members share resonance

3. **Sort and deduplicate**:
   - Create sorted list of unique values
   - This gives exactly `3 × 2^(n-2)` values

### Efficient Computation

```rust
fn enumerate_resonance_classes(n: usize, alpha: &AlphaVec<P>) -> Vec<P> {
    let mut resonances = Vec::new();
    
    // Generate Klein representatives (first n-2 bits vary)
    for i in 0..(1 << (n-2)) {
        // Create pattern with first n-2 bits from i
        let pattern = BitWord::from_klein_representative(i, n);
        
        // Compute resonance for all 4 Klein variants
        for klein in 0..4 {
            let variant = pattern.apply_klein_transform(klein);
            resonances.push(variant.r(alpha));
        }
    }
    
    // Sort and deduplicate
    resonances.sort_unstable();
    resonances.dedup();
    resonances
}
```

## Klein Group Structure

### Klein Orbit Position

Within a resonance class, Klein group members are ordered by:

1. **Lexicographic order** of the last two bits
2. **Mapping**: `00 → 0, 01 → 1, 10 → 2, 11 → 3`

### Klein Transform

```rust
fn apply_klein_transform(pattern: &BitWord, klein: u8) -> BitWord {
    let mut result = pattern.clone();
    let n = pattern.len();
    
    // Apply XOR to last two bits based on klein value
    if klein & 1 != 0 {
        result.flip_bit(n - 2);
    }
    if klein & 2 != 0 {
        result.flip_bit(n - 1);
    }
    
    result
}
```

## Performance Considerations

### Caching Strategy

1. **PageStructure cache**: Store per bit length
2. **Resonance lookups**: Use binary search on sorted list
3. **Representative cache**: Store page representatives

### Complexity Analysis

- Page index computation: O(log k) where k = number of resonance classes
- Page membership: O(m) where m = patterns per resonance class  
- Structure generation: O(2^n) but done once per bit length

## Edge Cases

### Small Bit Lengths

- **n = 0**: Single page (degenerate case)
- **n = 1**: Single page (no Klein structure)
- **n = 2**: 3 pages (Klein group exists but no unity constraint)
- **n ≥ 3**: Full structure with `3 × 2^(n-2)` resonance classes

### Floating Point Considerations

- Use epsilon-based comparison for resonance equality
- Ensure consistent ordering despite rounding
- Consider using rational arithmetic for exact computation

## Future Extensions

### Symmetry Integration

When ccm-symmetry is implemented, pages will be further refined by:
- Orbit decomposition under symmetry group
- Finer equivalence classes
- Structure: `resonance × klein × symmetry`

### Coherence Norm Refinement

When full Clifford algebra is implemented:
- Use actual coherence norm instead of just resonance
- Grade-based decomposition
- Richer page structure

## Implementation Notes

1. **Start with resonance-based pages** (current capability)
2. **Ensure extensibility** for future coherence norm
3. **Maintain API stability** as we add features
4. **Test thoroughly** at boundary conditions
5. **Document limitations** of current approach

This specification provides a mathematically grounded, overflow-free page system that scales to arbitrary bit lengths while maintaining meaningful structure aligned with CCM principles.