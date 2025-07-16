# Boundary Detection Module Specification

## Overview

The boundary detection module identifies natural decomposition points in sequences of Clifford elements. These boundaries represent transitions between coherently composed parts of a mathematical object, enabling effective decomposition strategies.

## Mathematical Foundation

### Boundary Definition

A **boundary** is a position in a sequence of sections where the mathematical structure exhibits a significant transition. This can manifest as:

1. **Coherence discontinuity**: Sharp changes in coherence coupling
2. **Symmetry breaking**: Loss or change of symmetry properties
3. **Conservation transitions**: Changes in conserved quantities
4. **Structural alignment**: Natural period boundaries (e.g., 256-byte pages)
5. **Algebraic transitions**: Klein group or other algebraic structure changes

### Confidence Scoring

Each detected boundary has a confidence score ∈ [0, 1] representing the strength of evidence:
- **0.0-0.3**: Weak evidence, likely noise
- **0.3-0.5**: Moderate evidence, possible boundary
- **0.5-0.7**: Strong evidence, probable boundary
- **0.7-1.0**: Very strong evidence, definite boundary

## Core Types

### Boundary Structure

```rust
pub struct Boundary {
    /// Position in the section array (between sections[i-1] and sections[i])
    pub position: usize,
    
    /// Confidence score (0.0 to 1.0)
    pub confidence: f64,
    
    /// Type of boundary detected
    pub boundary_type: BoundaryType,
    
    /// Additional metadata
    pub metadata: BoundaryMetadata,
}

pub enum BoundaryType {
    /// Low coherence coupling between sections
    WeakCoupling,
    
    /// Symmetry break point
    SymmetryBreak,
    
    /// Conservation law boundary
    ConservationBoundary,
    
    /// Page-aligned boundary (256-period)
    PageAligned,
    
    /// Klein group transition
    KleinTransition,
    
    /// Combined indicators
    Multiple(Vec<BoundaryType>),
}

pub struct BoundaryMetadata {
    /// Coherence values before and after boundary
    pub coherence_before: f64,
    pub coherence_after: f64,
    
    /// Detected symmetries before and after
    pub symmetries_before: Vec<SymmetryType>,
    pub symmetries_after: Vec<SymmetryType>,
    
    /// Conservation quantities that changed
    pub changed_quantities: Vec<String>,
    
    /// Additional detector-specific data
    pub detector_data: HashMap<String, f64>,
}
```

## Boundary Detectors

### 1. Weak Coupling Detector

Identifies boundaries where coherence coupling between adjacent sections is minimal.

#### Algorithm

```rust
fn detect_weak_coupling(sections: &[CliffordElement<P>], ccm: &StandardCCM<P>) -> Vec<Boundary> {
    let mut boundaries = Vec::new();
    
    // Compute pairwise coherence products
    for i in 1..sections.len() {
        let coupling = ccm.coherence_product(&sections[i-1], &sections[i]);
        
        // Normalize by individual norms
        let norm_before = ccm.coherence_norm(&sections[i-1]);
        let norm_after = ccm.coherence_norm(&sections[i]);
        let normalized_coupling = coupling / (norm_before * norm_after).sqrt();
        
        // Weak coupling threshold (empirically determined)
        if normalized_coupling < self.coupling_threshold {
            let confidence = 1.0 - normalized_coupling / self.coupling_threshold;
            
            boundaries.push(Boundary {
                position: i,
                confidence,
                boundary_type: BoundaryType::WeakCoupling,
                metadata: BoundaryMetadata {
                    coherence_before: norm_before.to_f64(),
                    coherence_after: norm_after.to_f64(),
                    detector_data: hashmap!{
                        "coupling".to_string() => coupling.to_f64(),
                        "normalized_coupling".to_string() => normalized_coupling.to_f64(),
                    },
                    ..Default::default()
                },
            });
        }
    }
    
    boundaries
}
```

#### Parameters

- `coupling_threshold`: Default 0.1, lower values indicate weaker coupling
- `min_section_norm`: Minimum norm to consider (avoid numerical issues)

### 2. Symmetry Break Detector

Identifies positions where symmetry properties change significantly.

#### Algorithm

```rust
fn detect_symmetry_breaks(sections: &[CliffordElement<P>], ccm: &StandardCCM<P>) -> Vec<Boundary> {
    let mut boundaries = Vec::new();
    
    // Analyze symmetries in sliding windows
    let window_size = 4; // Adjustable parameter
    
    for i in window_size..sections.len()-window_size {
        // Analyze symmetry before boundary
        let before_window = &sections[i-window_size..i];
        let symmetries_before = analyze_window_symmetries(before_window, ccm);
        
        // Analyze symmetry after boundary
        let after_window = &sections[i..i+window_size];
        let symmetries_after = analyze_window_symmetries(after_window, ccm);
        
        // Compute symmetry change score
        let change_score = compute_symmetry_change(symmetries_before, symmetries_after);
        
        if change_score > self.symmetry_threshold {
            boundaries.push(Boundary {
                position: i,
                confidence: change_score.min(1.0),
                boundary_type: BoundaryType::SymmetryBreak,
                metadata: BoundaryMetadata {
                    symmetries_before,
                    symmetries_after,
                    detector_data: hashmap!{
                        "change_score".to_string() => change_score,
                    },
                    ..Default::default()
                },
            });
        }
    }
    
    boundaries
}

fn analyze_window_symmetries(window: &[CliffordElement<P>], ccm: &StandardCCM<P>) -> Vec<SymmetryType> {
    let mut symmetries = Vec::new();
    
    // Check for Klein group structure
    if has_klein_structure(window, ccm) {
        symmetries.push(SymmetryType::Klein);
    }
    
    // Check for cyclic patterns
    if let Some(period) = find_cyclic_period(window, ccm) {
        symmetries.push(SymmetryType::Cyclic(period));
    }
    
    // Check for reflection symmetry
    if has_reflection_symmetry(window, ccm) {
        symmetries.push(SymmetryType::Reflection);
    }
    
    symmetries
}
```

#### Symmetry Analysis Functions

1. **Klein Structure Detection**:
   - Check if 4 consecutive sections form Klein group under appropriate operation
   - Use resonance values and XOR relationships

2. **Cyclic Pattern Detection**:
   - Compute autocorrelation of coherence norms
   - Identify periodic patterns in grade distributions

3. **Reflection Symmetry**:
   - Compare sections equidistant from center
   - Check coherence product symmetry

### 3. Conservation Boundary Detector

Identifies boundaries where conserved quantities change, indicating separate coherent parts.

#### Algorithm

```rust
fn detect_conservation_boundaries(
    sections: &[CliffordElement<P>], 
    ccm: &StandardCCM<P>,
    conservation_laws: &[Box<dyn ConservationLaw<P>>]
) -> Vec<Boundary> {
    let mut boundaries = Vec::new();
    
    // Compute conserved quantities in sliding windows
    let window_size = 8; // Must be multiple of conservation period
    
    for i in window_size..sections.len()-window_size {
        let mut changed_quantities = Vec::new();
        let mut total_violation = 0.0;
        
        for law in conservation_laws {
            // Compute quantity before potential boundary
            let before_window = &sections[i-window_size..i];
            let q_before = compute_window_quantity(before_window, law, ccm);
            
            // Compute quantity after potential boundary
            let after_window = &sections[i..i+window_size];
            let q_after = compute_window_quantity(after_window, law, ccm);
            
            // Check for significant change
            let relative_change = (q_after - q_before).abs() / q_before.abs().max(1e-10);
            
            if relative_change > self.conservation_threshold {
                changed_quantities.push(law.name().to_string());
                total_violation += relative_change;
            }
        }
        
        if !changed_quantities.is_empty() {
            let confidence = (total_violation / changed_quantities.len() as f64).min(1.0);
            
            boundaries.push(Boundary {
                position: i,
                confidence,
                boundary_type: BoundaryType::ConservationBoundary,
                metadata: BoundaryMetadata {
                    changed_quantities,
                    detector_data: hashmap!{
                        "total_violation".to_string() => total_violation,
                    },
                    ..Default::default()
                },
            });
        }
    }
    
    boundaries
}
```

### 4. Page-Aligned Boundary Detector

Identifies boundaries that align with natural 256-element periods in the resonance structure.

#### Algorithm

```rust
fn detect_page_boundaries(sections: &[CliffordElement<P>], ccm: &StandardCCM<P>) -> Vec<Boundary> {
    let mut boundaries = Vec::new();
    let page_size = 256;
    
    for i in (page_size..sections.len()).step_by(page_size) {
        // Verify this is actually a page boundary by checking resonance patterns
        let boundary_strength = verify_page_boundary(sections, i, ccm);
        
        if boundary_strength > 0.0 {
            boundaries.push(Boundary {
                position: i,
                confidence: boundary_strength,
                boundary_type: BoundaryType::PageAligned,
                metadata: BoundaryMetadata {
                    detector_data: hashmap!{
                        "page_number".to_string() => (i / page_size) as f64,
                        "alignment_score".to_string() => boundary_strength,
                    },
                    ..Default::default()
                },
            });
        }
    }
    
    boundaries
}

fn verify_page_boundary(sections: &[CliffordElement<P>], pos: usize, ccm: &StandardCCM<P>) -> f64 {
    // Check for resonance reset pattern
    let window = 16; // Check elements around boundary
    
    if pos < window || pos + window > sections.len() {
        return 0.0;
    }
    
    // Compute resonance discontinuity
    let before_resonances = compute_resonances(&sections[pos-window..pos], ccm);
    let after_resonances = compute_resonances(&sections[pos..pos+window], ccm);
    
    // Check for characteristic page transition pattern
    let pattern_match = check_transition_pattern(before_resonances, after_resonances);
    
    pattern_match
}
```

### 5. Klein Transition Detector

Identifies boundaries where Klein group structure changes.

#### Algorithm

```rust
fn detect_klein_transitions(sections: &[CliffordElement<P>], ccm: &StandardCCM<P>) -> Vec<Boundary> {
    let mut boundaries = Vec::new();
    
    // Klein groups operate on 4-element sets
    for i in 4..sections.len()-4 {
        // Check Klein structure before
        let before_klein = analyze_klein_structure(&sections[i-4..i], ccm);
        
        // Check Klein structure after
        let after_klein = analyze_klein_structure(&sections[i..i+4], ccm);
        
        // Detect transitions
        if before_klein.is_valid && !after_klein.is_valid {
            // Klein structure lost
            boundaries.push(create_klein_boundary(i, 0.8, "klein_lost"));
        } else if !before_klein.is_valid && after_klein.is_valid {
            // Klein structure gained
            boundaries.push(create_klein_boundary(i, 0.8, "klein_gained"));
        } else if before_klein.is_valid && after_klein.is_valid 
                && before_klein.group_type != after_klein.group_type {
            // Klein structure changed
            boundaries.push(create_klein_boundary(i, 0.9, "klein_changed"));
        }
    }
    
    boundaries
}

struct KleinAnalysis {
    is_valid: bool,
    group_type: KleinGroupType,
    resonance_sum: f64,
    xor_homomorphic: bool,
}

enum KleinGroupType {
    Unity,      // All elements have resonance 1
    Scaled(f64), // All elements have same non-unity resonance
    Mixed,      // Different resonances but valid Klein structure
}
```

## Boundary Fusion and Ranking

When multiple detectors identify nearby boundaries, they should be fused:

```rust
fn fuse_boundaries(all_boundaries: Vec<Boundary>, fusion_distance: usize) -> Vec<Boundary> {
    // Sort by position
    let mut sorted = all_boundaries;
    sorted.sort_by_key(|b| b.position);
    
    let mut fused = Vec::new();
    let mut current_group = vec![sorted[0].clone()];
    
    for boundary in sorted.into_iter().skip(1) {
        if boundary.position - current_group.last().unwrap().position <= fusion_distance {
            current_group.push(boundary);
        } else {
            // Fuse current group and start new one
            fused.push(fuse_boundary_group(current_group));
            current_group = vec![boundary];
        }
    }
    
    if !current_group.is_empty() {
        fused.push(fuse_boundary_group(current_group));
    }
    
    fused
}

fn fuse_boundary_group(group: Vec<Boundary>) -> Boundary {
    // Weighted average position
    let total_confidence: f64 = group.iter().map(|b| b.confidence).sum();
    let position = group.iter()
        .map(|b| b.position as f64 * b.confidence)
        .sum::<f64>() / total_confidence;
    
    // Combined confidence (using root mean square)
    let confidence = (group.iter()
        .map(|b| b.confidence * b.confidence)
        .sum::<f64>() / group.len() as f64)
        .sqrt();
    
    // Collect all boundary types
    let mut types = Vec::new();
    for b in &group {
        match &b.boundary_type {
            BoundaryType::Multiple(ts) => types.extend(ts.clone()),
            t => types.push(t.clone()),
        }
    }
    
    Boundary {
        position: position.round() as usize,
        confidence: confidence.min(1.0),
        boundary_type: if types.len() == 1 {
            types[0].clone()
        } else {
            BoundaryType::Multiple(types)
        },
        metadata: merge_metadata(group),
    }
}
```

## Performance Optimization

### Caching Strategy

```rust
pub struct BoundaryCache<P: Float> {
    // Cache coherence products between adjacent sections
    coherence_cache: HashMap<(usize, usize), P>,
    
    // Cache symmetry analysis results
    symmetry_cache: HashMap<Range<usize>, Vec<SymmetryType>>,
    
    // Cache conservation quantities
    conservation_cache: HashMap<(Range<usize>, ConservationLawId), P>,
}
```

### Parallel Detection

Different detectors can run in parallel:

```rust
#[cfg(feature = "rayon")]
fn detect_all_boundaries_parallel(
    sections: &[CliffordElement<P>],
    ccm: &StandardCCM<P>,
    detectors: &[Box<dyn BoundaryDetector<P>>],
) -> Vec<Boundary> {
    use rayon::prelude::*;
    
    let all_boundaries: Vec<Vec<Boundary>> = detectors
        .par_iter()
        .map(|detector| detector.detect_boundaries(sections, ccm))
        .collect();
    
    let mut combined = Vec::new();
    for boundaries in all_boundaries {
        combined.extend(boundaries);
    }
    
    fuse_boundaries(combined, 3) // Fuse within 3 positions
}
```

## Configuration Parameters

```rust
pub struct BoundaryDetectionConfig {
    /// Weak coupling detector parameters
    pub coupling_threshold: f64, // Default: 0.1
    pub min_section_norm: f64,   // Default: 1e-10
    
    /// Symmetry break detector parameters
    pub symmetry_window_size: usize, // Default: 4
    pub symmetry_threshold: f64,      // Default: 0.5
    
    /// Conservation boundary parameters
    pub conservation_window_size: usize, // Default: 8
    pub conservation_threshold: f64,     // Default: 0.1
    
    /// Klein transition parameters
    pub klein_window_size: usize, // Default: 4
    
    /// Fusion parameters
    pub fusion_distance: usize,   // Default: 3
    pub min_confidence: f64,      // Default: 0.3
}
```

## Testing Strategy

1. **Unit tests** for each detector with known patterns
2. **Integration tests** with synthetic data having known boundaries
3. **Property tests**: Boundaries should be consistent and well-ordered
4. **Performance benchmarks** for large section arrays
5. **Validation against known decompositions** (e.g., factorization)

## Future Extensions

1. **Machine learning detectors**: Train on known good decompositions
2. **Adaptive thresholds**: Adjust based on data characteristics
3. **Hierarchical boundaries**: Multi-scale boundary detection
4. **Domain-specific detectors**: Custom detectors for specific applications
5. **Confidence calibration**: Ensure confidence scores are well-calibrated probabilities