# CCM - Complete Coherence-Centric Mathematics Implementation

The `ccm` package provides the complete, integrated implementation of Coherence-Centric Mathematics. It brings together the three fundamental mathematical structures (embedding, coherence, symmetry) into a unified system that applications can use directly.

## Features

- **Unified API**: Single interface for all CCM operations
- **Scale-Adaptive Algorithms**: Automatic strategy selection based on input size
- **High-Performance Cache**: Multi-level LRU cache for expensive computations
- **Thread-Safe**: Concurrent access with RwLock protection
- **No-std Support**: Works in embedded environments

## Basic Usage

```rust
use ccm::{StandardCCM, CCMCore};
use ccm::prelude::*;

// Create CCM instance
let ccm = StandardCCM::<f64>::new(8)?;

// Generate alpha values
let alpha = ccm.generate_alpha()?;

// Create input
let input = BitWord::from_u8(42);

// Find minimal representation
let minimal = ccm.find_minimum_resonance(&input, &alpha)?;

// Embed into Clifford algebra
let section = ccm.embed(&minimal, &alpha)?;

// Compute coherence norm
let norm = ccm.coherence_norm(&section);
```

## Cache System

The CCM implementation includes a sophisticated multi-level cache to optimize performance:

### Cache Levels

1. **Alpha Cache**: Stores generated alpha values per dimension
2. **Klein Cache**: Caches Klein group member computations
3. **Resonance Cache**: Stores resonance value calculations
4. **Basis Cache**: Caches Clifford basis elements
5. **Minimal Cache**: Stores minimal resonance results

### Cache Configuration

```rust
use ccm::cache::CacheConfig;

let config = CacheConfig {
    alpha_cache_size: 32,      // Max alpha values to cache
    klein_cache_size: 1024,    // Max Klein groups to cache
    resonance_cache_size: 4096,// Max resonance values
    basis_cache_size: 256,     // Max basis elements
    minimal_cache_size: 512,   // Max minimal results
    thread_safe: true,         // Enable thread safety
};

let ccm = StandardCCM::<f64>::with_cache_config(8, config)?;
```

### Cache Warming

Pre-populate the cache with commonly used values:

```rust
// Warm cache with common patterns
ccm.warm_cache()?;
```

### Cache Management

```rust
// Clear all caches
ccm.clear_cache();

// Get cache statistics (requires std feature)
#[cfg(feature = "std")]
{
    let stats = ccm.cache_stats();
    println!("Cache hit rate: {:.2}%", stats.hit_rate() * 100.0);
    println!("Total hits: {}", stats.total_hits());
    println!("Total misses: {}", stats.total_misses());
    
    // Reset statistics
    ccm.reset_cache_stats();
}
```

## Advanced Features

### Scale-Adaptive Search

The implementation automatically selects optimal algorithms based on dimension:

```rust
// Search for BitWords with specific resonance
let target = 1.618; // Golden ratio
let tolerance = 0.001;
let results = ccm.search_by_resonance(target, &alpha, tolerance)?;
```

- **n ≤ 20**: Direct exhaustive search
- **20 < n ≤ 64**: Klein group algebraic search
- **n > 64**: Full geometric search (future)

### Symmetry Operations

Apply group transformations while preserving CCM structure:

```rust
// Apply symmetry transformation
let g = /* group element */;
let transformed = ccm.apply_symmetry(&section, &g)?;

// Verify invariance
assert!((ccm.coherence_norm(&section) - ccm.coherence_norm(&transformed)).abs() < 1e-10);
```

## Performance

The cache system provides significant performance improvements:

- **Alpha generation**: ~1000x faster after first computation
- **Klein members**: ~100x faster for repeated queries
- **Resonance search**: ~10x faster with populated cache
- **Minimal resonance**: ~50x faster for common patterns

Run benchmarks:
```bash
cargo bench --features std
```

## Features

- `default`: Enables std and alloc
- `std`: Standard library support (enables statistics, threading)
- `alloc`: Heap allocation support

## Mathematical Foundation

The implementation is based on three axioms:

1. **Coherence Inner Product** (Axiom A1): Grade-orthogonal metric
2. **Minimal Embedding** (Axiom A2): Unique minimal norm representation
3. **Symmetry Group Action** (Axiom A3): Structure-preserving transformations

These work together to enable:
- Efficient data encoding
- Integer factorization
- Quantum state embeddings
- Coherence minimization

## Thread Safety

With the `std` feature, all cache operations are thread-safe:

```rust
use std::sync::Arc;
use std::thread;

let ccm = Arc::new(StandardCCM::<f64>::new(8)?);

let handles: Vec<_> = (0..4).map(|i| {
    let ccm_clone = Arc::clone(&ccm);
    thread::spawn(move || {
        let alpha = ccm_clone.generate_alpha().unwrap();
        // Concurrent cache access is safe
        let word = BitWord::from_u8(i * 10);
        ccm_clone.find_minimum_resonance(&word, &alpha)
    })
}).collect();
```

## Examples

See the `examples/` directory for:
- Basic CCM usage
- Cache optimization strategies
- Parallel computation patterns
- Custom cache configurations

## License

MIT