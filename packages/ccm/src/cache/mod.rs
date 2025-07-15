//! Caching system for CCM operations
//!
//! This module provides a multi-level cache to optimize expensive computations
//! in the CCM system. The cache stores frequently accessed values like alpha
//! constants, Klein group members, resonance values, and Clifford basis elements.

// Helper macro to handle different RwLock APIs
macro_rules! write_lock {
    ($lock:expr) => {{
        #[cfg(feature = "std")]
        {
            $lock.write().unwrap()
        }
        #[cfg(not(feature = "std"))]
        {
            $lock.write()
        }
    }};
}

macro_rules! read_lock {
    ($lock:expr) => {{
        #[cfg(feature = "std")]
        {
            $lock.read().unwrap()
        }
        #[cfg(not(feature = "std"))]
        {
            $lock.read()
        }
    }};
}

use ccm_coherence::CliffordElement;
use ccm_core::{BitWord, Float};
use ccm_embedding::AlphaVec;
use core::num::NonZeroUsize;
use lru::LruCache;

#[cfg(not(feature = "std"))]
use spin::RwLock;
#[cfg(feature = "std")]
use std::sync::RwLock;

#[cfg(not(feature = "std"))]
use hashbrown::HashMap;
#[cfg(feature = "std")]
use std::collections::HashMap;

#[cfg(all(not(feature = "std"), feature = "alloc"))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

/// Configuration for CCM cache
#[derive(Clone, Debug)]
pub struct CacheConfig {
    /// Maximum number of alpha values to cache (per dimension)
    pub alpha_cache_size: usize,
    /// Maximum number of Klein group computations to cache
    pub klein_cache_size: usize,
    /// Maximum number of resonance values to cache
    pub resonance_cache_size: usize,
    /// Maximum number of Clifford basis elements to cache
    pub basis_cache_size: usize,
    /// Maximum number of minimal resonance results to cache
    pub minimal_cache_size: usize,
    /// Whether to enable thread-safe caching (uses RwLock)
    pub thread_safe: bool,
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self {
            alpha_cache_size: 32,
            klein_cache_size: 1024,
            resonance_cache_size: 4096,
            basis_cache_size: 256,
            minimal_cache_size: 512,
            thread_safe: true,
        }
    }
}

/// Multi-level cache for CCM operations
pub struct CcmCache<P: Float> {
    /// Cache for alpha values indexed by dimension
    alpha_cache: RwLock<HashMap<usize, AlphaVec<P>>>,
    /// Cache for Klein group members
    klein_cache: RwLock<LruCache<BitWord, Vec<BitWord>>>,
    /// Cache for resonance values
    resonance_cache: RwLock<LruCache<(BitWord, usize), P>>,
    /// Cache for Clifford basis elements
    basis_cache: RwLock<HashMap<(usize, usize), CliffordElement<P>>>,
    /// Cache for minimal resonance results
    minimal_cache: RwLock<LruCache<BitWord, BitWord>>,
    /// Configuration
    config: CacheConfig,
    /// Statistics (only available with std feature)
    #[cfg(feature = "std")]
    stats: RwLock<CacheStats>,
}

impl<P: Float> Default for CcmCache<P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: Float> CcmCache<P> {
    /// Create a new cache with default configuration
    pub fn new() -> Self {
        Self::with_config(CacheConfig::default())
    }

    /// Create a new cache with custom configuration
    pub fn with_config(config: CacheConfig) -> Self {
        Self {
            alpha_cache: RwLock::new(HashMap::new()),
            klein_cache: RwLock::new(LruCache::new(
                NonZeroUsize::new(config.klein_cache_size).unwrap(),
            )),
            resonance_cache: RwLock::new(LruCache::new(
                NonZeroUsize::new(config.resonance_cache_size).unwrap(),
            )),
            basis_cache: RwLock::new(HashMap::new()),
            minimal_cache: RwLock::new(LruCache::new(
                NonZeroUsize::new(config.minimal_cache_size).unwrap(),
            )),
            config,
            #[cfg(feature = "std")]
            stats: RwLock::new(CacheStats::default()),
        }
    }

    /// Clear all caches
    pub fn clear(&self) {
        write_lock!(self.alpha_cache).clear();
        write_lock!(self.klein_cache).clear();
        write_lock!(self.resonance_cache).clear();
        write_lock!(self.basis_cache).clear();
        write_lock!(self.minimal_cache).clear();
    }

    /// Get cache statistics (only available with std feature)
    #[cfg(feature = "std")]
    pub fn stats(&self) -> CacheStats {
        read_lock!(self.stats).clone()
    }

    /// Reset cache statistics
    #[cfg(feature = "std")]
    pub fn reset_stats(&self) {
        *write_lock!(self.stats) = CacheStats::default();
    }
}

/// Cache operations for alpha values
impl<P: Float> CcmCache<P> {
    /// Get cached alpha values for a dimension
    pub fn get_alpha(&self, dimension: usize) -> Option<AlphaVec<P>> {
        let result = read_lock!(self.alpha_cache).get(&dimension).cloned();
        #[cfg(feature = "std")]
        {
            let mut stats = write_lock!(self.stats);
            if result.is_some() {
                stats.alpha_hits += 1;
            } else {
                stats.alpha_misses += 1;
            }
        }
        result
    }

    /// Store alpha values for a dimension
    pub fn put_alpha(&self, dimension: usize, alpha: AlphaVec<P>) {
        let mut cache = write_lock!(self.alpha_cache);
        if cache.len() >= self.config.alpha_cache_size {
            // Simple eviction: remove smallest dimension
            if let Some(&min_dim) = cache.keys().min() {
                cache.remove(&min_dim);
            }
        }
        cache.insert(dimension, alpha);
    }
}

/// Cache operations for Klein groups
impl<P: Float> CcmCache<P> {
    /// Get cached Klein group members
    pub fn get_klein_members(&self, word: &BitWord) -> Option<Vec<BitWord>> {
        let result = write_lock!(self.klein_cache).get(word).cloned();
        #[cfg(feature = "std")]
        {
            let mut stats = write_lock!(self.stats);
            if result.is_some() {
                stats.klein_hits += 1;
            } else {
                stats.klein_misses += 1;
            }
        }
        result
    }

    /// Store Klein group members
    pub fn put_klein_members(&self, word: BitWord, members: Vec<BitWord>) {
        write_lock!(self.klein_cache).put(word, members);
    }
}

/// Cache operations for resonance values
impl<P: Float> CcmCache<P> {
    /// Get cached resonance value
    pub fn get_resonance(&self, word: &BitWord, alpha_dim: usize) -> Option<P> {
        let result = write_lock!(self.resonance_cache)
            .get(&(word.clone(), alpha_dim))
            .cloned();
        #[cfg(feature = "std")]
        {
            let mut stats = write_lock!(self.stats);
            if result.is_some() {
                stats.resonance_hits += 1;
            } else {
                stats.resonance_misses += 1;
            }
        }
        result
    }

    /// Store resonance value
    pub fn put_resonance(&self, word: BitWord, alpha_dim: usize, resonance: P) {
        write_lock!(self.resonance_cache).put((word, alpha_dim), resonance);
    }
}

/// Cache operations for Clifford basis elements
impl<P: Float> CcmCache<P> {
    /// Get cached basis element
    pub fn get_basis_element(&self, dimension: usize, index: usize) -> Option<CliffordElement<P>> {
        let result = read_lock!(self.basis_cache)
            .get(&(dimension, index))
            .cloned();
        #[cfg(feature = "std")]
        {
            let mut stats = write_lock!(self.stats);
            if result.is_some() {
                stats.basis_hits += 1;
            } else {
                stats.basis_misses += 1;
            }
        }
        result
    }

    /// Store basis element
    pub fn put_basis_element(&self, dimension: usize, index: usize, element: CliffordElement<P>) {
        let mut cache = write_lock!(self.basis_cache);
        if cache.len() >= self.config.basis_cache_size {
            // Simple eviction: remove first element
            if let Some(&key) = cache.keys().next() {
                cache.remove(&key);
            }
        }
        cache.insert((dimension, index), element);
    }
}

/// Cache operations for minimal resonance
impl<P: Float> CcmCache<P> {
    /// Get cached minimal resonance result
    pub fn get_minimal(&self, word: &BitWord) -> Option<BitWord> {
        let result = write_lock!(self.minimal_cache).get(word).cloned();
        #[cfg(feature = "std")]
        {
            let mut stats = write_lock!(self.stats);
            if result.is_some() {
                stats.minimal_hits += 1;
            } else {
                stats.minimal_misses += 1;
            }
        }
        result
    }

    /// Store minimal resonance result
    pub fn put_minimal(&self, word: BitWord, minimal: BitWord) {
        write_lock!(self.minimal_cache).put(word, minimal);
    }
}

/// Cache statistics (optional feature)
#[cfg(feature = "std")]
#[derive(Default, Clone, Debug)]
pub struct CacheStats {
    pub alpha_hits: usize,
    pub alpha_misses: usize,
    pub klein_hits: usize,
    pub klein_misses: usize,
    pub resonance_hits: usize,
    pub resonance_misses: usize,
    pub basis_hits: usize,
    pub basis_misses: usize,
    pub minimal_hits: usize,
    pub minimal_misses: usize,
}

#[cfg(feature = "std")]
impl CacheStats {
    /// Total cache hits
    pub fn total_hits(&self) -> usize {
        self.alpha_hits
            + self.klein_hits
            + self.resonance_hits
            + self.basis_hits
            + self.minimal_hits
    }

    /// Total cache misses
    pub fn total_misses(&self) -> usize {
        self.alpha_misses
            + self.klein_misses
            + self.resonance_misses
            + self.basis_misses
            + self.minimal_misses
    }

    /// Cache hit rate (0.0 to 1.0)
    pub fn hit_rate(&self) -> f64 {
        let hits = self.total_hits() as f64;
        let total = (self.total_hits() + self.total_misses()) as f64;
        if total > 0.0 {
            hits / total
        } else {
            0.0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cache_creation() {
        let cache = CcmCache::<f64>::new();
        assert_eq!(cache.config.klein_cache_size, 1024);
    }

    #[test]
    fn test_cache_clear() {
        let cache = CcmCache::<f64>::new();
        cache.clear();
        // Cache should be empty after clear
        assert!(cache.get_alpha(8).is_none());
    }

    #[test]
    #[cfg(feature = "std")]
    fn test_cache_stats() {
        let stats = CacheStats {
            alpha_hits: 10,
            alpha_misses: 5,
            klein_hits: 20,
            klein_misses: 10,
            resonance_hits: 30,
            resonance_misses: 15,
            basis_hits: 40,
            basis_misses: 20,
            minimal_hits: 50,
            minimal_misses: 25,
        };

        assert_eq!(stats.total_hits(), 150);
        assert_eq!(stats.total_misses(), 75);
        assert!((stats.hit_rate() - 0.666).abs() < 0.001);
    }
}
