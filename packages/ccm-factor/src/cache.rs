//! Caching system for CCM-Factor to improve performance

use crate::error::{FactorError, Result};

use ccm_coherence::CliffordElement;
use ccm_core::BitWord;
use ccm_embedding::{AlphaVec, Resonance};
use num_traits::Float;

#[cfg(feature = "std")]
use std::collections::HashMap;
#[cfg(feature = "std")]
use std::sync::{Arc, RwLock};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::collections::HashMap;
#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::sync::{Arc, RwLock};

/// Cache configuration
#[derive(Clone, Debug)]
pub struct CacheConfig {
    /// Maximum number of Klein groups to cache
    pub klein_cache_size: usize,
    /// Maximum number of resonance values to cache
    pub resonance_cache_size: usize,
    /// Maximum number of Clifford basis elements to cache
    pub basis_cache_size: usize,
    /// Maximum number of grade decompositions to cache
    pub grade_cache_size: usize,
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self {
            klein_cache_size: 1024,
            resonance_cache_size: 4096,
            basis_cache_size: 256,
            grade_cache_size: 512,
        }
    }
}

/// Multi-level cache for CCM-Factor operations
pub struct FactorCache<P: Float> {
    /// Cache for Klein group members
    klein_cache: Arc<RwLock<HashMap<BitWord, Vec<BitWord>>>>,
    /// Cache for resonance values
    resonance_cache: Arc<RwLock<HashMap<BitWord, P>>>,
    /// Cache for Clifford basis elements
    basis_cache: Arc<RwLock<HashMap<(usize, usize), CliffordElement<P>>>>,
    /// Cache for grade decompositions
    grade_cache: Arc<RwLock<HashMap<BitWord, Vec<usize>>>>,
    /// Configuration
    config: CacheConfig,
}

impl<P: Float + num_traits::FromPrimitive> FactorCache<P> {
    /// Create a new cache with default configuration
    pub fn new() -> Self {
        Self::with_config(CacheConfig::default())
    }

    /// Create a new cache with custom configuration
    pub fn with_config(config: CacheConfig) -> Self {
        Self {
            klein_cache: Arc::new(RwLock::new(HashMap::new())),
            resonance_cache: Arc::new(RwLock::new(HashMap::new())),
            basis_cache: Arc::new(RwLock::new(HashMap::new())),
            grade_cache: Arc::new(RwLock::new(HashMap::new())),
            config,
        }
    }

    /// Get or compute Klein group members
    pub fn get_or_compute_klein_members(&self, bitword: &BitWord) -> Result<Vec<BitWord>> {
        // Check cache first
        {
            let cache = self.klein_cache.read()
                .map_err(|_| FactorError::InternalError("Cache lock poisoned".into()))?;
            if let Some(members) = cache.get(bitword) {
                return Ok(members.clone());
            }
        }

        // Compute if not cached
        let members = <BitWord as Resonance<P>>::class_members(bitword);

        // Store in cache if there's room
        {
            let mut cache = self.klein_cache.write()
                .map_err(|_| FactorError::InternalError("Cache lock poisoned".into()))?;
            
            if cache.len() < self.config.klein_cache_size {
                cache.insert(bitword.clone(), members.clone());
            } else if self.config.klein_cache_size > 0 {
                // Simple eviction: remove first entry
                if let Some(first_key) = cache.keys().next().cloned() {
                    cache.remove(&first_key);
                    cache.insert(bitword.clone(), members.clone());
                }
            }
        }

        Ok(members)
    }

    /// Get or compute resonance value
    pub fn get_or_compute_resonance(&self, bitword: &BitWord, alpha: &AlphaVec<P>) -> Result<P> {
        // Check cache first
        {
            let cache = self.resonance_cache.read()
                .map_err(|_| FactorError::InternalError("Cache lock poisoned".into()))?;
            if let Some(&resonance) = cache.get(bitword) {
                return Ok(resonance);
            }
        }

        // Compute if not cached
        let resonance = bitword.r(alpha);

        // Store in cache if there's room
        {
            let mut cache = self.resonance_cache.write()
                .map_err(|_| FactorError::InternalError("Cache lock poisoned".into()))?;
            
            if cache.len() < self.config.resonance_cache_size {
                cache.insert(bitword.clone(), resonance);
            } else if self.config.resonance_cache_size > 0 {
                // Simple eviction: remove first entry
                if let Some(first_key) = cache.keys().next().cloned() {
                    cache.remove(&first_key);
                    cache.insert(bitword.clone(), resonance);
                }
            }
        }

        Ok(resonance)
    }

    /// Get or compute basis element
    pub fn get_or_compute_basis(
        &self,
        dimension: usize,
        index: usize,
        compute_fn: impl FnOnce() -> Result<CliffordElement<P>>,
    ) -> Result<CliffordElement<P>> {
        let key = (dimension, index);

        // Check cache first
        {
            let cache = self.basis_cache.read()
                .map_err(|_| FactorError::InternalError("Cache lock poisoned".into()))?;
            if let Some(element) = cache.get(&key) {
                return Ok(element.clone());
            }
        }

        // Compute if not cached
        let element = compute_fn()?;

        // Store in cache if there's room
        {
            let mut cache = self.basis_cache.write()
                .map_err(|_| FactorError::InternalError("Cache lock poisoned".into()))?;
            
            if cache.len() < self.config.basis_cache_size {
                cache.insert(key, element.clone());
            } else if self.config.basis_cache_size > 0 {
                // Simple eviction: remove first entry
                if let Some(first_key) = cache.keys().next().cloned() {
                    cache.remove(&first_key);
                    cache.insert(key, element.clone());
                }
            }
        }

        Ok(element)
    }

    /// Get or compute grade decomposition
    pub fn get_or_compute_grades(
        &self,
        bitword: &BitWord,
        compute_fn: impl FnOnce() -> Vec<usize>,
    ) -> Result<Vec<usize>> {
        // Check cache first
        {
            let cache = self.grade_cache.read()
                .map_err(|_| FactorError::InternalError("Cache lock poisoned".into()))?;
            if let Some(grades) = cache.get(bitword) {
                return Ok(grades.clone());
            }
        }

        // Compute if not cached
        let grades = compute_fn();

        // Store in cache if there's room
        {
            let mut cache = self.grade_cache.write()
                .map_err(|_| FactorError::InternalError("Cache lock poisoned".into()))?;
            
            if cache.len() < self.config.grade_cache_size {
                cache.insert(bitword.clone(), grades.clone());
            } else if self.config.grade_cache_size > 0 {
                // Simple eviction: remove first entry
                if let Some(first_key) = cache.keys().next().cloned() {
                    cache.remove(&first_key);
                    cache.insert(bitword.clone(), grades.clone());
                }
            }
        }

        Ok(grades)
    }

    /// Clear all caches
    pub fn clear(&self) -> Result<()> {
        self.klein_cache.write()
            .map_err(|_| FactorError::InternalError("Cache lock poisoned".into()))?
            .clear();
        self.resonance_cache.write()
            .map_err(|_| FactorError::InternalError("Cache lock poisoned".into()))?
            .clear();
        self.basis_cache.write()
            .map_err(|_| FactorError::InternalError("Cache lock poisoned".into()))?
            .clear();
        self.grade_cache.write()
            .map_err(|_| FactorError::InternalError("Cache lock poisoned".into()))?
            .clear();
        Ok(())
    }

    /// Get cache statistics
    #[cfg(feature = "std")]
    pub fn stats(&self) -> Result<CacheStats> {
        let klein_size = self.klein_cache.read()
            .map_err(|_| FactorError::InternalError("Cache lock poisoned".into()))?
            .len();
        let resonance_size = self.resonance_cache.read()
            .map_err(|_| FactorError::InternalError("Cache lock poisoned".into()))?
            .len();
        let basis_size = self.basis_cache.read()
            .map_err(|_| FactorError::InternalError("Cache lock poisoned".into()))?
            .len();
        let grade_size = self.grade_cache.read()
            .map_err(|_| FactorError::InternalError("Cache lock poisoned".into()))?
            .len();

        Ok(CacheStats {
            klein_entries: klein_size,
            resonance_entries: resonance_size,
            basis_entries: basis_size,
            grade_entries: grade_size,
            config: self.config.clone(),
        })
    }
}

/// Cache statistics
#[cfg(feature = "std")]
#[derive(Clone, Debug)]
pub struct CacheStats {
    pub klein_entries: usize,
    pub resonance_entries: usize,
    pub basis_entries: usize,
    pub grade_entries: usize,
    pub config: CacheConfig,
}

#[cfg(feature = "std")]
impl CacheStats {
    /// Get total number of cached entries
    pub fn total_entries(&self) -> usize {
        self.klein_entries + self.resonance_entries + self.basis_entries + self.grade_entries
    }

    /// Get cache utilization as a percentage
    pub fn utilization(&self) -> f64 {
        let total_capacity = self.config.klein_cache_size
            + self.config.resonance_cache_size
            + self.config.basis_cache_size
            + self.config.grade_cache_size;
        
        if total_capacity == 0 {
            0.0
        } else {
            (self.total_entries() as f64 / total_capacity as f64) * 100.0
        }
    }
}

impl<P: Float + num_traits::FromPrimitive> Default for FactorCache<P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: Float + num_traits::FromPrimitive> Clone for FactorCache<P> {
    fn clone(&self) -> Self {
        // Create a new cache with the same configuration
        // Note: This doesn't clone the cached data
        Self::with_config(self.config.clone())
    }
}