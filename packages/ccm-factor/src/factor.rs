//! Core CCMFactor implementation

use crate::{
    alignment::find_alignment_windows,
    cache::{FactorCache, CacheConfig},
    error::{FactorError, Result},
    recovery::recover_factors_from_windows,
    types::FactorConfig,
    verification::verify_factorization,
};

use ccm::{CCMCore, StandardCCM};
use ccm_coherence::CliffordElement;
use ccm_core::BitWord;
use ccm_embedding::AlphaVec;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{Float, One, Zero};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Main factorization engine using CCM
pub struct CCMFactor<P: Float + num_traits::FromPrimitive + std::iter::Sum> {
    /// CCM instance
    ccm: StandardCCM<P>,

    /// Configuration
    config: FactorConfig,

    /// Cached alpha values for different channel sizes
    alpha_cache: Vec<(usize, AlphaVec<P>)>,
    
    /// Multi-level cache for performance
    cache: FactorCache<P>,
}

impl<P: Float + num_traits::FromPrimitive + std::iter::Sum> CCMFactor<P> {
    /// Create a new CCMFactor instance with default configuration
    pub fn new() -> Result<Self> {
        Self::with_config(FactorConfig::default())
    }

    /// Create a new CCMFactor instance with custom configuration
    pub fn with_config(config: FactorConfig) -> Result<Self> {
        let ccm = StandardCCM::new(config.channel_size)?;

        Ok(Self {
            ccm,
            config,
            alpha_cache: Vec::new(),
            cache: FactorCache::new(),
        })
    }
    
    /// Create with custom cache configuration
    pub fn with_cache_config(config: FactorConfig, cache_config: CacheConfig) -> Result<Self> {
        let ccm = StandardCCM::new(config.channel_size)?;

        Ok(Self {
            ccm,
            config,
            alpha_cache: Vec::new(),
            cache: FactorCache::with_config(cache_config),
        })
    }

    /// Factor a BigUint into its prime factors
    pub fn factor(&mut self, n: &BigUint) -> Result<Vec<BigUint>> {
        // Handle trivial cases
        if n.is_zero() {
            return Err(FactorError::InvalidInput("Cannot factor zero".into()));
        }
        if n.is_one() {
            return Ok(vec![]);
        }

        // Check if it's prime first (optimization)
        if self.is_probably_prime(n) {
            return Ok(vec![n.clone()]);
        }

        // Convert to channels and find factors
        let channel_size = self.determine_channel_size(n);
        let channels = self.embed_integer_to_channels(n, channel_size)?;

        // Find alignment windows
        let windows = find_alignment_windows(
            &self.ccm,
            &channels,
            self.config.max_window_size,
            self.config.min_confidence,
        )?;

        if windows.is_empty() {
            return Err(FactorError::NoAlignmentFound);
        }

        // Recover factors from windows
        let alpha = self.get_or_create_alpha(channel_size)?;
        let factors = recover_factors_from_windows(
            &self.ccm,
            &windows,
            n,
            &alpha,
            self.config.resonance_tolerance,
        )?;

        // Verify the factorization
        verify_factorization(n, &factors, &self.ccm, &alpha)?;

        Ok(factors)
    }

    /// Embed an integer into CCM channel sections
    pub fn embed_integer_to_channels(
        &mut self,
        n: &BigUint,
        channel_size: usize,
    ) -> Result<Vec<CliffordElement<P>>> {
        let bytes = n.to_bytes_be();
        let mut channels = Vec::new();
        let bytes_per_channel = channel_size / 8;

        // Pad to multiple of channel size
        let padded_len =
            ((bytes.len() + bytes_per_channel - 1) / bytes_per_channel) * bytes_per_channel;
        let mut padded_bytes = vec![0u8; padded_len - bytes.len()];
        padded_bytes.extend_from_slice(&bytes);

        // Get alpha for this channel size
        let alpha = self.get_or_create_alpha(channel_size)?;

        // Process each channel
        for chunk in padded_bytes.chunks(bytes_per_channel) {
            let bitword = BitWord::from_bytes(chunk);

            // Find Klein minimum within the resonance class using cache
            let klein_members = self.cache.get_or_compute_klein_members(&bitword)?;
            
            // Find the member with minimal resonance using cached values
            let mut minimal = bitword.clone();
            let mut min_resonance = self.cache.get_or_compute_resonance(&bitword, &alpha)?;
            
            for member in klein_members {
                let resonance = self.cache.get_or_compute_resonance(&member, &alpha)?;
                if resonance < min_resonance {
                    minimal = member;
                    min_resonance = resonance;
                }
            }

            // Embed the Klein minimum into CCM section
            let section = self.ccm.embed(&minimal, &alpha)?;
            channels.push(section);
        }

        Ok(channels)
    }

    /// Determine optimal channel size for given integer
    fn determine_channel_size(&self, n: &BigUint) -> usize {
        if !self.config.adaptive_channels {
            return self.config.channel_size;
        }

        let bits = n.bits() as usize;
        match bits {
            0..=128 => 8,
            129..=512 => 16,
            513..=2048 => 32,
            2049..=8192 => 64,
            _ => 128,
        }
    }

    /// Get or create alpha values for a given channel size
    fn get_or_create_alpha(&mut self, channel_size: usize) -> Result<AlphaVec<P>> {
        // Check cache first
        for (size, alpha) in &self.alpha_cache {
            if *size == channel_size {
                return Ok(alpha.clone());
            }
        }

        // Generate new alpha values
        let alpha = AlphaVec::for_bit_length(channel_size)
            .map_err(|_| FactorError::CCMError(ccm_core::CcmError::InvalidInput))?;

        // Cache for future use
        self.alpha_cache.push((channel_size, alpha.clone()));

        Ok(alpha)
    }

    /// Miller-Rabin primality test
    pub fn is_probably_prime(&self, n: &BigUint) -> bool {
        // Handle small cases
        if n <= &BigUint::one() {
            return false;
        }
        if n == &BigUint::from(2u32) || n == &BigUint::from(3u32) {
            return true;
        }
        if n.is_even() {
            return false;
        }

        // Write n-1 = 2^r * d where d is odd
        let n_minus_1 = n - BigUint::one();
        let (r, d) = factor_out_powers_of_two(&n_minus_1);

        // Choose witnesses based on the size of n
        let witnesses = select_miller_rabin_witnesses(n);

        // Test with each witness
        for a in witnesses {
            if !miller_rabin_witness_test(&a, &d, r, n) {
                return false;
            }
        }

        true
    }
    
    /// Clear all caches
    pub fn clear_cache(&self) -> Result<()> {
        self.cache.clear()
    }
    
    /// Get cache statistics
    #[cfg(feature = "std")]
    pub fn cache_stats(&self) -> Result<crate::cache::CacheStats> {
        self.cache.stats()
    }
}

/// Factor out powers of 2 from n, returning (r, d) where n = 2^r * d and d is odd
fn factor_out_powers_of_two(n: &BigUint) -> (u32, BigUint) {
    let mut r = 0;
    let mut d = n.clone();
    
    while d.is_even() {
        d >>= 1;
        r += 1;
    }
    
    (r, d)
}

/// Select appropriate witnesses for Miller-Rabin test based on n's size
fn select_miller_rabin_witnesses(n: &BigUint) -> Vec<BigUint> {
    // For small n, use deterministic witnesses
    if n < &BigUint::from(2047u32) {
        vec![BigUint::from(2u32)]
    } else if n < &BigUint::from(1_373_653u32) {
        vec![BigUint::from(2u32), BigUint::from(3u32)]
    } else if n < &BigUint::from(9_080_191u32) {
        vec![BigUint::from(31u32), BigUint::from(73u32)]
    } else if n < &BigUint::from(25_326_001u32) {
        vec![BigUint::from(2u32), BigUint::from(3u32), BigUint::from(5u32)]
    } else if n < &BigUint::from(3_215_031_751u64) {
        vec![
            BigUint::from(2u32),
            BigUint::from(3u32),
            BigUint::from(5u32),
            BigUint::from(7u32),
        ]
    } else {
        // For larger n, use the first k primes where k gives good probability
        vec![
            BigUint::from(2u32),
            BigUint::from(3u32),
            BigUint::from(5u32),
            BigUint::from(7u32),
            BigUint::from(11u32),
            BigUint::from(13u32),
            BigUint::from(17u32),
            BigUint::from(19u32),
            BigUint::from(23u32),
            BigUint::from(29u32),
            BigUint::from(31u32),
            BigUint::from(37u32),
        ]
    }
}

/// Perform Miller-Rabin witness test
fn miller_rabin_witness_test(a: &BigUint, d: &BigUint, r: u32, n: &BigUint) -> bool {
    // Compute a^d mod n
    let mut x = a.modpow(d, n);
    
    if x == BigUint::one() || x == n - BigUint::one() {
        return true;
    }
    
    // Square x repeatedly r-1 times
    for _ in 0..r - 1 {
        x = (&x * &x) % n;
        
        if x == n - BigUint::one() {
            return true;
        }
        
        if x == BigUint::one() {
            return false;
        }
    }
    
    false
}

/// Parallel version of CCMFactor (when parallel feature is enabled)
#[cfg(feature = "parallel")]
pub struct ParallelCCMFactor<P: Float + num_traits::FromPrimitive + std::iter::Sum + Send + Sync> {
    inner: CCMFactor<P>,
}

#[cfg(feature = "parallel")]
impl<P: Float + num_traits::FromPrimitive + std::iter::Sum + Send + Sync> ParallelCCMFactor<P> {
    /// Create a new parallel factorization engine
    pub fn new() -> Result<Self> {
        Ok(Self {
            inner: CCMFactor::new()?,
        })
    }
    
    /// Create with custom cache configuration
    pub fn with_cache_config(config: FactorConfig, cache_config: CacheConfig) -> Result<Self> {
        Ok(Self {
            inner: CCMFactor::with_cache_config(config, cache_config)?,
        })
    }

    /// Factor using parallel window search
    pub fn factor(&mut self, n: &BigUint) -> Result<Vec<BigUint>> {
        use crate::alignment::find_alignment_windows_parallel;
        
        // Handle trivial cases
        if n.is_zero() {
            return Err(FactorError::InvalidInput("Cannot factor zero".into()));
        }
        if n.is_one() {
            return Ok(vec![]);
        }

        // Check if it's prime first
        if self.inner.is_probably_prime(n) {
            return Ok(vec![n.clone()]);
        }

        // Convert to channels and find factors using parallel search
        let channel_size = self.inner.determine_channel_size(n);
        let channels = self.inner.embed_integer_to_channels(n, channel_size)?;

        // Find alignment windows in parallel
        let windows = find_alignment_windows_parallel(
            &self.inner.ccm,
            &channels,
            self.inner.config.max_window_size,
            self.inner.config.min_confidence,
        )?;

        if windows.is_empty() {
            return Err(FactorError::NoAlignmentFound);
        }

        // Recover factors from windows
        let alpha = self.inner.get_or_create_alpha(channel_size)?;
        let factors = recover_factors_from_windows(
            &self.inner.ccm,
            &windows,
            n,
            &alpha,
            self.inner.config.resonance_tolerance,
        )?;

        // Verify the factorization
        verify_factorization(n, &factors, &self.inner.ccm, &alpha)?;

        Ok(factors)
    }
}
