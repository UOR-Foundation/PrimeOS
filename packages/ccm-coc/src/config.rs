//! Configuration for the COC framework

use ccm::cache::CacheConfig;

#[cfg(feature = "std")]
use std::time::Duration;

/// Configuration for the COC framework
#[derive(Clone, Debug)]
pub struct CocConfig {
    /// Default boundary detection confidence threshold
    pub boundary_confidence_threshold: f64,
    
    /// Maximum window size to consider
    pub max_window_size: usize,
    
    /// Minimum window size
    pub min_window_size: usize,
    
    /// Conservation law tolerance
    pub conservation_tolerance: f64,
    
    /// Enable parallel decomposition
    pub parallel: bool,
    
    /// Timeout for decomposition attempts
    #[cfg(feature = "std")]
    pub decomposition_timeout: Option<Duration>,
    
    /// Cache configuration
    pub cache_config: CacheConfig,
    
    /// Maximum recursion depth for decomposition
    pub max_recursion_depth: usize,
    
    /// Minimum confidence score for accepting a decomposition
    pub min_decomposition_confidence: f64,
    
    /// Enable early termination when confidence is high
    pub early_termination: bool,
    
    /// Threshold for early termination
    pub early_termination_threshold: f64,
}

impl Default for CocConfig {
    fn default() -> Self {
        Self {
            boundary_confidence_threshold: 0.5,
            max_window_size: 20,
            min_window_size: 1,
            conservation_tolerance: 1e-6,
            parallel: cfg!(feature = "parallel"),
            #[cfg(feature = "std")]
            decomposition_timeout: Some(Duration::from_secs(60)),
            cache_config: CacheConfig::default(),
            max_recursion_depth: 10,
            min_decomposition_confidence: 0.7,
            early_termination: true,
            early_termination_threshold: 0.95,
        }
    }
}

impl CocConfig {
    /// Create a new configuration with all defaults
    pub fn new() -> Self {
        Self::default()
    }
    
    /// Set the boundary confidence threshold
    pub fn with_boundary_threshold(mut self, threshold: f64) -> Self {
        self.boundary_confidence_threshold = threshold;
        self
    }
    
    /// Set the window size range
    pub fn with_window_sizes(mut self, min: usize, max: usize) -> Self {
        self.min_window_size = min;
        self.max_window_size = max;
        self
    }
    
    /// Set the conservation law tolerance
    pub fn with_conservation_tolerance(mut self, tolerance: f64) -> Self {
        self.conservation_tolerance = tolerance;
        self
    }
    
    /// Enable or disable parallel processing
    pub fn with_parallel(mut self, parallel: bool) -> Self {
        self.parallel = parallel;
        self
    }
    
    /// Set the decomposition timeout
    #[cfg(feature = "std")]
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.decomposition_timeout = Some(timeout);
        self
    }
    
    /// Disable timeout
    #[cfg(feature = "std")]
    pub fn no_timeout(mut self) -> Self {
        self.decomposition_timeout = None;
        self
    }
    
    /// Set the cache configuration
    pub fn with_cache_config(mut self, cache_config: CacheConfig) -> Self {
        self.cache_config = cache_config;
        self
    }
    
    /// Set the maximum recursion depth
    pub fn with_max_recursion(mut self, depth: usize) -> Self {
        self.max_recursion_depth = depth;
        self
    }
    
    /// Validate the configuration
    pub fn validate(&self) -> Result<(), &'static str> {
        if self.boundary_confidence_threshold < 0.0 || self.boundary_confidence_threshold > 1.0 {
            return Err("Boundary confidence threshold must be between 0 and 1");
        }
        
        if self.min_window_size == 0 {
            return Err("Minimum window size must be at least 1");
        }
        
        if self.min_window_size > self.max_window_size {
            return Err("Minimum window size cannot exceed maximum window size");
        }
        
        if self.conservation_tolerance <= 0.0 {
            return Err("Conservation tolerance must be positive");
        }
        
        if self.max_recursion_depth == 0 {
            return Err("Maximum recursion depth must be at least 1");
        }
        
        if self.min_decomposition_confidence < 0.0 || self.min_decomposition_confidence > 1.0 {
            return Err("Minimum decomposition confidence must be between 0 and 1");
        }
        
        if self.early_termination_threshold < 0.0 || self.early_termination_threshold > 1.0 {
            return Err("Early termination threshold must be between 0 and 1");
        }
        
        Ok(())
    }
}