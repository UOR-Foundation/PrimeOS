//! Main COC engine

use crate::{
    CocConfig, CocError, Result,
    CoherentObject, DecompositionStrategy, ConservationLaw,
};
use ccm::{StandardCCM, CliffordElement};
use ccm_core::Float;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::{boxed::Box, vec::Vec};
#[cfg(feature = "std")]
use std::{boxed::Box, vec::Vec};

/// Main COC engine
pub struct COC<P: Float> {
    ccm: StandardCCM<P>,
    strategies: Vec<Box<dyn DecompositionStrategy<P>>>,
    conservation_laws: Vec<Box<dyn ConservationLaw<P>>>,
    config: CocConfig,
}

impl<P: Float + num_traits::FromPrimitive> COC<P> {
    /// Create a new COC instance
    pub fn new(dimension: usize) -> Result<Self> {
        let config = CocConfig::default();
        config.validate().map_err(|e| CocError::InvalidConfig(e.into()))?;
        
        let ccm = StandardCCM::new(dimension)?;
        
        Ok(Self {
            ccm,
            strategies: Vec::new(),
            conservation_laws: Vec::new(),
            config,
        })
    }
    
    /// Create with existing CCM instance
    pub fn with_ccm(ccm: StandardCCM<P>) -> Result<Self> {
        let config = CocConfig::default();
        config.validate().map_err(|e| CocError::InvalidConfig(e.into()))?;
        
        Ok(Self {
            ccm,
            strategies: Vec::new(),
            conservation_laws: Vec::new(),
            config,
        })
    }
    
    /// Add a decomposition strategy
    pub fn add_strategy(&mut self, strategy: Box<dyn DecompositionStrategy<P>>) {
        self.strategies.push(strategy);
    }
    
    /// Add a conservation law
    pub fn add_conservation_law(&mut self, law: Box<dyn ConservationLaw<P>>) {
        self.conservation_laws.push(law);
    }
    
    /// Get reference to the CCM instance
    pub fn ccm(&self) -> &StandardCCM<P> {
        &self.ccm
    }
    
    /// Get reference to the configuration
    pub fn config(&self) -> &CocConfig {
        &self.config
    }
    
    /// Set a new configuration
    pub fn set_config(&mut self, config: CocConfig) -> Result<()> {
        config.validate().map_err(|e| CocError::InvalidConfig(e.into()))?;
        self.config = config;
        Ok(())
    }
    
    /// Get the conservation laws
    pub fn conservation_laws(&self) -> &[Box<dyn ConservationLaw<P>>] {
        &self.conservation_laws
    }
    
    /// Sort strategies by priority (higher priority first)
    pub fn sort_strategies_by_priority(&mut self) {
        self.strategies.sort_by(|a, b| {
            b.priority().cmp(&a.priority())
        });
    }
}