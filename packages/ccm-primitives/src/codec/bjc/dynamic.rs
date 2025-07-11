//! Dynamic BJC codec that calculates alpha values based on input size
//!
//! This module provides encode/decode functions that generate alpha values
//! as a pure function of the input bit length, eliminating the need for
//! pre-defined constants.

use crate::{AlphaVec, BitWord, CcmError, Float};
use super::{BjcPacket, encode_bjc, decode_bjc, FloatEncoding};

/// Encode using dynamically generated alpha values
pub fn encode_bjc_dynamic<P: Float + FloatEncoding + num_traits::FromPrimitive, const N: usize>(
    raw: &BitWord<N>,
    k: usize,
    include_hash: bool,
) -> Result<BjcPacket, CcmError> {
    // Generate alpha values based on input bit length
    let alpha = AlphaVec::<P>::for_bit_length(N)?;
    
    // Use standard encode with generated alphas
    encode_bjc(raw, &alpha, k, include_hash)
}

/// Decode using dynamically generated alpha values
pub fn decode_bjc_dynamic<P: Float + FloatEncoding + num_traits::FromPrimitive, const N: usize>(
    packet: &BjcPacket,
) -> Result<BitWord<N>, CcmError> {
    // Extract bit length from packet header
    let packet_n = packet.n_bits & 0x7F;
    if packet_n as usize != N {
        return Err(CcmError::InvalidLength);
    }
    
    // Generate the same alpha values that were used for encoding
    let alpha = AlphaVec::<P>::for_bit_length(N)?;
    
    // Use standard decode with generated alphas
    decode_bjc(packet, &alpha)
}

/// Configuration for dynamic codec behavior
#[derive(Debug, Clone, Copy)]
pub struct DynamicCodecConfig {
    /// Strategy for alpha generation
    pub strategy: AlphaStrategy,
    /// Whether to use caching for repeated operations
    pub cache_alphas: bool,
}

#[derive(Debug, Clone, Copy)]
pub enum AlphaStrategy {
    /// Pure calculation based on bit length
    Calculated,
    /// Mathematical constants scaled by bit length
    Mathematical,
    /// Hybrid approach
    Hybrid,
}

impl Default for DynamicCodecConfig {
    fn default() -> Self {
        Self {
            strategy: AlphaStrategy::Calculated,
            cache_alphas: true,
        }
    }
}

/// BJC codec with configurable dynamic behavior
pub struct DynamicBjcCodec<P: Float> {
    config: DynamicCodecConfig,
    // Optional cache for frequently used alpha values
    #[cfg(feature = "std")]
    cache: std::sync::Mutex<std::collections::HashMap<usize, AlphaVec<P>>>,
}

impl<P: Float + FloatEncoding + num_traits::FromPrimitive> DynamicBjcCodec<P> {
    pub fn new(config: DynamicCodecConfig) -> Self {
        Self {
            config,
            #[cfg(feature = "std")]
            cache: std::sync::Mutex::new(std::collections::HashMap::new()),
        }
    }
    
    /// Get or generate alpha values for given bit length
    fn get_alpha(&self, bit_length: usize) -> Result<AlphaVec<P>, CcmError> {
        #[cfg(feature = "std")]
        if self.config.cache_alphas {
            let cache = self.cache.lock().unwrap();
            if let Some(alpha) = cache.get(&bit_length) {
                return Ok(alpha.clone());
            }
        }
        
        let alpha = match self.config.strategy {
            AlphaStrategy::Calculated => AlphaVec::for_bit_length(bit_length)?,
            AlphaStrategy::Mathematical => AlphaVec::mathematical(bit_length)?,
            AlphaStrategy::Hybrid => {
                // Use mathematical for common sizes, calculated for others
                match bit_length {
                    8 | 16 | 32 | 64 => AlphaVec::mathematical(bit_length)?,
                    _ => AlphaVec::for_bit_length(bit_length)?,
                }
            }
        };
        
        #[cfg(feature = "std")]
        if self.config.cache_alphas {
            let mut cache = self.cache.lock().unwrap();
            cache.insert(bit_length, alpha.clone());
        }
        
        Ok(alpha)
    }
    
    pub fn encode<const N: usize>(
        &self,
        raw: &BitWord<N>,
        k: usize,
        include_hash: bool,
    ) -> Result<BjcPacket, CcmError> {
        let alpha = self.get_alpha(N)?;
        encode_bjc(raw, &alpha, k, include_hash)
    }
    
    pub fn decode<const N: usize>(
        &self,
        packet: &BjcPacket,
    ) -> Result<BitWord<N>, CcmError> {
        let alpha = self.get_alpha(N)?;
        decode_bjc(packet, &alpha)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_dynamic_roundtrip() {
        // Test with different bit lengths
        for n in [8, 16, 32] {
            match n {
                8 => test_roundtrip_n::<8>(),
                16 => test_roundtrip_n::<16>(),
                32 => test_roundtrip_n::<32>(),
                _ => unreachable!(),
            }
        }
    }
    
    fn test_roundtrip_n<const N: usize>() {
        let input = BitWord::<N>::from(42u64);
        
        // Test direct dynamic functions
        let packet = encode_bjc_dynamic::<f64, N>(&input, 1, false)
            .expect("Dynamic encode failed");
        let decoded = decode_bjc_dynamic::<f64, N>(&packet)
            .expect("Dynamic decode failed");
        
        assert_eq!(input, decoded);
        
        // Test with codec struct
        let codec = DynamicBjcCodec::<f64>::new(DynamicCodecConfig::default());
        let packet2 = codec.encode(&input, 1, false).expect("Codec encode failed");
        let decoded2 = codec.decode::<N>(&packet2).expect("Codec decode failed");
        
        assert_eq!(input, decoded2);
    }
    
    #[test]
    fn test_different_strategies() {
        let configs = [
            DynamicCodecConfig {
                strategy: AlphaStrategy::Calculated,
                cache_alphas: false,
            },
            DynamicCodecConfig {
                strategy: AlphaStrategy::Mathematical,
                cache_alphas: false,
            },
            DynamicCodecConfig {
                strategy: AlphaStrategy::Hybrid,
                cache_alphas: true,
            },
        ];
        
        for config in configs {
            let codec = DynamicBjcCodec::<f64>::new(config);
            let input = BitWord::<8>::from(123u8);
            
            let packet = codec.encode(&input, 1, false).unwrap();
            let decoded = codec.decode::<8>(&packet).unwrap();
            
            assert_eq!(input, decoded, "Failed with config {:?}", config);
        }
    }
}