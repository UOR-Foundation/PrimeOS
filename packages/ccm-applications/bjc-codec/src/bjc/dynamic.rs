//! Dynamic BJC codec that calculates alpha values based on input size
//!
//! This module provides encode/decode functions that generate alpha values
//! as a pure function of the input bit length, eliminating the need for
//! pre-defined constants.

use super::{decode_bjc, encode_bjc, BjcPacket, FloatEncoding};
use ccm_core::{BitWord, CcmError, Float};
use ccm_embedding::AlphaVec;

/// Encode using dynamically generated alpha values
pub fn encode_bjc_dynamic<P: Float + FloatEncoding + num_traits::FromPrimitive>(
    raw: &BitWord,
    k: usize,
    include_hash: bool,
) -> Result<BjcPacket, CcmError> {
    // Generate alpha values based on input bit length
    let n = raw.len();
    let alpha = AlphaVec::<P>::for_bit_length(n)?;

    // Use standard encode with generated alphas
    encode_bjc(raw, &alpha, k, include_hash)
}

/// Decode using dynamically generated alpha values
pub fn decode_bjc_dynamic<P: Float + FloatEncoding + num_traits::FromPrimitive>(
    packet: &BjcPacket,
) -> Result<BitWord, CcmError> {
    // Extract bit length from packet header
    let n = (packet.n_bits & 0x7F) as usize;

    // Generate the same alpha values that were used for encoding
    let alpha = AlphaVec::<P>::for_bit_length(n)?;

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

    pub fn encode(
        &self,
        raw: &BitWord,
        k: usize,
        include_hash: bool,
    ) -> Result<BjcPacket, CcmError> {
        let n = raw.len();
        let alpha = self.get_alpha(n)?;
        encode_bjc(raw, &alpha, k, include_hash)
    }

    pub fn decode(&self, packet: &BjcPacket) -> Result<BitWord, CcmError> {
        let n = (packet.n_bits & 0x7F) as usize;
        let alpha = self.get_alpha(n)?;
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
            println!("Testing N={}", n);
            test_roundtrip_n(n);
        }
    }

    fn test_roundtrip_n(n: usize) {
        let input = BitWord::from_u64(42u64, n);

        // Test direct dynamic functions
        let packet = encode_bjc_dynamic::<f64>(&input, 1, false).expect("Dynamic encode failed");
        let decoded = decode_bjc_dynamic::<f64>(&packet).expect("Dynamic decode failed");

        assert_eq!(input.to_usize(), decoded.to_usize());
        assert_eq!(input.len(), decoded.len());

        // Test with codec struct
        let codec = DynamicBjcCodec::<f64>::new(DynamicCodecConfig::default());
        let packet2 = codec.encode(&input, 1, false).expect("Codec encode failed");
        let decoded2 = codec.decode(&packet2).expect("Codec decode failed");

        assert_eq!(input.to_usize(), decoded2.to_usize());
        assert_eq!(input.len(), decoded2.len());
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
            let input = BitWord::from_u8(123);

            let packet = codec.encode(&input, 1, false).unwrap();
            let decoded = codec.decode(&packet).unwrap();

            assert_eq!(
                input.to_usize(),
                decoded.to_usize(),
                "Failed with config {:?}",
                config
            );
            assert_eq!(
                input.len(),
                decoded.len(),
                "Failed with config {:?}",
                config
            );
        }
    }
}
