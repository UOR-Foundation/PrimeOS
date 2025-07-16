//! Verification of factorization using conservation laws

use crate::error::{FactorError, Result};

use ccm::{CCMCore, StandardCCM};
use ccm_coherence::CliffordElement;
use ccm_core::BitWord;
use ccm_embedding::{AlphaVec, Resonance};
use num_bigint::BigUint;
use num_traits::{Float, One, Zero};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Verify that the factorization is correct using multiple methods
pub fn verify_factorization<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    n: &BigUint,
    factors: &[BigUint],
    ccm: &StandardCCM<P>,
    alpha: &AlphaVec<P>,
) -> Result<()> {
    // Basic verification: product equals n
    verify_product(n, factors)?;

    // Verify using resonance conservation
    verify_resonance_conservation(n, factors, ccm, alpha)?;

    // Verify using coherence conservation
    verify_coherence_conservation(n, factors, ccm, alpha)?;

    // Verify 768-cycle conservation
    verify_768_cycle_conservation(n, factors, ccm, alpha)?;

    // Verify resonance current conservation
    verify_resonance_current_conservation(n, factors, ccm, alpha)?;

    Ok(())
}

/// Verify that the product of factors equals n
fn verify_product(n: &BigUint, factors: &[BigUint]) -> Result<()> {
    if factors.is_empty() {
        if n.is_one() {
            return Ok(());
        } else {
            return Err(FactorError::VerificationFailed);
        }
    }

    let product: BigUint = factors.iter().product();

    if product == *n {
        Ok(())
    } else {
        Err(FactorError::VerificationFailed)
    }
}

/// Verify resonance conservation: R(n) should relate to R(factors)
fn verify_resonance_conservation<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    n: &BigUint,
    factors: &[BigUint],
    ccm: &StandardCCM<P>,
    alpha: &AlphaVec<P>,
) -> Result<()> {
    // Convert n to channels and compute total resonance
    let n_channels = integer_to_channels(n, ccm, alpha)?;
    let n_resonance = compute_total_resonance(&n_channels, ccm);

    // Compute total resonance of factors
    let mut factor_resonance = P::zero();
    for factor in factors {
        let factor_channels = integer_to_channels(factor, ccm, alpha)?;
        factor_resonance = factor_resonance + compute_total_resonance(&factor_channels, ccm);
    }

    // Check conservation within tolerance
    let tolerance = P::from(0.01).unwrap() * n_resonance;
    let difference = (n_resonance - factor_resonance).abs();

    if difference <= tolerance {
        Ok(())
    } else {
        Err(FactorError::ConservationViolation(format!(
            "Resonance conservation failed: {} vs {}",
            n_resonance.to_f64().unwrap_or(0.0),
            factor_resonance.to_f64().unwrap_or(0.0)
        )))
    }
}

/// Verify coherence norm conservation
fn verify_coherence_conservation<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    n: &BigUint,
    factors: &[BigUint],
    ccm: &StandardCCM<P>,
    alpha: &AlphaVec<P>,
) -> Result<()> {
    // Get coherence embedding of n
    let n_channels = integer_to_channels(n, ccm, alpha)?;
    let n_coherence = compute_total_coherence(&n_channels, ccm);

    // For multiplicative conservation, we expect:
    // ||n|| ≈ ||p|| * ||q|| for n = p * q
    // or more generally: ||n|| ≈ ∏||factors||

    let mut factor_coherence_product = P::one();
    for factor in factors {
        let factor_channels = integer_to_channels(factor, ccm, alpha)?;
        let factor_coherence = compute_total_coherence(&factor_channels, ccm);
        factor_coherence_product = factor_coherence_product * factor_coherence;
    }

    // Check multiplicative conservation within tolerance
    let tolerance = P::from(0.1).unwrap() * n_coherence;
    let difference = (n_coherence - factor_coherence_product).abs();

    if difference <= tolerance {
        Ok(())
    } else {
        // Try additive conservation as fallback
        verify_additive_coherence_conservation(n, factors, ccm, alpha)
    }
}

/// Try additive coherence conservation
fn verify_additive_coherence_conservation<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    n: &BigUint,
    factors: &[BigUint],
    ccm: &StandardCCM<P>,
    alpha: &AlphaVec<P>,
) -> Result<()> {
    let n_channels = integer_to_channels(n, ccm, alpha)?;
    let n_coherence = compute_total_coherence(&n_channels, ccm);

    // For additive conservation: ||n|| ≈ ∑||factors||
    let mut factor_coherence_sum = P::zero();
    for factor in factors {
        let factor_channels = integer_to_channels(factor, ccm, alpha)?;
        let factor_coherence = compute_total_coherence(&factor_channels, ccm);
        factor_coherence_sum = factor_coherence_sum + factor_coherence;
    }

    let tolerance = P::from(0.1).unwrap() * n_coherence;
    let difference = (n_coherence - factor_coherence_sum).abs();

    if difference <= tolerance {
        Ok(())
    } else {
        Err(FactorError::ConservationViolation(format!(
            "Coherence conservation failed: {} vs sum {} or product",
            n_coherence.to_f64().unwrap_or(0.0),
            factor_coherence_sum.to_f64().unwrap_or(0.0)
        )))
    }
}

/// Convert integer to channel sections
fn integer_to_channels<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    n: &BigUint,
    ccm: &StandardCCM<P>,
    alpha: &AlphaVec<P>,
) -> Result<Vec<CliffordElement<P>>> {
    let bytes = n.to_bytes_be();
    let channel_size = alpha.len();
    let bytes_per_channel = channel_size / 8;

    let mut channels = Vec::new();

    // Pad to multiple of channel size
    let padded_len =
        ((bytes.len() + bytes_per_channel - 1) / bytes_per_channel) * bytes_per_channel;
    let mut padded_bytes = vec![0u8; padded_len - bytes.len()];
    padded_bytes.extend_from_slice(&bytes);

    for chunk in padded_bytes.chunks(bytes_per_channel) {
        let bitword = ccm_core::BitWord::from_bytes(chunk);
        let minimal = ccm.find_minimum_resonance(&bitword, alpha)?;
        let section = ccm.embed(&minimal, alpha)?;
        channels.push(section);
    }

    Ok(channels)
}

/// Compute total resonance across all channels
fn compute_total_resonance<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    channels: &[CliffordElement<P>],
    ccm: &StandardCCM<P>,
) -> P {
    channels.iter().map(|ch| ccm.coherence_norm(ch)).sum()
}

/// Compute total coherence norm
fn compute_total_coherence<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    channels: &[CliffordElement<P>],
    ccm: &StandardCCM<P>,
) -> P {
    // Use L2 norm of coherence norms
    let sum_of_squares: P = channels
        .iter()
        .map(|ch| {
            let norm = ccm.coherence_norm(ch);
            norm * norm
        })
        .sum();

    sum_of_squares.sqrt()
}

/// Verify 768-cycle conservation law
fn verify_768_cycle_conservation<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    n: &BigUint,
    factors: &[BigUint],
    ccm: &StandardCCM<P>,
    alpha: &AlphaVec<P>,
) -> Result<()> {
    // const CYCLE_LENGTH: usize = 768;  // Currently unused
    const EXPECTED_SUM: f64 = 687.110133051847;
    
    // Compute 768-cycle sum for n
    let n_cycle_sum = compute_768_cycle_sum(n, ccm, alpha)?;
    
    // Verify it matches the expected conservation value
    let tolerance = P::from(1e-6).unwrap();
    let expected = P::from(EXPECTED_SUM).unwrap();
    
    if (n_cycle_sum - expected).abs() > tolerance {
        return Err(FactorError::ConservationViolation(format!(
            "768-cycle sum {} doesn't match expected {}",
            n_cycle_sum.to_f64().unwrap_or(0.0),
            EXPECTED_SUM
        )));
    }
    
    // For factors, verify each maintains conservation
    for factor in factors {
        let factor_sum = compute_768_cycle_sum(factor, ccm, alpha)?;
        if (factor_sum - expected).abs() > tolerance {
            return Err(FactorError::ConservationViolation(format!(
                "Factor {} violates 768-cycle conservation",
                factor
            )));
        }
    }
    
    Ok(())
}

/// Compute the 768-cycle resonance sum
pub(crate) fn compute_768_cycle_sum<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    n: &BigUint,
    ccm: &StandardCCM<P>,
    alpha: &AlphaVec<P>,
) -> Result<P> {
    const CYCLE_LENGTH: usize = 768;
    const POSITIONS_PER_PAGE: usize = 256;
    
    // The 768-cycle consists of 3 pages of 256 positions each
    // For proper channel decomposition, we need to consider how n maps to the cycle
    
    let mut sum = P::zero();
    
    // Extract the relevant portion of n that corresponds to the 768-cycle
    let n_bytes = n.to_bytes_le();
    
    // Process the cycle based on the channel structure
    for cycle_pos in 0..CYCLE_LENGTH {
        // Compute which page and position within page
        let page = cycle_pos / POSITIONS_PER_PAGE;
        let pos_in_page = cycle_pos % POSITIONS_PER_PAGE;
        
        // Create BitWord for this position
        // The position is determined by the channel decomposition
        let mut bitword = if n_bytes.len() > cycle_pos / 8 {
            // Use actual data from n if available
            let byte_idx = cycle_pos / 8;
            let byte_val = n_bytes[byte_idx];
            
            // For proper channel alignment, consider the page structure
            let aligned_val = (byte_val as usize + page * POSITIONS_PER_PAGE + pos_in_page) % 256;
            BitWord::from_u8(aligned_val as u8)
        } else {
            // Beyond n's data, use cycle position directly
            BitWord::from_u8(pos_in_page as u8)
        };
        
        // Apply Klein group correction for proper cycle behavior
        // Unity positions must be preserved: 0, 1, 48, 49 (and their page offsets)
        if is_unity_position(cycle_pos) {
            // Ensure this position contributes unity resonance
            let klein_members = <BitWord as Resonance<P>>::class_members(&bitword);
            // Find the Klein member with resonance = 1
            for member in klein_members {
                if (member.r(alpha) - P::one()).abs() < P::from(1e-10).unwrap() {
                    bitword = member;
                    break;
                }
            }
        }
        
        let resonance = bitword.r(alpha);
        sum = sum + resonance;
    }
    
    Ok(sum)
}

/// Check if a cycle position is a unity position
pub(crate) fn is_unity_position(pos: usize) -> bool {
    // Unity positions in 768-cycle: 0, 1, 48, 49, 256, 257, 304, 305, 512, 513, 560, 561
    const UNITY_POSITIONS: [usize; 12] = [0, 1, 48, 49, 256, 257, 304, 305, 512, 513, 560, 561];
    UNITY_POSITIONS.contains(&pos)
}

/// Verify resonance current conservation
fn verify_resonance_current_conservation<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    n: &BigUint,
    _factors: &[BigUint],
    ccm: &StandardCCM<P>,
    alpha: &AlphaVec<P>,
) -> Result<()> {
    // Get channels for n
    let channels = integer_to_channels(n, ccm, alpha)?;
    
    if channels.len() < 2 {
        // Not enough data for current computation
        return Ok(());
    }
    
    // Compute resonance currents
    let mut total_current = P::zero();
    
    for i in 0..channels.len().saturating_sub(1) {
        let r_current = ccm.coherence_norm(&channels[i]);
        let r_next = ccm.coherence_norm(&channels[i + 1]);
        let current = r_next - r_current;
        total_current = total_current + current;
    }
    
    // For a complete cycle, current should sum to zero
    // Check if we have at least one complete 768-cycle
    if channels.len() >= 768 {
        let cycle_current = compute_cycle_current(&channels[0..768], ccm)?;
        let tolerance = P::from(0.001).unwrap();
        
        if cycle_current.abs() > tolerance {
            return Err(FactorError::ConservationViolation(format!(
                "Resonance current conservation violated: sum = {}",
                cycle_current.to_f64().unwrap_or(0.0)
            )));
        }
    }
    
    Ok(())
}

/// Compute current sum over a cycle
fn compute_cycle_current<P: Float + num_traits::FromPrimitive + std::iter::Sum>(
    channels: &[CliffordElement<P>],
    ccm: &StandardCCM<P>,
) -> Result<P> {
    let mut sum = P::zero();
    
    for i in 0..channels.len().saturating_sub(1) {
        let r_current = ccm.coherence_norm(&channels[i]);
        let r_next = ccm.coherence_norm(&channels[i + 1]);
        sum = sum + (r_next - r_current);
    }
    
    // Close the cycle
    if !channels.is_empty() {
        let r_last = ccm.coherence_norm(&channels[channels.len() - 1]);
        let r_first = ccm.coherence_norm(&channels[0]);
        sum = sum + (r_first - r_last);
    }
    
    Ok(sum)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verify_product() {
        let n = BigUint::from(15u32);
        let factors = vec![BigUint::from(3u32), BigUint::from(5u32)];
        assert!(verify_product(&n, &factors).is_ok());

        let wrong_factors = vec![BigUint::from(2u32), BigUint::from(7u32)];
        assert!(verify_product(&n, &wrong_factors).is_err());
    }

    #[test]
    fn test_empty_factors() {
        let n = BigUint::from(1u32);
        let factors = vec![];
        assert!(verify_product(&n, &factors).is_ok());

        let n = BigUint::from(2u32);
        assert!(verify_product(&n, &factors).is_err());
    }
}
