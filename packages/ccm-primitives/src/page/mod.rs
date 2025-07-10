//! Page symmetry helpers

use crate::bitword::BitWord;

/// Get the page index for a given bit pattern
/// Page = lexicographic position among patterns with same popcount
/// Uses combinatorial ranking algorithm for O(n) complexity
pub fn page_of<const N: usize>(word: BitWord<N>) -> usize {
    let popcount = word.popcount() as usize;
    if popcount == 0 {
        return 0;
    }

    // Combinatorial ranking: count patterns with same popcount that come before this one
    let mut rank = 0;
    let mut remaining_ones = popcount;

    // Process bits from most significant to least significant
    for i in (0..N).rev() {
        if word.bit(i) {
            // This bit is set. Count all patterns with a 0 here
            if remaining_ones > 0 && i >= remaining_ones - 1 {
                rank += binomial(i, remaining_ones - 1);
            }
            remaining_ones -= 1;

            if remaining_ones == 0 {
                break;
            }
        }
    }

    rank
}

/// Inject a page index to create a bit pattern
/// Inverse of page_of - creates the nth pattern with given popcount
/// Uses combinatorial unranking algorithm for O(n) complexity
pub fn inject_page<const N: usize>(page: usize, popcount: usize) -> Option<BitWord<N>> {
    if popcount > N {
        return None;
    }

    if popcount == 0 {
        return Some(BitWord::zero());
    }

    // Check if page is valid
    if page >= binomial(N, popcount) {
        return None;
    }

    // Combinatorial unranking: build the bit pattern from the rank
    let mut result = 0u64;
    let mut remaining_rank = page;
    let mut remaining_ones = popcount;

    // Process positions from most significant to least significant
    for i in (0..N).rev() {
        if remaining_ones == 0 {
            break;
        }

        // Check if we should set this bit
        if i >= remaining_ones - 1 {
            let count_if_zero = binomial(i, remaining_ones - 1);

            if remaining_rank >= count_if_zero {
                // Set this bit to 1
                result |= 1u64 << i;
                remaining_rank -= count_if_zero;
                remaining_ones -= 1;
            }
            // else bit remains 0
        }
    }

    Some(BitWord::from(result))
}

/// Compute binomial coefficient C(n, k)
/// Uses iterative algorithm to avoid overflow
pub fn binomial(n: usize, k: usize) -> usize {
    if k > n {
        return 0;
    }
    if k == 0 || k == n {
        return 1;
    }

    let k = k.min(n - k); // Take advantage of symmetry

    // Use u128 for intermediate calculations to avoid overflow
    let mut result = 1u128;
    let mut divisor = 1u128;

    for i in 0..k {
        result *= (n - i) as u128;
        divisor *= (i + 1) as u128;

        // Keep the fraction reduced to avoid overflow
        let gcd = gcd(result, divisor);
        result /= gcd;
        divisor /= gcd;
    }

    (result / divisor) as usize
}

/// Greatest common divisor using Euclidean algorithm
fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

/// Get the total number of pages for a given popcount
pub fn page_count<const N: usize>(popcount: usize) -> usize {
    binomial(N, popcount)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_page_of() {
        // All patterns with popcount 0 have page 0
        assert_eq!(page_of(BitWord::<8>::from(0b00000000u8)), 0);

        // First pattern with popcount 1
        assert_eq!(page_of(BitWord::<8>::from(0b00000001u8)), 0);

        // Second pattern with popcount 1
        assert_eq!(page_of(BitWord::<8>::from(0b00000010u8)), 1);

        // Third pattern with popcount 1
        assert_eq!(page_of(BitWord::<8>::from(0b00000100u8)), 2);
    }

    #[test]
    fn test_inject_page() {
        // Get the first pattern with popcount 2
        let pattern = inject_page::<8>(0, 2).unwrap();
        assert_eq!(pattern.to_usize(), 0b00000011);
        assert_eq!(pattern.popcount(), 2);

        // Get the second pattern with popcount 2
        let pattern = inject_page::<8>(1, 2).unwrap();
        assert_eq!(pattern.to_usize(), 0b00000101);
        assert_eq!(pattern.popcount(), 2);
    }

    #[test]
    fn test_binomial() {
        assert_eq!(binomial(8, 0), 1);
        assert_eq!(binomial(8, 1), 8);
        assert_eq!(binomial(8, 2), 28);
        assert_eq!(binomial(8, 3), 56);
        assert_eq!(binomial(8, 4), 70);
        assert_eq!(binomial(8, 8), 1);
        assert_eq!(binomial(8, 9), 0);
    }

    #[test]
    fn test_page_inject_roundtrip() {
        for popcount in 0..=8 {
            let total_pages = page_count::<8>(popcount);

            for page in 0..total_pages.min(10) {
                let pattern = inject_page::<8>(page, popcount).unwrap();
                assert_eq!(pattern.popcount() as usize, popcount);
                assert_eq!(page_of(pattern), page);
            }
        }
    }
}
