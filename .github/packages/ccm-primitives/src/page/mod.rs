//! Page symmetry helpers

use crate::bitword::BitWord;

/// Get the page index for a given bit pattern
/// Page = lexicographic position among patterns with same popcount
///
/// For a k-combination represented by positions c_1 < c_2 < ... < c_k,
/// the rank is: sum(C(c_i, i)) for i = 1..k
pub fn page_of(word: &BitWord) -> usize {
    let mut rank = 0;
    let mut k = 1; // 1-indexed for standard formula
    let n = word.len();

    // Find positions of set bits in ascending order
    for pos in 0..n {
        if word.bit(pos) {
            // Add C(pos, k) to rank
            rank += binomial(pos, k);
            k += 1;
        }
    }

    rank
}

/// Inject a page index to create a bit pattern
/// Inverse of page_of - creates the nth pattern with given popcount
///
/// Finds the k-combination with the given rank using the inverse
/// of the combinatorial number system
pub fn inject_page(page: usize, popcount: usize, n: usize) -> Option<BitWord> {
    if popcount > n {
        return None;
    }

    if popcount == 0 {
        return Some(BitWord::new(n));
    }

    // Check if page is valid
    if page >= binomial(n, popcount) {
        return None;
    }

    let mut result = BitWord::new(n);
    let mut rank = page;

    // Find positions for each of the k bits
    for i in (1..=popcount).rev() {
        // Find largest c such that C(c, i) <= rank
        let mut c = i - 1;
        while c < n && binomial(c + 1, i) <= rank {
            c += 1;
        }

        // Set bit at position c
        result.set_bit(c, true);

        // Subtract C(c, i) from rank
        rank -= binomial(c, i);
    }

    Some(result)
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
pub fn page_count(n: usize, popcount: usize) -> usize {
    binomial(n, popcount)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_page_of() {
        // All patterns with popcount 0 have page 0
        assert_eq!(page_of(&BitWord::from_u8(0b00000000u8)), 0);

        // Debug: print rankings for patterns with popcount 1
        println!("\nPatterns with popcount 1:");
        for i in 0..8 {
            let pattern = 1u8 << i;
            let word = BitWord::from_u8(pattern);
            let page = page_of(&word);
            println!("  0b{:08b} (bit {} set) -> page {}", pattern, i, page);
        }

        // First pattern with popcount 1
        assert_eq!(page_of(&BitWord::from_u8(0b00000001u8)), 0);

        // Second pattern with popcount 1
        assert_eq!(page_of(&BitWord::from_u8(0b00000010u8)), 1);

        // Third pattern with popcount 1
        assert_eq!(page_of(&BitWord::from_u8(0b00000100u8)), 2);
    }

    #[test]
    fn test_inject_page() {
        // Debug: print patterns with popcount 2
        println!("\nPatterns with popcount 2:");
        for page in 0..10 {
            if let Some(pattern) = inject_page(page, 2, 8) {
                println!("  page {} -> 0b{:08b}", page, pattern.to_usize());
            }
        }

        // Get the first pattern with popcount 2
        let pattern = inject_page(0, 2, 8).unwrap();
        assert_eq!(pattern.to_usize(), 0b00000011);
        assert_eq!(pattern.popcount(), 2);

        // Get the second pattern with popcount 2
        let pattern = inject_page(1, 2, 8).unwrap();
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
            let total_pages = page_count(8, popcount);

            for page in 0..total_pages.min(10) {
                let pattern = inject_page(page, popcount, 8).unwrap();
                assert_eq!(pattern.popcount() as usize, popcount);
                assert_eq!(page_of(&pattern), page);
            }
        }
    }

    #[test]
    fn test_page_large_sizes() {
        // Test with sizes larger than 64 bits
        for n in [65, 128, 256] {
            println!("\nTesting page operations for n={}", n);

            // Test patterns with various popcounts
            for popcount in [0, 1, 2, 3, n / 2, n - 1, n] {
                if popcount > n {
                    continue;
                }

                let total_pages = page_count(n, popcount);
                println!("  popcount={}: {} total pages", popcount, total_pages);

                // Test first few pages
                for page in 0..total_pages.min(5) {
                    let pattern = inject_page(page, popcount, n).unwrap();
                    assert_eq!(pattern.popcount() as usize, popcount);
                    assert_eq!(page_of(&pattern), page);
                }
            }
        }
    }

    #[test]
    fn test_binomial_large() {
        // Test binomial coefficients for large values
        assert_eq!(binomial(100, 2), 4950);
        assert_eq!(binomial(256, 1), 256);
        assert_eq!(binomial(256, 2), 32640);

        // Test symmetry: C(n,k) = C(n,n-k)
        for n in [64, 100, 128, 256] {
            for k in [1, 2, 3, 10] {
                if k <= n {
                    assert_eq!(binomial(n, k), binomial(n, n - k));
                }
            }
        }
    }
}
