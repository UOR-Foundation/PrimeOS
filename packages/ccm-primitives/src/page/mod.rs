//! Page symmetry helpers

use crate::bitword::BitWord;

/// Get the page index for a given bit pattern
/// Page = lexicographic position among patterns with same popcount
pub fn page_of<const N: usize>(word: BitWord<N>) -> usize {
    let popcount = word.popcount() as usize;
    if popcount == 0 {
        return 0;
    }

    // Count how many patterns with same popcount come before this one
    let mut page = 0;
    let value = word.to_usize();

    // Iterate through all patterns with same popcount that are smaller
    for i in 0..value {
        if (i as u64).count_ones() == popcount as u32 {
            page += 1;
        }
    }

    page
}

/// Inject a page index to create a bit pattern
/// Inverse of page_of - creates the nth pattern with given popcount
pub fn inject_page<const N: usize>(page: usize, popcount: usize) -> Option<BitWord<N>> {
    if popcount > N {
        return None;
    }

    let mut count = 0;
    let max_value = if N == 64 { !0u64 } else { (1u64 << N) - 1 };

    for i in 0..=max_value {
        if i.count_ones() == popcount as u32 {
            if count == page {
                return Some(BitWord::from(i));
            }
            count += 1;
        }
    }

    None
}

/// Compute binomial coefficient C(n, k)
pub fn binomial(n: usize, k: usize) -> usize {
    if k > n {
        return 0;
    }
    if k == 0 || k == n {
        return 1;
    }

    let k = k.min(n - k); // Take advantage of symmetry
    let mut result = 1;

    for i in 0..k {
        result = result * (n - i) / (i + 1);
    }

    result
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
        assert_eq!(page_of(BitWord::<8>::from(0b00000000)), 0);

        // First pattern with popcount 1
        assert_eq!(page_of(BitWord::<8>::from(0b00000001)), 0);

        // Second pattern with popcount 1
        assert_eq!(page_of(BitWord::<8>::from(0b00000010)), 1);

        // Third pattern with popcount 1
        assert_eq!(page_of(BitWord::<8>::from(0b00000100)), 2);
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
