//! Tests for cache functionality

use ccm::cache::CacheConfig;
use ccm::{CCMCore, StandardCCM};
use ccm_core::BitWord;

#[test]
fn test_alpha_cache() {
    let ccm = StandardCCM::<f64>::new(8).unwrap();

    // First call should generate and cache
    let alpha1 = ccm.generate_alpha().unwrap();

    // Second call should retrieve from cache
    let alpha2 = ccm.generate_alpha().unwrap();

    // Should be identical
    assert_eq!(alpha1.len(), alpha2.len());
    for i in 0..alpha1.len() {
        assert_eq!(alpha1[i], alpha2[i]);
    }
}

#[test]
fn test_minimal_resonance_cache() {
    let ccm = StandardCCM::<f64>::new(8).unwrap();
    let alpha = ccm.generate_alpha().unwrap();

    let input = BitWord::from_u8(123);

    // First call should compute and cache
    let min1 = ccm.find_minimum_resonance(&input, &alpha).unwrap();

    // Second call should retrieve from cache
    let min2 = ccm.find_minimum_resonance(&input, &alpha).unwrap();

    // Should be identical
    assert_eq!(min1, min2);
}

#[test]
fn test_klein_members_cache() {
    let ccm = StandardCCM::<f64>::new(8).unwrap();

    let word = BitWord::from_u8(42);

    // First call should compute and cache
    let members1 = ccm.klein_members(&word);

    // Second call should retrieve from cache
    let members2 = ccm.klein_members(&word);

    // Should be identical
    assert_eq!(members1.len(), members2.len());
    for i in 0..members1.len() {
        assert_eq!(members1[i], members2[i]);
    }
}

#[test]
fn test_cache_clear() {
    let ccm = StandardCCM::<f64>::new(8).unwrap();
    let alpha = ccm.generate_alpha().unwrap();

    let word = BitWord::from_u8(100);

    // Populate caches
    let _ = ccm.find_minimum_resonance(&word, &alpha).unwrap();
    let _ = ccm.klein_members(&word);

    // Clear cache
    ccm.clear_cache();

    // Operations should still work after clear
    let min = ccm.find_minimum_resonance(&word, &alpha).unwrap();
    let members = ccm.klein_members(&word);

    assert!(min.to_usize() < 256);
    assert_eq!(members.len(), 4);
}

#[test]
fn test_custom_cache_config() {
    let config = CacheConfig {
        alpha_cache_size: 8,
        klein_cache_size: 256,
        resonance_cache_size: 1024,
        basis_cache_size: 64,
        minimal_cache_size: 128,
        thread_safe: true,
    };

    let ccm = StandardCCM::<f64>::with_cache_config(8, config).unwrap();
    let alpha = ccm.generate_alpha().unwrap();

    // Should work with custom config
    let word = BitWord::from_u8(77);
    let min = ccm.find_minimum_resonance(&word, &alpha).unwrap();
    assert!(min.to_usize() < 256);
}

#[test]
fn test_resonance_caching_in_search() {
    let ccm = StandardCCM::<f64>::new(8).unwrap();
    let alpha = ccm.generate_alpha().unwrap();

    // Search will use cached resonance values
    let target = 1.5;
    let tolerance = 0.5;

    // First search populates cache
    let results1 = ccm.search_by_resonance(target, &alpha, tolerance).unwrap();

    // Second search should be faster due to cache
    let results2 = ccm.search_by_resonance(target, &alpha, tolerance).unwrap();

    // Results should be identical
    assert_eq!(results1.len(), results2.len());
}

#[test]
fn test_basis_element_cache() {
    let ccm = StandardCCM::<f64>::new(8).unwrap();
    let alpha = ccm.generate_alpha().unwrap();

    // Embed operation uses cached basis elements
    let word1 = BitWord::from_u8(10);
    let word2 = BitWord::from_u8(10); // Same value

    let section1 = ccm.embed(&word1, &alpha).unwrap();
    let section2 = ccm.embed(&word2, &alpha).unwrap(); // Should use cache

    // Coherence norms should be identical
    let norm1 = ccm.coherence_norm(&section1);
    let norm2 = ccm.coherence_norm(&section2);

    assert_eq!(norm1, norm2);
}

#[test]
fn test_cache_warming() {
    let ccm = StandardCCM::<f64>::new(8).unwrap();

    // Clear cache to start fresh
    ccm.clear_cache();

    // Warm the cache
    ccm.warm_cache().unwrap();

    // Check that common values are cached
    let alpha = ccm.generate_alpha().unwrap();

    // These should hit cache
    let word = BitWord::from_u8(0);
    let _ = ccm.find_minimum_resonance(&word, &alpha).unwrap();
    let _ = ccm.klein_members(&word);

    #[cfg(feature = "std")]
    {
        let stats = ccm.cache_stats();
        // Should have hits from warmed values
        assert!(stats.total_hits() > 0);
    }
}

#[test]
#[cfg(feature = "std")]
fn test_cache_statistics() {
    let ccm = StandardCCM::<f64>::new(8).unwrap();
    let alpha = ccm.generate_alpha().unwrap();

    // Reset stats to start fresh
    ccm.reset_cache_stats();

    // First access - should be a miss
    let word1 = BitWord::from_u8(42);
    let _ = ccm.find_minimum_resonance(&word1, &alpha).unwrap();

    // Second access - should be a hit
    let _ = ccm.find_minimum_resonance(&word1, &alpha).unwrap();

    let stats = ccm.cache_stats();
    assert_eq!(stats.minimal_hits, 1);
    assert_eq!(stats.minimal_misses, 1);
    assert_eq!(stats.total_hits(), 1);
    assert_eq!(stats.total_misses(), 1);
    assert!((stats.hit_rate() - 0.5).abs() < 0.01);
}

#[test]
#[cfg(feature = "std")]
fn test_cache_thread_safety() {
    use std::sync::Arc;
    use std::thread;

    let ccm = Arc::new(StandardCCM::<f64>::new(8).unwrap());
    let alpha = ccm.generate_alpha().unwrap();

    let mut handles = vec![];

    // Spawn multiple threads accessing cache
    for i in 0..4 {
        let ccm_clone = Arc::clone(&ccm);
        let alpha_clone = alpha.clone();

        let handle = thread::spawn(move || {
            let word = BitWord::from_u8((i * 50) as u8);
            let min = ccm_clone
                .find_minimum_resonance(&word, &alpha_clone)
                .unwrap();
            let members = ccm_clone.klein_members(&word);
            (min, members)
        });

        handles.push(handle);
    }

    // All threads should complete successfully
    for handle in handles {
        let (min, members) = handle.join().unwrap();
        assert!(min.to_usize() < 256);
        assert_eq!(members.len(), 4);
    }
}
