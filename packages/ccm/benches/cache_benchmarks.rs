//! Benchmarks for CCM cache performance

use ccm::cache::CacheConfig;
use ccm::{CCMCore, StandardCCM};
use ccm_core::BitWord;
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

fn bench_alpha_generation(c: &mut Criterion) {
    let mut group = c.benchmark_group("alpha_generation");

    // Test with cache
    group.bench_function("with_cache", |b| {
        let ccm = StandardCCM::<f64>::new(8).unwrap();
        b.iter(|| black_box(ccm.generate_alpha().unwrap()));
    });

    // Test without cache (clear before each iteration)
    group.bench_function("without_cache", |b| {
        let ccm = StandardCCM::<f64>::new(8).unwrap();
        b.iter(|| {
            ccm.clear_cache();
            black_box(ccm.generate_alpha().unwrap())
        });
    });

    group.finish();
}

fn bench_minimal_resonance(c: &mut Criterion) {
    let mut group = c.benchmark_group("minimal_resonance");
    let ccm = StandardCCM::<f64>::new(8).unwrap();
    let alpha = ccm.generate_alpha().unwrap();

    let test_words = vec![
        BitWord::from_u8(42),
        BitWord::from_u8(123),
        BitWord::from_u8(200),
    ];

    for word in &test_words {
        let word_val = word.to_usize();

        // With cache
        group.bench_with_input(BenchmarkId::new("with_cache", word_val), word, |b, w| {
            b.iter(|| black_box(ccm.find_minimum_resonance(w, &alpha).unwrap()));
        });

        // Without cache
        group.bench_with_input(BenchmarkId::new("without_cache", word_val), word, |b, w| {
            b.iter(|| {
                ccm.clear_cache();
                black_box(ccm.find_minimum_resonance(w, &alpha).unwrap())
            });
        });
    }

    group.finish();
}

fn bench_klein_members(c: &mut Criterion) {
    let mut group = c.benchmark_group("klein_members");
    let ccm = StandardCCM::<f64>::new(8).unwrap();

    // With cache
    group.bench_function("with_cache", |b| {
        let word = BitWord::from_u8(100);
        b.iter(|| black_box(ccm.klein_members(&word)));
    });

    // Without cache
    group.bench_function("without_cache", |b| {
        let word = BitWord::from_u8(100);
        b.iter(|| {
            ccm.clear_cache();
            black_box(ccm.klein_members(&word))
        });
    });

    group.finish();
}

fn bench_search_with_cache(c: &mut Criterion) {
    let mut group = c.benchmark_group("search_by_resonance");

    // Small dimension with cache
    group.bench_function("dim_8_with_cache", |b| {
        let ccm = StandardCCM::<f64>::new(8).unwrap();
        let alpha = ccm.generate_alpha().unwrap();

        b.iter(|| black_box(ccm.search_by_resonance(1.5, &alpha, 0.5).unwrap()));
    });

    // Small dimension without cache
    group.bench_function("dim_8_without_cache", |b| {
        let ccm = StandardCCM::<f64>::new(8).unwrap();
        let alpha = ccm.generate_alpha().unwrap();

        b.iter(|| {
            ccm.clear_cache();
            black_box(ccm.search_by_resonance(1.5, &alpha, 0.5).unwrap())
        });
    });

    group.finish();
}

fn bench_cache_warming(c: &mut Criterion) {
    let mut group = c.benchmark_group("cache_warming");

    group.bench_function("warm_cache_8", |b| {
        let ccm = StandardCCM::<f64>::new(8).unwrap();
        b.iter(|| {
            ccm.clear_cache();
            black_box(ccm.warm_cache().unwrap())
        });
    });

    group.bench_function("warm_cache_12", |b| {
        let ccm = StandardCCM::<f64>::new(12).unwrap();
        b.iter(|| {
            ccm.clear_cache();
            black_box(ccm.warm_cache().unwrap())
        });
    });

    group.finish();
}

#[cfg(feature = "std")]
fn bench_cache_overhead(c: &mut Criterion) {
    let mut group = c.benchmark_group("cache_overhead");

    // Measure overhead of statistics tracking
    group.bench_function("stats_tracking", |b| {
        let ccm = StandardCCM::<f64>::new(8).unwrap();
        let word = BitWord::from_u8(42);

        b.iter(|| {
            // This will update stats
            black_box(ccm.klein_members(&word));
            black_box(ccm.cache_stats());
        });
    });

    group.finish();
}

fn bench_different_cache_sizes(c: &mut Criterion) {
    let mut group = c.benchmark_group("cache_sizes");

    let sizes = vec![
        (
            "small",
            CacheConfig {
                alpha_cache_size: 4,
                klein_cache_size: 64,
                resonance_cache_size: 256,
                basis_cache_size: 32,
                minimal_cache_size: 64,
                thread_safe: true,
            },
        ),
        ("default", CacheConfig::default()),
        (
            "large",
            CacheConfig {
                alpha_cache_size: 128,
                klein_cache_size: 4096,
                resonance_cache_size: 16384,
                basis_cache_size: 1024,
                minimal_cache_size: 2048,
                thread_safe: true,
            },
        ),
    ];

    for (name, config) in sizes {
        group.bench_function(name, |b| {
            let ccm = StandardCCM::<f64>::with_cache_config(8, config.clone()).unwrap();
            let alpha = ccm.generate_alpha().unwrap();

            b.iter(|| {
                for i in 0..100u8 {
                    let word = BitWord::from_u8(i);
                    black_box(ccm.find_minimum_resonance(&word, &alpha).unwrap());
                }
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_alpha_generation,
    bench_minimal_resonance,
    bench_klein_members,
    bench_search_with_cache,
    bench_cache_warming,
    bench_different_cache_sizes
);

#[cfg(feature = "std")]
criterion_group!(std_benches, bench_cache_overhead);

#[cfg(not(feature = "std"))]
criterion_main!(benches);

#[cfg(feature = "std")]
criterion_main!(benches, std_benches);
