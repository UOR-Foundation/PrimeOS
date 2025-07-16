//! Benchmarks for CCM factorization

use ccm_factor::{BigUint, CCMFactor};
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

fn bench_small_semiprimes(c: &mut Criterion) {
    let mut group = c.benchmark_group("small_semiprimes");

    let test_cases = vec![
        ("3×5", 15u32),
        ("7×11", 77u32),
        ("13×17", 221u32),
        ("19×23", 437u32),
        ("29×31", 899u32),
    ];

    let mut factor = CCMFactor::<f64>::new().unwrap();

    for (name, n) in test_cases {
        group.bench_with_input(BenchmarkId::from_parameter(name), &n, |b, &n| {
            let n_big = BigUint::from(n);
            b.iter(|| {
                let _ = factor.factor(black_box(&n_big)).unwrap();
            });
        });
    }

    group.finish();
}

fn bench_perfect_powers(c: &mut Criterion) {
    let mut group = c.benchmark_group("perfect_powers");

    let test_cases = vec![
        ("2^4", 16u32),
        ("2^8", 256u32),
        ("3^3", 27u32),
        ("3^4", 81u32),
        ("5^3", 125u32),
    ];

    let mut factor = CCMFactor::<f64>::new().unwrap();

    for (name, n) in test_cases {
        group.bench_with_input(BenchmarkId::from_parameter(name), &n, |b, &n| {
            let n_big = BigUint::from(n);
            b.iter(|| {
                let _ = factor.factor(black_box(&n_big)).unwrap();
            });
        });
    }

    group.finish();
}

fn bench_channel_sizes(c: &mut Criterion) {
    let mut group = c.benchmark_group("channel_sizes");

    // Test different channel sizes
    let sizes = vec![8, 16, 32];
    let n = BigUint::from(1001u32); // 7 × 11 × 13

    for channel_size in sizes {
        group.bench_with_input(
            BenchmarkId::new("channel_size", channel_size),
            &channel_size,
            |b, &channel_size| {
                let mut factor = CCMFactor::<f64>::with_config(ccm_factor::FactorConfig {
                    channel_size,
                    adaptive_channels: false,
                    ..Default::default()
                })
                .unwrap();

                b.iter(|| {
                    let _ = factor.factor(black_box(&n)).unwrap();
                });
            },
        );
    }

    group.finish();
}

fn bench_vs_trial_division(c: &mut Criterion) {
    let mut group = c.benchmark_group("ccm_vs_trial");

    // Simple trial division for comparison
    fn trial_division(n: &BigUint) -> Vec<BigUint> {
        let mut factors = Vec::new();
        let mut remaining = n.clone();
        let mut divisor = BigUint::from(2u32);

        while &divisor * &divisor <= remaining {
            while (&remaining % &divisor).is_zero() {
                factors.push(divisor.clone());
                remaining /= &divisor;
            }
            divisor += 1u32;
        }

        if remaining > BigUint::from(1u32) {
            factors.push(remaining);
        }

        factors
    }

    let test_numbers = vec![
        143u32, // 11 × 13
        323,    // 17 × 19
        667,    // 23 × 29
        1147,   // 31 × 37
    ];

    let mut ccm_factor = CCMFactor::<f64>::new().unwrap();

    for n in test_numbers {
        let n_big = BigUint::from(n);

        group.bench_with_input(BenchmarkId::new("CCM", n), &n_big, |b, n| {
            b.iter(|| {
                let _ = ccm_factor.factor(black_box(n)).unwrap();
            });
        });

        group.bench_with_input(BenchmarkId::new("Trial", n), &n_big, |b, n| {
            b.iter(|| {
                let _ = trial_division(black_box(n));
            });
        });
    }

    group.finish();
}

#[cfg(feature = "parallel")]
fn bench_parallel_vs_sequential(c: &mut Criterion) {
    use ccm_factor::ParallelCCMFactor;

    let mut group = c.benchmark_group("parallel_vs_sequential");

    let n = BigUint::from(999999u32); // 3^3 × 7 × 11 × 13 × 37

    group.bench_function("sequential", |b| {
        let mut factor = CCMFactor::<f64>::new().unwrap();
        b.iter(|| {
            let _ = factor.factor(black_box(&n)).unwrap();
        });
    });

    group.bench_function("parallel", |b| {
        let mut factor = ParallelCCMFactor::<f64>::new().unwrap();
        b.iter(|| {
            let _ = factor.factor(black_box(&n)).unwrap();
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_small_semiprimes,
    bench_perfect_powers,
    bench_channel_sizes,
    bench_vs_trial_division,
);

#[cfg(feature = "parallel")]
criterion_group!(parallel_benches, bench_parallel_vs_sequential,);

#[cfg(not(feature = "parallel"))]
criterion_main!(benches);

#[cfg(feature = "parallel")]
criterion_main!(benches, parallel_benches);
