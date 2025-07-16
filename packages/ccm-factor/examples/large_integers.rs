//! Example of factoring larger integers with custom configuration

use ccm_factor::{BigUint, CCMFactor, FactorConfig};
use std::time::Instant;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Custom configuration for larger numbers
    let config = FactorConfig {
        channel_size: 16,          // Use 16-bit channels
        adaptive_channels: true,   // Let it adapt for very large numbers
        max_window_size: 32,       // Larger windows for bigger patterns
        min_confidence: 0.6,       // Slightly lower threshold
        parallel: true,            // Enable parallel processing
        max_attempts: 5000,        // More attempts for harder problems
        resonance_tolerance: 1e-9, // Tighter tolerance
    };

    let mut factor = CCMFactor::<f64>::with_config(config)?;

    println!("Factoring larger integers with CCM\n");

    // Test cases with known factorizations
    let test_cases = vec![
        // Medium semiprimes
        ("10001", BigUint::from(10001u32)), // 73 * 137
        ("10403", BigUint::from(10403u32)), // 101 * 103
        // Larger composites
        ("123456", BigUint::from(123456u32)), // 2^6 * 3 * 643
        ("999999", BigUint::from(999999u32)), // 3^3 * 7 * 11 * 13 * 37
        // Perfect powers
        ("65536", BigUint::from(65536u32)), // 2^16
        ("59049", BigUint::from(59049u32)), // 3^10
        // Mersenne composite
        ("8191", BigUint::from(8191u32)),   // 2^13 - 1 (prime)
        ("32767", BigUint::from(32767u32)), // 2^15 - 1 = 7 * 31 * 151
    ];

    for (name, n) in test_cases {
        println!("Factoring {} ({}):", name, n);
        let start = Instant::now();

        match factor.factor(&n) {
            Ok(factors) => {
                let elapsed = start.elapsed();

                print!("  {} = ", n);
                for (i, f) in factors.iter().enumerate() {
                    if i > 0 {
                        print!(" × ");
                    }
                    print!("{}", f);
                }
                println!();
                println!("  Time: {:?}", elapsed);

                // Verify
                let product: BigUint = factors.iter().product();
                assert_eq!(product, n, "Product verification failed!");
            }
            Err(e) => {
                println!("  Failed: {:?}", e);
            }
        }
        println!();
    }

    // Demonstrate adaptive channel sizing
    println!("\nAdaptive channel sizing demonstration:");

    let sizes = vec![
        ("8-bit", BigUint::from(255u8)),
        ("16-bit", BigUint::from(65535u16)),
        ("32-bit", BigUint::from(4294967295u32)),
        ("64-bit", BigUint::from(18446744073709551615u64)),
    ];

    for (desc, n) in sizes {
        println!("{} number: {}", desc, n);
        let start = Instant::now();

        match factor.factor(&n) {
            Ok(factors) => {
                println!("  Found {} factors in {:?}", factors.len(), start.elapsed());
            }
            Err(e) => {
                println!("  Error: {:?}", e);
            }
        }
    }

    Ok(())
}
