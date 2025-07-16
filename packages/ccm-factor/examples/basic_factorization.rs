//! Basic factorization example

use ccm_factor::{BigUint, CCMFactor};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Create a CCM factorization engine
    let mut factor = CCMFactor::<f64>::new()?;

    // Factor some numbers
    let numbers = vec![
        15u32, // 3 * 5
        21,    // 3 * 7
        35,    // 5 * 7
        77,    // 7 * 11
        143,   // 11 * 13
        221,   // 13 * 17
        1001,  // 7 * 11 * 13
        2047,  // 23 * 89
    ];

    for n in numbers {
        println!("\nFactoring {}:", n);

        let n_big = BigUint::from(n);
        match factor.factor(&n_big) {
            Ok(factors) => {
                print!("{} = ", n);
                for (i, f) in factors.iter().enumerate() {
                    if i > 0 {
                        print!(" × ");
                    }
                    print!("{}", f);
                }
                println!();

                // Verify
                let product: BigUint = factors.iter().product();
                assert_eq!(product, n_big);
            }
            Err(e) => {
                println!("Failed to factor {}: {:?}", n, e);
            }
        }
    }

    // Try a prime number
    println!("\nTrying prime numbers:");
    for p in [17u32, 19, 23, 29, 31] {
        let n = BigUint::from(p);
        let factors = factor.factor(&n)?;
        println!("{} = {} (prime: {})", p, factors[0], factors.len() == 1);
    }

    Ok(())
}
