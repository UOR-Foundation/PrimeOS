//! Tool to find alpha values that ensure unique minimum resonances per Klein group

use crate::{AlphaVec, BitWord, Resonance};
use std::collections::HashMap;

/// Check if a set of alpha values produces unique minimum resonances
fn check_alpha_uniqueness(alpha: &AlphaVec<f64>) -> (bool, Vec<(String, Vec<Vec<u8>>)>) {
    let mut resonance_to_groups: HashMap<String, Vec<Vec<u8>>> = HashMap::new();
    let mut checked = vec![false; 256];

    for i in 0..=255u8 {
        if checked[i as usize] {
            continue;
        }

        let base = BitWord::<8>::from(i);
        let members = <BitWord<8> as Resonance<f64>>::class_members(&base);

        for m in &members {
            checked[m.to_usize()] = true;
        }

        let mut min_resonance = f64::INFINITY;
        let mut min_member = members[0];

        for &m in &members {
            let r = m.r(alpha);
            if r < min_resonance || (r == min_resonance && m.to_usize() < min_member.to_usize()) {
                min_resonance = r;
                min_member = m;
            }
        }

        let resonance_key = format!("{:.10}", min_resonance);
        let group_bytes: Vec<u8> = members.iter().map(|m| m.to_usize() as u8).collect();

        resonance_to_groups
            .entry(resonance_key)
            .or_insert_with(Vec::new)
            .push(group_bytes);
    }

    let mut non_unique = Vec::new();
    for (resonance, groups) in &resonance_to_groups {
        if groups.len() > 1 {
            non_unique.push((resonance.clone(), groups.clone()));
        }
    }

    (non_unique.is_empty(), non_unique)
}

#[test]
fn find_good_alphas() {
    // Try different combinations of mathematical constants
    let _candidates = vec![
        ("e", std::f64::consts::E),
        ("pi", std::f64::consts::PI),
        ("sqrt(2)", std::f64::consts::SQRT_2),
        ("sqrt(3)", 3.0_f64.sqrt()),
        ("sqrt(5)", 5.0_f64.sqrt()),
        ("phi", 1.6180339887498950), // Golden ratio
        ("tribonacci", 1.8392867552141612),
        ("sqrt(e)", std::f64::consts::E.sqrt()),
        ("sqrt(pi)", std::f64::consts::PI.sqrt()),
        ("2", 2.0),
        ("3", 3.0),
        ("1/2", 0.5),
        ("1/3", 1.0 / 3.0),
        ("e/2", std::f64::consts::E / 2.0),
        ("pi/2", std::f64::consts::PI / 2.0),
        ("2/pi", 2.0 / std::f64::consts::PI),
        ("e/pi", std::f64::consts::E / std::f64::consts::PI),
        ("pi/e", std::f64::consts::PI / std::f64::consts::E),
    ];

    println!("Searching for alpha combinations that ensure unique Klein group minima...\n");

    // We need 8 values where the last two satisfy unity constraint
    // Try different combinations
    let mut found_valid = false;

    // First, try some hand-picked combinations that avoid problematic patterns
    let test_cases = vec![
        // Avoid having α₅ = 1/√2 when α₇ = 1/√2, as this creates symmetries
        vec![
            std::f64::consts::E,
            1.8392867552141612, // tribonacci
            1.6180339887498950, // phi
            std::f64::consts::PI,
            3.0_f64.sqrt(), // √3 instead of √2
            2.0,
            std::f64::consts::PI / 2.0,
            2.0 / std::f64::consts::PI, // Unity: (π/2) * (2/π) = 1
        ],
        vec![
            2.0,
            std::f64::consts::E,
            1.8392867552141612,
            1.6180339887498950,
            std::f64::consts::PI,
            3.0_f64.sqrt(),
            5.0_f64.sqrt(),
            1.0 / 5.0_f64.sqrt(), // Unity: √5 * (1/√5) = 1
        ],
        vec![
            std::f64::consts::PI,
            std::f64::consts::E,
            2.0,
            3.0,
            1.6180339887498950,
            1.8392867552141612,
            3.0_f64.sqrt(),
            1.0 / 3.0_f64.sqrt(), // Unity: √3 * (1/√3) = 1
        ],
    ];

    for (i, values) in test_cases.iter().enumerate() {
        match AlphaVec::try_from(values.clone()) {
            Ok(alpha) => {
                let (is_unique, non_unique) = check_alpha_uniqueness(&alpha);

                println!("Test case {}:", i + 1);
                println!(
                    "  Alpha values: {:?}",
                    values
                        .iter()
                        .map(|v| format!("{:.6}", v))
                        .collect::<Vec<_>>()
                );
                println!(
                    "  Unity product: {} * {} = {}",
                    values[6],
                    values[7],
                    values[6] * values[7]
                );

                if is_unique {
                    println!("  ✓ All Klein groups have unique minimum resonances!");
                    found_valid = true;

                    // Print the successful alpha configuration
                    println!("\nSuccessful alpha configuration:");
                    for (_j, &v) in values.iter().enumerate() {
                        println!("    α₇ = {:.15}", v);
                    }
                    break;
                } else {
                    println!("  ✗ {} non-unique resonances found", non_unique.len());
                }
                println!();
            }
            Err(e) => {
                println!("Test case {}: Invalid alpha vector: {:?}\n", i + 1, e);
            }
        }
    }

    if !found_valid {
        // Try random perturbations of promising values
        println!("\nTrying perturbations of mathematical constants...\n");

        let base_values = vec![
            std::f64::consts::E,
            std::f64::consts::PI,
            1.8392867552141612,
            1.6180339887498950,
            2.0,
            3.0,
            0.5, // Will be adjusted for unity
            2.0, // Will be adjusted for unity
        ];

        for perturbation in 0..20 {
            let mut values = base_values.clone();

            // Apply small perturbations to avoid exact symmetries
            for i in 0..6 {
                values[i] *= 1.0 + (perturbation as f64 + 1.0) * 0.01;
            }

            // Ensure unity constraint
            values[6] = 2.0 + perturbation as f64 * 0.1;
            values[7] = 1.0 / values[6];

            match AlphaVec::try_from(values.clone()) {
                Ok(alpha) => {
                    let (is_unique, _non_unique) = check_alpha_uniqueness(&alpha);

                    if is_unique {
                        println!(
                            "Found valid configuration with perturbation {}!",
                            perturbation
                        );
                        println!(
                            "  Alpha values: {:?}",
                            values
                                .iter()
                                .map(|v| format!("{:.6}", v))
                                .collect::<Vec<_>>()
                        );
                        found_valid = true;
                        break;
                    }
                }
                Err(_) => continue,
            }
        }
    }

    assert!(
        found_valid,
        "Could not find alpha values that ensure unique Klein group minima!"
    );
}

#[test]
fn analyze_problem_pattern() {
    // Analyze why certain alpha configurations fail
    let alpha = AlphaVec::try_from(vec![
        std::f64::consts::E,
        1.8392867552141612,
        1.6180339887498950,
        std::f64::consts::SQRT_2,
        std::f64::consts::PI,
        1.0 / std::f64::consts::SQRT_2,
        std::f64::consts::SQRT_2,
        1.0 / std::f64::consts::SQRT_2,
    ])
    .unwrap();

    // Look at the problematic groups
    println!("Analyzing problematic Klein group pairs:\n");

    let group1 = vec![0u8, 64, 128, 192];
    let group2 = vec![40u8, 104, 168, 232];

    println!("Group 1: {:?}", group1);
    println!("Group 2: {:?}", group2);
    println!(
        "Difference: {:?}\n",
        group1
            .iter()
            .zip(&group2)
            .map(|(a, b)| b - a)
            .collect::<Vec<_>>()
    );

    // Check bit patterns
    println!("Bit patterns:");
    for (a, b) in group1.iter().zip(&group2) {
        println!("  {:08b} vs {:08b} (diff: {:08b})", a, b, a ^ b);
    }

    // The pattern shows that problematic groups differ by bit 5 (value 32) and bit 3 (value 8)
    // This suggests α₃ and α₅ are creating the symmetry

    println!("\nResonance analysis:");
    for (a, b) in group1.iter().zip(&group2) {
        let wa = BitWord::<8>::from(*a);
        let wb = BitWord::<8>::from(*b);
        println!(
            "  R({:3}) = {:.10}, R({:3}) = {:.10}",
            a,
            wa.r(&alpha),
            b,
            wb.r(&alpha)
        );
    }

    // When α₅ = 1/√2 and α₇ = 1/√2, we get problematic symmetries
    println!(
        "\nProblem: α₅ = {} and α₇ = {} are the same!",
        alpha[5], alpha[7]
    );
    println!("This creates symmetry between bits 5 and 7, breaking uniqueness.");
}
