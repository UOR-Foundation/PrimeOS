//! Test that alpha values produce unique minimum resonances per Klein group

use crate::{AlphaVec, BitWord, Resonance};
use std::collections::HashMap;

#[test]
fn test_klein_group_minimum_uniqueness() {
    let alpha = create_test_alpha();

    // Map from minimum resonance to list of Klein groups with that minimum
    let mut resonance_to_groups: HashMap<String, Vec<Vec<u8>>> = HashMap::new();

    // Check all 64 Klein groups (256 values / 4 members per group)
    let mut checked = vec![false; 256];

    for i in 0..=255u8 {
        if checked[i as usize] {
            continue;
        }

        let base = BitWord::from_u8(i);
        let members = <BitWord as Resonance<f64>>::class_members(&base);

        // Mark all members as checked
        for m in &members {
            checked[m.to_usize()] = true;
        }

        // Find minimum resonance in this group
        let mut min_resonance = f64::INFINITY;
        let mut min_member = members[0].clone();

        for m in &members {
            let r = m.r(&alpha);
            if r < min_resonance || (r == min_resonance && m.to_usize() < min_member.to_usize()) {
                min_resonance = r;
                min_member = m.clone();
            }
        }

        // Store this group under its minimum resonance
        let resonance_key = format!("{:.10}", min_resonance);
        let group_bytes: Vec<u8> = members.iter().map(|m| m.to_usize() as u8).collect();

        resonance_to_groups
            .entry(resonance_key)
            .or_insert_with(Vec::new)
            .push(group_bytes);
    }

    // Check for non-unique minimum resonances
    let mut non_unique = Vec::new();
    for (resonance, groups) in &resonance_to_groups {
        if groups.len() > 1 {
            non_unique.push((resonance.clone(), groups.clone()));
        }
    }

    if !non_unique.is_empty() {
        println!("Non-unique minimum resonances found!");
        for (resonance, groups) in &non_unique {
            println!("\nResonance {}: {} Klein groups", resonance, groups.len());
            for (i, group) in groups.iter().enumerate() {
                println!("  Group {}: {:?}", i, group);
            }
        }

        panic!(
            "Alpha values do not produce unique minimum resonances per Klein group. \
                This breaks BJC codec bijectivity!"
        );
    }
}

/// Create test alpha vector
fn create_test_alpha() -> AlphaVec<f64> {
    AlphaVec::try_from(vec![
        std::f64::consts::E,        // e
        1.8392867552141612,         // Tribonacci
        1.6180339887498950,         // Golden ratio
        std::f64::consts::PI,       // π
        3.0_f64.sqrt(),             // √3
        2.0,                        // 2
        std::f64::consts::PI / 2.0, // π/2
        2.0 / std::f64::consts::PI, // 2/π (unity)
    ])
    .unwrap()
}
