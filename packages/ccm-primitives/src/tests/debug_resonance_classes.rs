//! Debug resonance classes to understand why we get 24 instead of 96

#[cfg(test)]
mod tests {
    use crate::{Resonance, AlphaVec};
    use std::collections::BTreeMap;
    
    #[test]
    fn debug_resonance_class_count() {
        let alpha = AlphaVec::<f64>::for_bit_length(8).unwrap();
        
        // Map to store resonance -> Klein groups
        let mut resonance_map: BTreeMap<u64, Vec<u8>> = BTreeMap::new();
        
        // Check all 64 Klein groups
        for klein_base in 0u8..64 {
            let members = [
                klein_base,
                klein_base | 0b01000000,
                klein_base | 0b10000000,
                klein_base | 0b11000000,
            ];
            
            // Find minimum resonance in this Klein group
            let mut min_res = f64::INFINITY;
            let mut min_member = members[0];
            
            for &member in &members {
                let r = member.r(&alpha);
                if r < min_res {
                    min_res = r;
                    min_member = member;
                }
            }
            
            // Use bit representation to avoid floating point comparison issues
            let res_bits = min_res.to_bits();
            resonance_map.entry(res_bits).or_insert_with(Vec::new).push(klein_base);
        }
        
        println!("Total unique resonance values: {}", resonance_map.len());
        println!("\nResonance value distribution:");
        
        let mut sorted_resonances: Vec<(f64, Vec<u8>)> = resonance_map
            .into_iter()
            .map(|(bits, groups)| (f64::from_bits(bits), groups))
            .collect();
        
        sorted_resonances.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
        
        for (i, (resonance, klein_groups)) in sorted_resonances.iter().enumerate() {
            println!("  {}: R = {:.10}, Klein groups: {:?} (count: {})", 
                     i, resonance, klein_groups, klein_groups.len());
        }
        
        // Check the pattern - why do we get 24 instead of 96?
        println!("\n=== Analysis ===");
        println!("We have {} unique resonance values", sorted_resonances.len());
        println!("Average Klein groups per resonance: {}", 64.0 / sorted_resonances.len() as f64);
        
        // Check if certain bits dominate
        println!("\n=== Bit Pattern Analysis ===");
        for (resonance, klein_groups) in sorted_resonances.iter().take(5) {
            println!("R = {:.6}:", resonance);
            for &kg in klein_groups {
                let members = [
                    kg,
                    kg | 0b01000000,
                    kg | 0b10000000,
                    kg | 0b11000000,
                ];
                for m in &members {
                    let r = m.r(&alpha);
                    println!("  {:08b} -> {:.6}", m, r);
                }
                println!();
            }
        }
    }
}