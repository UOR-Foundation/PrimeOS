//! Debug test for Klein group unity constraint

use ccm_core::BitWord;
use ccm_embedding::{AlphaVec, Resonance};

#[test]
fn debug_klein_unity() {
    let n = 3;
    let alpha = AlphaVec::<f64>::mathematical(n).unwrap();
    
    println!("\nAlpha values for n={}:", n);
    for i in 0..n {
        println!("  alpha[{}] = {:?}", i, alpha.get(i));
    }
    
    // Check unity constraint
    let alpha_n2 = alpha.get(n-2).unwrap();
    let alpha_n1 = alpha.get(n-1).unwrap();
    let unity_product = alpha_n2 * alpha_n1;
    println!("\nUnity constraint check:");
    println!("  alpha[{}] * alpha[{}] = {} * {} = {}", 
        n-2, n-1, alpha_n2, alpha_n1, unity_product);
    println!("  Expected: 1.0");
    println!("  Satisfied: {}", alpha.verify_unity_constraint());
    
    // Test Klein orbit
    let b = BitWord::from_u64(0b000, n);
    let members = <BitWord as Resonance<f64>>::class_members(&b);
    
    println!("\nKlein orbit for 0b000:");
    for (i, member) in members.iter().enumerate() {
        let val = member.to_usize();
        let r = member.r(&alpha);
        println!("  Member {}: 0b{:03b} -> R = {}", i, val, r);
    }
}