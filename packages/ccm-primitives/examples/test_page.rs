use ccm_primitives::bitword::BitWord;
use ccm_primitives::page::{page_of, inject_page, binomial, page_count};

fn main() {
    println!("Testing page module with new BitWord API...\n");
    
    // Test 1: Basic functionality
    println!("Test 1: Basic functionality");
    let word8 = BitWord::from_u8(0b00000101); // bits 0 and 2 set
    println!("  BitWord 0b00000101 has page: {}", page_of(&word8));
    
    // Test 2: Large BitWord (> 64 bits)
    println!("\nTest 2: Large BitWord (128 bits)");
    let mut word128 = BitWord::new(128);
    word128.set_bit(0, true);
    word128.set_bit(64, true);
    word128.set_bit(127, true);
    println!("  128-bit word with bits 0,64,127 set has page: {}", page_of(&word128));
    
    // Test 3: Roundtrip with inject_page
    println!("\nTest 3: Roundtrip test");
    for popcount in 1..=3 {
        let total = page_count(128, popcount);
        println!("  For popcount={}, there are {} possible pages", popcount, total);
        
        // Test first few pages
        for page in 0..5.min(total) {
            let pattern = inject_page(page, popcount, 128).unwrap();
            let recovered_page = page_of(&pattern);
            println!("    Page {} -> BitWord with {} bits -> Page {}", 
                     page, pattern.popcount(), recovered_page);
            assert_eq!(page, recovered_page);
        }
    }
    
    // Test 4: Very large BitWord (1024 bits)
    println!("\nTest 4: Very large BitWord (1024 bits)");
    let mut word1024 = BitWord::new(1024);
    word1024.set_bit(0, true);
    word1024.set_bit(500, true);
    word1024.set_bit(1023, true);
    let page = page_of(&word1024);
    println!("  1024-bit word with bits 0,500,1023 set has page: {}", page);
    
    // Verify roundtrip
    let recovered = inject_page(page, 3, 1024).unwrap();
    assert_eq!(recovered.popcount(), 3);
    assert!(recovered.bit(0));
    assert!(recovered.bit(500));
    assert!(recovered.bit(1023));
    println!("  Roundtrip successful!");
    
    // Test 5: Binomial coefficients for large values
    println!("\nTest 5: Large binomial coefficients");
    println!("  C(1000, 2) = {}", binomial(1000, 2));
    println!("  C(2000, 3) = {}", binomial(2000, 3));
    println!("  C(4096, 2) = {}", binomial(4096, 2));
    
    println!("\nAll tests passed!");
}