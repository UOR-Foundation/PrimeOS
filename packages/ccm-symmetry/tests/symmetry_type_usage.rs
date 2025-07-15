//! Integration test demonstrating SymmetryType usage in window analysis
//!
//! This test shows how SymmetryType can be used to:
//! 1. Identify symmetries in data windows
//! 2. Guide decomposition strategies
//! 3. Associate conservation laws with symmetries

use ccm_symmetry::SymmetryType;

#[cfg(feature = "std")]
use std::collections::HashMap;
#[cfg(not(feature = "std"))]
use hashbrown::HashMap;

/// Mock window analysis structure (similar to ccm-coc's WindowAnalysis)
#[derive(Debug)]
struct WindowAnalysis {
    /// Detected symmetries in this window
    pub symmetries: Vec<SymmetryType>,
    /// Conservation quantities associated with symmetries
    pub conserved_quantities: HashMap<String, f64>,
}

impl WindowAnalysis {
    fn new() -> Self {
        Self {
            symmetries: Vec::new(),
            conserved_quantities: HashMap::new(),
        }
    }
    
    /// Add a detected symmetry
    fn add_symmetry(&mut self, sym: SymmetryType) {
        self.symmetries.push(sym);
    }
    
    /// Add a conserved quantity associated with a symmetry
    fn add_conserved_quantity(&mut self, name: String, value: f64) {
        self.conserved_quantities.insert(name, value);
    }
}

/// Detect symmetries in a mock data window
fn detect_symmetries(data: &[u8]) -> Vec<SymmetryType> {
    let mut symmetries = Vec::new();
    
    // Check for Klein group structure (XOR patterns)
    if has_klein_structure(data) {
        symmetries.push(SymmetryType::Klein);
    }
    
    // Check for cyclic patterns
    if let Some(period) = find_cyclic_period(data) {
        symmetries.push(SymmetryType::Cyclic(period));
    }
    
    // Check for reflection symmetry
    if is_palindromic(data) {
        symmetries.push(SymmetryType::Reflection);
    }
    
    // Check for translation invariance
    if is_shift_invariant(data) {
        symmetries.push(SymmetryType::Translation);
    }
    
    symmetries
}

/// Mock check for Klein group structure
fn has_klein_structure(data: &[u8]) -> bool {
    // In real CCM, this would check for XOR-homomorphic properties
    // For Klein V₄ = {0, 1, 2, 3} under XOR mod 4, we check if data matches
    data.len() == 4 && {
        // Klein four-group V₄ = {00, 01, 10, 11} in binary
        // These form a group under XOR: 00⊕01=01, 00⊕10=10, 01⊕10=11, etc.
        let mut sorted = data.to_vec();
        sorted.sort();
        sorted == vec![0b00, 0b01, 0b10, 0b11]
    }
}

/// Find cyclic period in data
fn find_cyclic_period(data: &[u8]) -> Option<usize> {
    for period in 2..=data.len() / 2 {
        if data.chunks(period).all(|chunk| chunk == &data[..chunk.len()]) {
            return Some(period);
        }
    }
    None
}

/// Check if data is palindromic (reflection symmetry)
fn is_palindromic(data: &[u8]) -> bool {
    let n = data.len();
    (0..n / 2).all(|i| data[i] == data[n - 1 - i])
}

/// Check for translation invariance
fn is_shift_invariant(data: &[u8]) -> bool {
    // Mock: check if all bytes are the same (trivial translation invariance)
    data.windows(2).all(|w| w[0] == w[1])
}

/// Guide decomposition based on detected symmetries
fn suggest_decomposition_strategy(symmetries: &[SymmetryType]) -> &'static str {
    for sym in symmetries {
        match sym {
            SymmetryType::Klein => return "Use Klein-guided decomposition",
            SymmetryType::Cyclic(_) => return "Use cyclic decomposition",
            SymmetryType::Reflection => return "Use reflection-based splitting",
            _ => continue,
        }
    }
    "Use exhaustive search"
}

/// Associate conservation laws with symmetries (Noether's theorem)
fn associate_conservation_laws(symmetry: &SymmetryType) -> Option<(&'static str, f64)> {
    match symmetry {
        SymmetryType::Translation => Some(("momentum", 1.0)),
        SymmetryType::Rotation => Some(("angular_momentum", 2.0)),
        SymmetryType::Klein => Some(("resonance", 1.618)),
        SymmetryType::Cyclic(n) => Some(("cyclic_charge", *n as f64)),
        _ => None,
    }
}

#[test]
fn test_symmetry_detection_in_window() {
    // Test data with Klein group structure
    let klein_data = vec![0b00, 0b01, 0b10, 0b11]; // V₄ = {00, 01, 10, 11}
    let symmetries = detect_symmetries(&klein_data);
    
    assert!(symmetries.contains(&SymmetryType::Klein));
    assert_eq!(symmetries.len(), 1);
}

#[test]
fn test_cyclic_pattern_detection() {
    // Test data with cyclic period 3
    let cyclic_data = vec![1, 2, 3, 1, 2, 3, 1, 2, 3];
    let symmetries = detect_symmetries(&cyclic_data);
    
    assert!(symmetries.contains(&SymmetryType::Cyclic(3)));
}

#[test]
fn test_reflection_symmetry() {
    // Palindromic data
    let palindrome = vec![1, 2, 3, 4, 3, 2, 1];
    let symmetries = detect_symmetries(&palindrome);
    
    assert!(symmetries.contains(&SymmetryType::Reflection));
}

#[test]
fn test_window_analysis_workflow() {
    // Create mock window data
    let window_data = vec![0b00, 0b01, 0b10, 0b11]; // Klein structure
    
    // Create window analysis
    let mut analysis = WindowAnalysis::new();
    
    // Detect symmetries
    let symmetries = detect_symmetries(&window_data);
    for sym in symmetries {
        analysis.add_symmetry(sym.clone());
        
        // Add associated conservation laws
        if let Some((name, value)) = associate_conservation_laws(&sym) {
            analysis.add_conserved_quantity(name.to_string(), value);
        }
    }
    
    // Verify results
    assert_eq!(analysis.symmetries.len(), 1);
    assert!(matches!(analysis.symmetries[0], SymmetryType::Klein));
    assert!(analysis.conserved_quantities.contains_key("resonance"));
    assert_eq!(analysis.conserved_quantities["resonance"], 1.618);
}

#[test]
fn test_decomposition_strategy_selection() {
    // Test Klein structure
    let klein_syms = vec![SymmetryType::Klein];
    assert_eq!(
        suggest_decomposition_strategy(&klein_syms),
        "Use Klein-guided decomposition"
    );
    
    // Test cyclic structure
    let cyclic_syms = vec![SymmetryType::Cyclic(5)];
    assert_eq!(
        suggest_decomposition_strategy(&cyclic_syms),
        "Use cyclic decomposition"
    );
    
    // Test no special structure
    let no_syms = vec![];
    assert_eq!(
        suggest_decomposition_strategy(&no_syms),
        "Use exhaustive search"
    );
}

#[test]
fn test_symmetry_properties() {
    // Test various symmetry properties
    let symmetries = vec![
        SymmetryType::Translation,
        SymmetryType::Klein,
        SymmetryType::Cyclic(6),
        SymmetryType::Dihedral(4),
        SymmetryType::Permutation(3),
    ];
    
    for sym in symmetries {
        match &sym {
            SymmetryType::Translation => {
                assert!(sym.is_continuous());
                assert!(sym.is_abelian());
                assert_eq!(sym.order(), None);
            }
            SymmetryType::Klein => {
                assert!(sym.is_discrete());
                assert!(sym.is_abelian());
                assert_eq!(sym.order(), Some(4));
            }
            SymmetryType::Cyclic(n) => {
                assert!(sym.is_discrete());
                assert!(sym.is_abelian());
                assert_eq!(sym.order(), Some(*n));
            }
            SymmetryType::Dihedral(n) => {
                assert!(sym.is_discrete());
                assert_eq!(sym.is_abelian(), *n <= 2);
                assert_eq!(sym.order(), Some(2 * n));
            }
            SymmetryType::Permutation(n) => {
                assert!(sym.is_discrete());
                assert_eq!(sym.is_abelian(), *n <= 2);
                // S₃ has order 6
                if *n == 3 {
                    assert_eq!(sym.order(), Some(6));
                }
            }
            _ => {}
        }
    }
}

#[test]
fn test_display_formatting() {
    let symmetries = vec![
        (SymmetryType::Translation, "Translation"),
        (SymmetryType::Klein, "Klein V₄"),
        (SymmetryType::Cyclic(5), "Cyclic C5"),
        (SymmetryType::Dihedral(4), "Dihedral D4"),
        (SymmetryType::Custom("MyGroup".to_string()), "Custom(MyGroup)"),
    ];
    
    for (sym, expected) in symmetries {
        assert_eq!(format!("{}", sym), expected);
    }
}

#[cfg(feature = "serde")]
#[test]
fn test_serialization() {
    use serde_json;
    
    let sym = SymmetryType::Cyclic(5);
    
    // Serialize
    let json = serde_json::to_string(&sym).unwrap();
    assert_eq!(json, r#"{"Cyclic":5}"#);
    
    // Deserialize
    let deserialized: SymmetryType = serde_json::from_str(&json).unwrap();
    assert_eq!(deserialized, sym);
}