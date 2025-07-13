//! Examples of using rotors for rotations in Clifford algebra

use ccm_coherence::{
    coherence_norm,
    rotor::{rotor_from_vectors, Rotor},
    CliffordAlgebra, CliffordElement,
};
use num_complex::Complex;
use std::f64::consts::PI;

fn main() {
    println!("=== Rotor Examples ===\n");

    let algebra = CliffordAlgebra::<f64>::generate(3).unwrap();

    // Example 1: Create a rotor from a bivector
    println!("1. Creating a rotor from a bivector (rotation in e₁e₂ plane)");
    let mut bivector = CliffordElement::<f64>::zero(3);
    let angle = PI / 4.0; // 45 degrees
    bivector
        .set_component(3, Complex::new(angle / 2.0, 0.0))
        .unwrap(); // e₁e₂

    let rotor = Rotor::from_bivector(&bivector, &algebra).unwrap();
    println!("   Rotation angle: {:.1} degrees", angle * 180.0 / PI);
    println!(
        "   Rotor is normalized: {}",
        rotor.as_element().is_unit_norm()
    );

    // Example 2: Apply rotor to a vector
    println!("\n2. Rotating a vector");
    let v = CliffordElement::<f64>::basis_vector(0, 3).unwrap(); // e₁
    let v_rotated = rotor.apply_to_vector(&v, &algebra).unwrap();

    println!("   Original vector: e₁");
    print_vector_components(&v_rotated);

    // Example 3: Compose rotations
    println!("\n3. Composing two rotations");
    let rotor2 = Rotor::from_bivector(&bivector, &algebra).unwrap();
    let composed = rotor.compose(&rotor2, &algebra).unwrap();

    let v_double_rotated = composed.apply_to_vector(&v, &algebra).unwrap();
    println!("   After two 45° rotations (90° total):");
    print_vector_components(&v_double_rotated);

    // Example 4: Create rotor from two vectors
    println!("\n4. Creating rotor that rotates one vector to another");
    let from = CliffordElement::<f64>::basis_vector(0, 3).unwrap(); // e₁
    let mut to = CliffordElement::<f64>::zero(3);
    // Create vector (e₁ + e₂)/√2
    to.set_component(1, Complex::new(1.0 / 2.0_f64.sqrt(), 0.0))
        .unwrap();
    to.set_component(2, Complex::new(1.0 / 2.0_f64.sqrt(), 0.0))
        .unwrap();

    let rotor_align = rotor_from_vectors(&from, &to, &algebra).unwrap();
    let result = rotor_align.apply_to_vector(&from, &algebra).unwrap();

    println!("   Rotating e₁ to (e₁ + e₂)/√2:");
    print_vector_components(&result);

    // Example 5: Rotor inverse
    println!("\n5. Rotor inverse (reverse rotation)");
    let inverse = rotor.inverse();
    let identity_test = rotor.compose(&inverse, &algebra).unwrap();
    println!("   R * R⁻¹ is identity: {}", identity_test.is_identity());

    // Apply inverse rotation
    let v_back = inverse.apply_to_vector(&v_rotated, &algebra).unwrap();
    println!("   Rotating back to original:");
    print_vector_components(&v_back);
}

fn print_vector_components(v: &CliffordElement<f64>) {
    // Print grade 1 components (vectors)
    let e1_comp = v.component(1).unwrap_or(Complex::new(0.0, 0.0));
    let e2_comp = v.component(2).unwrap_or(Complex::new(0.0, 0.0));
    let e3_comp = v.component(4).unwrap_or(Complex::new(0.0, 0.0));

    println!(
        "   Components: {:.3}e₁ + {:.3}e₂ + {:.3}e₃",
        e1_comp.re, e2_comp.re, e3_comp.re
    );

    // Check it's still normalized
    let norm = coherence_norm(v);
    println!("   Norm: {:.3}", norm);
}
