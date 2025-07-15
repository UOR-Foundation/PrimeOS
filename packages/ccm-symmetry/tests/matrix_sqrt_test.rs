//! Test for matrix square root implementation

use ccm_symmetry::group::{SymmetryGroup, GroupElement};

#[test]
fn test_matrix_square_root_2x2() {
    // Create a 2x2 matrix group (SO(2))
    let group = SymmetryGroup::<f64>::generate(4).unwrap();
    
    // Create a rotation matrix for 60 degrees
    let theta = std::f64::consts::PI / 3.0;
    let cos_theta = theta.cos();
    let sin_theta = theta.sin();
    
    let rotation = GroupElement::new(vec![cos_theta, -sin_theta, sin_theta, cos_theta]);
    
    // Compute square root
    let sqrt_rotation = group.group_square_root(&rotation).unwrap();
    
    // Verify: sqrt * sqrt = original
    let squared = group.multiply(&sqrt_rotation, &sqrt_rotation).unwrap();
    
    for (a, b) in rotation.params.iter().zip(&squared.params) {
        assert!((a - b).abs() < 1e-10, "Square root verification failed");
    }
}

#[test]
fn test_matrix_square_root_3x3() {
    // Create a 3x3 matrix group (SO(3))
    let group = SymmetryGroup::<f64>::generate(9).unwrap();
    
    // Create a rotation around z-axis
    let theta = std::f64::consts::PI / 4.0;
    let c = theta.cos();
    let s = theta.sin();
    
    let rotation = GroupElement::new(vec![
        c, -s, 0.0,
        s,  c, 0.0,
        0.0, 0.0, 1.0
    ]);
    
    // Compute square root
    let sqrt_rotation = group.group_square_root(&rotation).unwrap();
    
    // Verify: sqrt * sqrt = original
    let squared = group.multiply(&sqrt_rotation, &sqrt_rotation).unwrap();
    
    for (a, b) in rotation.params.iter().zip(&squared.params) {
        assert!((a - b).abs() < 1e-10, "Square root verification failed");
    }
}

#[test]
fn test_matrix_square_root_positive_definite() {
    // Create a 3x3 positive definite matrix
    let group = SymmetryGroup::<f64>::generate(9).unwrap();
    
    // Create a positive definite matrix: A = B^T * B + I
    let b = vec![
        1.0, 0.5, 0.3,
        0.0, 1.0, 0.2,
        0.0, 0.0, 1.0
    ];
    
    // Compute B^T * B
    let mut pd_matrix = vec![0.0; 9];
    for i in 0..3 {
        for j in 0..3 {
            let mut sum = 0.0;
            for k in 0..3 {
                sum += b[k * 3 + i] * b[k * 3 + j];
            }
            pd_matrix[i * 3 + j] = sum;
        }
    }
    
    // Add identity to ensure positive definiteness
    for i in 0..3 {
        pd_matrix[i * 3 + i] += 1.0;
    }
    
    let pd_element = GroupElement::new(pd_matrix);
    
    // Compute square root
    let sqrt_element = group.group_square_root(&pd_element).unwrap();
    
    // Verify: sqrt * sqrt = original
    let squared = group.multiply(&sqrt_element, &sqrt_element).unwrap();
    
    for (a, b) in pd_element.params.iter().zip(&squared.params) {
        assert!((a - b).abs() < 1e-6, "Square root verification failed for positive definite matrix");
    }
}

#[test]
fn test_matrix_square_root_4x4() {
    // Create a 4x4 matrix group
    let group = SymmetryGroup::<f64>::generate(16).unwrap();
    
    // Create a simple positive definite matrix
    let matrix = vec![
        2.0, 0.5, 0.0, 0.0,
        0.5, 2.0, 0.0, 0.0,
        0.0, 0.0, 3.0, 0.2,
        0.0, 0.0, 0.2, 3.0
    ];
    
    let element = GroupElement::new(matrix);
    
    // Compute square root
    let sqrt_element = group.group_square_root(&element).unwrap();
    
    // Verify: sqrt * sqrt = original
    let squared = group.multiply(&sqrt_element, &sqrt_element).unwrap();
    
    for (a, b) in element.params.iter().zip(&squared.params) {
        assert!((a - b).abs() < 1e-6, "Square root verification failed for 4x4 matrix");
    }
}

#[test]
fn test_matrix_square_root_identity() {
    // Test that sqrt(I) = I
    let group = SymmetryGroup::<f64>::generate(9).unwrap();
    
    let identity = group.identity();
    let sqrt_identity = group.group_square_root(&identity).unwrap();
    
    for (a, b) in identity.params.iter().zip(&sqrt_identity.params) {
        assert!((a - b).abs() < 1e-10, "Square root of identity should be identity");
    }
}