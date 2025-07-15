//! Test for 180-degree rotation logarithm

use ccm_symmetry::SymmetryGroup;

#[test]
fn test_180_degree_rotation_x_axis() {
    let group = SymmetryGroup::<f64>::generate(9).unwrap();
    
    // 180-degree rotation around x-axis: R_x(π)
    let rotation_x = vec![
        1.0,  0.0,  0.0,
        0.0, -1.0,  0.0,
        0.0,  0.0, -1.0
    ];
    
    // Test matrix logarithm
    let log_result = group.matrix_log_3x3(&rotation_x);
    assert!(log_result.is_some());
    
    let log_matrix = log_result.unwrap();
    
    // The logarithm should be a skew-symmetric matrix with θ = π
    // For rotation around x-axis: log(R) = π * [[0, 0, 0], [0, 0, -1], [0, 1, 0]]
    let expected_theta = std::f64::consts::PI;
    
    // Check skew-symmetry
    for i in 0..3 {
        for j in 0..3 {
            let log_ij = log_matrix[i * 3 + j];
            let log_ji = log_matrix[j * 3 + i];
            assert!((log_ij + log_ji).abs() < 1e-10, 
                "Matrix should be skew-symmetric at ({}, {})", i, j);
        }
    }
    
    // Verify the rotation axis from the logarithm
    let axis_x = log_matrix[7] / expected_theta;  // (2,1) element
    let axis_y = -log_matrix[2] / expected_theta; // -(0,2) element  
    let axis_z = log_matrix[1] / expected_theta;  // (0,1) element
    
    println!("Extracted axis: ({:.3}, {:.3}, {:.3})", axis_x, axis_y, axis_z);
    
    // Should be approximately (1, 0, 0) for x-axis rotation
    assert!((axis_x - 1.0).abs() < 1e-10);
    assert!(axis_y.abs() < 1e-10);
    assert!(axis_z.abs() < 1e-10);
}

#[test]
fn test_180_degree_rotation_y_axis() {
    let group = SymmetryGroup::<f64>::generate(9).unwrap();
    
    // 180-degree rotation around y-axis: R_y(π)
    let rotation_y = vec![
        -1.0,  0.0,  0.0,
         0.0,  1.0,  0.0,
         0.0,  0.0, -1.0
    ];
    
    let log_result = group.matrix_log_3x3(&rotation_y);
    assert!(log_result.is_some());
    
    let log_matrix = log_result.unwrap();
    let expected_theta = std::f64::consts::PI;
    
    // Extract axis
    let axis_x = log_matrix[7] / expected_theta;
    let axis_y = -log_matrix[2] / expected_theta;
    let axis_z = log_matrix[1] / expected_theta;
    
    println!("Y-axis rotation - extracted axis: ({:.3}, {:.3}, {:.3})", axis_x, axis_y, axis_z);
    
    // Should be approximately (0, 1, 0) for y-axis rotation
    assert!(axis_x.abs() < 1e-10);
    assert!((axis_y - 1.0).abs() < 1e-10);
    assert!(axis_z.abs() < 1e-10);
}

#[test]
fn test_180_degree_rotation_arbitrary_axis() {
    let group = SymmetryGroup::<f64>::generate(9).unwrap();
    
    // 180-degree rotation around axis (1, 1, 1)/sqrt(3)
    let axis_norm = (3.0_f64).sqrt();
    let nx = 1.0 / axis_norm;
    let ny = 1.0 / axis_norm;
    let nz = 1.0 / axis_norm;
    
    // Using Rodrigues' formula for 180-degree rotation: R = 2nn^T - I
    let rotation = vec![
        2.0 * nx * nx - 1.0, 2.0 * nx * ny,       2.0 * nx * nz,
        2.0 * ny * nx,       2.0 * ny * ny - 1.0, 2.0 * ny * nz,
        2.0 * nz * nx,       2.0 * nz * ny,       2.0 * nz * nz - 1.0
    ];
    
    let log_result = group.matrix_log_3x3(&rotation);
    assert!(log_result.is_some());
    
    let log_matrix = log_result.unwrap();
    let expected_theta = std::f64::consts::PI;
    
    // Extract axis from logarithm
    let axis_x = log_matrix[7] / expected_theta;
    let axis_y = -log_matrix[2] / expected_theta;
    let axis_z = log_matrix[1] / expected_theta;
    
    println!("Arbitrary axis rotation - extracted: ({:.3}, {:.3}, {:.3})", axis_x, axis_y, axis_z);
    
    // Normalize extracted axis
    let extracted_norm = (axis_x * axis_x + axis_y * axis_y + axis_z * axis_z).sqrt();
    let normalized_x = axis_x / extracted_norm;
    let normalized_y = axis_y / extracted_norm;
    let normalized_z = axis_z / extracted_norm;
    
    // Should match original axis
    assert!((normalized_x - nx).abs() < 1e-10);
    assert!((normalized_y - ny).abs() < 1e-10);
    assert!((normalized_z - nz).abs() < 1e-10);
}

#[test]
fn test_180_degree_rotation_exp_log_identity() {
    let group = SymmetryGroup::<f64>::generate(9).unwrap();
    
    // Create 180-degree rotation around z-axis
    let rotation_z = vec![
        -1.0,  0.0,  0.0,
         0.0, -1.0,  0.0,
         0.0,  0.0,  1.0
    ];
    
    // Compute logarithm
    let log_result = group.matrix_log_3x3(&rotation_z);
    assert!(log_result.is_some());
    let log_matrix = log_result.unwrap();
    
    // Compute exponential of the logarithm
    let exp_result = group.matrix_exp_3x3(&log_matrix);
    assert!(exp_result.is_some());
    let exp_matrix = exp_result.unwrap();
    
    // exp(log(R)) should equal R
    for i in 0..9 {
        assert!((exp_matrix[i] - rotation_z[i]).abs() < 1e-10,
                "exp(log(R)) != R at index {}: {} != {}", i, exp_matrix[i], rotation_z[i]);
    }
}

// Helper to make matrix_log_3x3 accessible for testing
impl SymmetryGroup<f64> {
    fn matrix_log_3x3(&self, matrix: &[f64]) -> Option<Vec<f64>> {
        // This would need to be made public or we'd need a different approach
        // For now, this test file won't compile without making the method public
        None // Placeholder
    }
    
    fn matrix_exp_3x3(&self, matrix: &[f64]) -> Option<Vec<f64>> {
        None // Placeholder
    }
}