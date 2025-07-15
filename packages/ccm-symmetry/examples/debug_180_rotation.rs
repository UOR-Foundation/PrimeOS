//! Debug 180-degree rotation

use ccm_symmetry::group::SymmetryGroup;

fn main() {
    // Test the construction of 180-degree rotation matrix
    let sqrt2 = 2.0_f64.sqrt();
    let nx = 1.0 / sqrt2;
    let ny = 1.0 / sqrt2;
    let nz = 0.0;
    
    println!("Axis: ({}, {}, {})", nx, ny, nz);
    println!("Axis norm: {}", (nx*nx + ny*ny + nz*nz).sqrt());
    
    // R = 2nn^T - I for 180-degree rotation
    let rotation = vec![
        2.0 * nx * nx - 1.0, 2.0 * nx * ny,       2.0 * nx * nz,
        2.0 * ny * nx,       2.0 * ny * ny - 1.0, 2.0 * ny * nz,
        2.0 * nz * nx,       2.0 * nz * ny,       2.0 * nz * nz - 1.0
    ];
    
    println!("\nRotation matrix:");
    for i in 0..3 {
        println!("[{:8.5}, {:8.5}, {:8.5}]", 
            rotation[i*3], rotation[i*3+1], rotation[i*3+2]);
    }
    
    // Check R^T * R = I by computing dot products of rows
    println!("\nOrthogonality check (R^T * R):");
    for i in 0..3 {
        for j in 0..3 {
            let mut sum = 0.0;
            for k in 0..3 {
                sum += rotation[i * 3 + k] * rotation[j * 3 + k];
            }
            let expected = if i == j { 1.0 } else { 0.0 };
            println!("Row {} · Row {} = {:8.5} (expected {})", i, j, sum, expected);
        }
    }
    
    // Check determinant
    let group = SymmetryGroup::<f64>::generate(9).unwrap();
    let det = group.compute_determinant(&rotation, 3).unwrap();
    println!("\nDeterminant: {}", det);
    
    // Check that R * axis = -axis (180-degree rotation property)
    let axis = vec![nx, ny, nz];
    let mut result = vec![0.0; 3];
    for i in 0..3 {
        for j in 0..3 {
            result[i] += rotation[i * 3 + j] * axis[j];
        }
    }
    println!("\nR * axis = [{:8.5}, {:8.5}, {:8.5}]", result[0], result[1], result[2]);
    println!("Expected: [{:8.5}, {:8.5}, {:8.5}]", -nx, -ny, -nz);
    
    // Verify this is indeed a 180-degree rotation
    // Trace(R) = 1 + 2*cos(θ), so for θ=π, trace = -1
    let trace = rotation[0] + rotation[4] + rotation[8];
    println!("\nTrace: {} (expected -1 for 180-degree rotation)", trace);
    
    // Now test the rotation in the actual test
    println!("\n=== Testing rotation from actual test ===");
    let test_rotation = vec![
        0.0, 1.0, 0.0,
        1.0, 0.0, 0.0,
        0.0, 0.0, -1.0
    ];
    
    println!("\nTest rotation matrix:");
    for i in 0..3 {
        println!("[{:8.5}, {:8.5}, {:8.5}]", 
            test_rotation[i*3], test_rotation[i*3+1], test_rotation[i*3+2]);
    }
    
    let is_valid = group.is_rotation_matrix_3x3(&test_rotation);
    println!("\nIs valid rotation matrix: {}", is_valid);
    
    if !is_valid {
        // Check what's wrong
        let test_det = group.compute_determinant(&test_rotation, 3).unwrap();
        println!("Determinant: {}", test_det);
        
        // Check orthogonality
        println!("\nOrthogonality check:");
        for i in 0..3 {
            for j in 0..3 {
                let mut sum = 0.0;
                for k in 0..3 {
                    sum += test_rotation[i * 3 + k] * test_rotation[j * 3 + k];
                }
                let expected = if i == j { 1.0 } else { 0.0 };
                println!("Row {} · Row {} = {:8.5} (expected {})", i, j, sum, expected);
            }
        }
    }
}