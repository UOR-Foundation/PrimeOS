//! Verify rotation matrix properties

fn main() {
    // 180-degree rotation around (1,1,0)/sqrt(2)
    let sqrt2 = 2.0_f64.sqrt();
    let nx = 1.0 / sqrt2;
    let ny = 1.0 / sqrt2;
    let nz = 0.0;
    
    println!("Axis: ({}, {}, {})", nx, ny, nz);
    
    // Compute 2nn^T
    println!("\n2nn^T:");
    for i in 0..3 {
        for j in 0..3 {
            let n = [nx, ny, nz];
            let val = 2.0 * n[i] * n[j];
            print!("{:8.5} ", val);
        }
        println!();
    }
    
    // Compute 2nn^T - I
    println!("\n2nn^T - I (should be the rotation matrix):");
    let rotation = vec![
        2.0 * nx * nx - 1.0, 2.0 * nx * ny,       2.0 * nx * nz,
        2.0 * ny * nx,       2.0 * ny * ny - 1.0, 2.0 * ny * nz,
        2.0 * nz * nx,       2.0 * nz * ny,       2.0 * nz * nz - 1.0
    ];
    
    for i in 0..3 {
        for j in 0..3 {
            print!("{:8.5} ", rotation[i * 3 + j]);
        }
        println!();
    }
    
    // Manually compute determinant using rule of Sarrus
    let a = rotation[0] * (rotation[4] * rotation[8] - rotation[5] * rotation[7]);
    let b = rotation[1] * (rotation[5] * rotation[6] - rotation[3] * rotation[8]);
    let c = rotation[2] * (rotation[3] * rotation[7] - rotation[4] * rotation[6]);
    let det = a - b + c;
    
    println!("\nDeterminant calculation:");
    println!("a = {} * ({} * {} - {} * {}) = {}", rotation[0], rotation[4], rotation[8], rotation[5], rotation[7], a);
    println!("b = {} * ({} * {} - {} * {}) = {}", rotation[1], rotation[5], rotation[6], rotation[3], rotation[8], b);
    println!("c = {} * ({} * {} - {} * {}) = {}", rotation[2], rotation[3], rotation[7], rotation[4], rotation[6], c);
    println!("det = a - b + c = {} - {} + {} = {}", a, b, c, det);
    
    // The issue is that n = (1/√2, 1/√2, 0) gives this specific matrix:
    // [0, 1, 0]
    // [1, 0, 0]  
    // [0, 0, -1]
    // which has det = -1
    
    println!("\nThis is actually a reflection (det = -1), not a rotation!");
    println!("For a 180-degree rotation, we need a proper rotation axis.");
    
    // Let's use a different test case: 180-degree rotation around z-axis
    println!("\n=== 180-degree rotation around z-axis ===");
    let rot_z = vec![
        -1.0, 0.0, 0.0,
        0.0, -1.0, 0.0,
        0.0, 0.0, 1.0
    ];
    
    for i in 0..3 {
        for j in 0..3 {
            print!("{:8.5} ", rot_z[i * 3 + j]);
        }
        println!();
    }
    
    let det_z = rot_z[0] * (rot_z[4] * rot_z[8] - rot_z[5] * rot_z[7])
              - rot_z[1] * (rot_z[3] * rot_z[8] - rot_z[5] * rot_z[6])
              + rot_z[2] * (rot_z[3] * rot_z[7] - rot_z[4] * rot_z[6]);
    println!("Determinant: {}", det_z);
}