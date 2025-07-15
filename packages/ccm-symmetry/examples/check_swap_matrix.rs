//! Check the swap matrix properties

fn main() {
    let rotation: Vec<f64> = vec![
        0.0, 1.0, 0.0,
        1.0, 0.0, 0.0,
        0.0, 0.0, 1.0
    ];
    
    println!("Matrix:");
    for i in 0..3 {
        println!("[{:8.5}, {:8.5}, {:8.5}]", 
            rotation[i*3], rotation[i*3+1], rotation[i*3+2]);
    }
    
    // Compute trace
    let trace = rotation[0] + rotation[4] + rotation[8];
    println!("\nTrace: {}", trace);
    println!("For SO(3), trace = 1 + 2cos(θ)");
    println!("So 2cos(θ) = trace - 1 = {}", trace - 1.0);
    println!("cos(θ) = {}", (trace - 1.0) / 2.0);
    
    // For θ = π, cos(θ) = -1, so trace should be -1
    // But our trace is 1, which means cos(θ) = 0, so θ = π/2
    
    println!("\nThis corresponds to θ = π/2 (90 degrees), not 180 degrees!");
    
    // Let's verify by computing R^2
    println!("\nComputing R^2:");
    let mut r_squared = vec![0.0; 9];
    for i in 0..3 {
        for j in 0..3 {
            let mut sum = 0.0;
            for k in 0..3 {
                sum += rotation[i * 3 + k] * rotation[k * 3 + j];
            }
            r_squared[i * 3 + j] = sum;
        }
    }
    
    println!("R^2:");
    for i in 0..3 {
        println!("[{:8.5}, {:8.5}, {:8.5}]", 
            r_squared[i*3], r_squared[i*3+1], r_squared[i*3+2]);
    }
    
    // Check if R^2 = I (which would mean R is a 180-degree rotation)
    let mut is_180 = true;
    for i in 0..3 {
        for j in 0..3 {
            let expected = if i == j { 1.0 } else { 0.0 };
            if (r_squared[i * 3 + j] - expected).abs() > 1e-10_f64 {
                is_180 = false;
            }
        }
    }
    
    if is_180 {
        println!("\nR^2 = I, so this IS a 180-degree rotation!");
    } else {
        println!("\nR^2 != I, so this is NOT a 180-degree rotation!");
    }
    
    // The issue is that this matrix swaps x and y, which is indeed a 180-degree
    // rotation, but around the axis (1,1,0)/sqrt(2), not around z.
    
    // Let's find the rotation axis
    // For a rotation matrix, the axis is the eigenvector with eigenvalue 1
    println!("\nFinding rotation axis...");
    
    // For this specific matrix, we can see that:
    // R * [1, 1, 0]^T = [1, 1, 0]^T
    let axis = vec![1.0, 1.0, 0.0];
    let mut r_axis = vec![0.0; 3];
    for i in 0..3 {
        for j in 0..3 {
            r_axis[i] += rotation[i * 3 + j] * axis[j];
        }
    }
    
    println!("R * [1, 1, 0] = [{}, {}, {}]", r_axis[0], r_axis[1], r_axis[2]);
    
    // Normalize the axis
    let norm = (axis[0] * axis[0] + axis[1] * axis[1] + axis[2] * axis[2]).sqrt();
    println!("\nRotation axis (normalized): [{:.5}, {:.5}, {:.5}]", 
        axis[0]/norm, axis[1]/norm, axis[2]/norm);
}