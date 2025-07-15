//! Verify 180-degree rotation around (1,1,1)/sqrt(3)

fn main() {
    // 180-degree rotation around (1,1,1)/sqrt(3)
    let sqrt3 = 3.0_f64.sqrt();
    let nx = 1.0 / sqrt3;
    let ny = 1.0 / sqrt3;
    let nz = 1.0 / sqrt3;
    
    println!("Axis: ({}, {}, {})", nx, ny, nz);
    println!("Axis norm: {}", (nx*nx + ny*ny + nz*nz).sqrt());
    
    // Compute each element of R = 2nn^T - I
    println!("\nComputing R = 2nn^T - I:");
    let r00 = 2.0 * nx * nx - 1.0;
    let r01 = 2.0 * nx * ny;
    let r02 = 2.0 * nx * nz;
    let r10 = 2.0 * ny * nx;
    let r11 = 2.0 * ny * ny - 1.0;
    let r12 = 2.0 * ny * nz;
    let r20 = 2.0 * nz * nx;
    let r21 = 2.0 * nz * ny;
    let r22 = 2.0 * nz * nz - 1.0;
    
    println!("r00 = 2*{:.5}*{:.5} - 1 = {:.5}", nx, nx, r00);
    println!("r11 = 2*{:.5}*{:.5} - 1 = {:.5}", ny, ny, r11);
    println!("r22 = 2*{:.5}*{:.5} - 1 = {:.5}", nz, nz, r22);
    
    let rotation = vec![r00, r01, r02, r10, r11, r12, r20, r21, r22];
    
    println!("\nRotation matrix:");
    for i in 0..3 {
        println!("[{:8.5}, {:8.5}, {:8.5}]", 
            rotation[i*3], rotation[i*3+1], rotation[i*3+2]);
    }
    
    // Manual determinant calculation
    let det = r00 * (r11 * r22 - r12 * r21)
            - r01 * (r10 * r22 - r12 * r20)
            + r02 * (r10 * r21 - r11 * r20);
            
    println!("\nDeterminant = {}", det);
    
    // Actually, let me compute this more carefully
    println!("\nDetailed determinant calculation:");
    let term1 = r00 * (r11 * r22 - r12 * r21);
    let term2 = r01 * (r10 * r22 - r12 * r20);
    let term3 = r02 * (r10 * r21 - r11 * r20);
    
    println!("term1 = {} * ({} * {} - {} * {}) = {}", r00, r11, r22, r12, r21, term1);
    println!("term2 = {} * ({} * {} - {} * {}) = {}", r01, r10, r22, r12, r20, term2);
    println!("term3 = {} * ({} * {} - {} * {}) = {}", r02, r10, r21, r11, r20, term3);
    println!("det = {} - {} + {} = {}", term1, term2, term3, det);
    
    // Let's verify with numerical values
    let n = 1.0 / sqrt3;
    println!("\nn = 1/sqrt(3) = {}", n);
    println!("2n^2 - 1 = {} - 1 = {}", 2.0 * n * n, 2.0 * n * n - 1.0);
    println!("2n^2 = {}", 2.0 * n * n);
    
    // Check if this is actually a rotation
    // For (1,1,1)/sqrt(3), we get:
    // R = 2/3 * [[1,1,1],[1,1,1],[1,1,1]] - I
    //   = [[2/3-1, 2/3, 2/3], [2/3, 2/3-1, 2/3], [2/3, 2/3, 2/3-1]]
    //   = [[-1/3, 2/3, 2/3], [2/3, -1/3, 2/3], [2/3, 2/3, -1/3]]
    
    println!("\nExpected matrix:");
    println!("[{:8.5}, {:8.5}, {:8.5}]", -1.0/3.0, 2.0/3.0, 2.0/3.0);
    println!("[{:8.5}, {:8.5}, {:8.5}]", 2.0/3.0, -1.0/3.0, 2.0/3.0);
    println!("[{:8.5}, {:8.5}, {:8.5}]", 2.0/3.0, 2.0/3.0, -1.0/3.0);
}