//! Trace determinant computation

fn main() {
    let matrix = vec![
        -0.33333, 0.66667, 0.66667,
        0.66667, -0.33333, 0.66667,
        0.66667, 0.66667, -0.33333
    ];
    
    println!("Matrix:");
    println!("[{:8.5}, {:8.5}, {:8.5}]", matrix[0], matrix[1], matrix[2]);
    println!("[{:8.5}, {:8.5}, {:8.5}]", matrix[3], matrix[4], matrix[5]);
    println!("[{:8.5}, {:8.5}, {:8.5}]", matrix[6], matrix[7], matrix[8]);
    
    // Det = a11(a22*a33 - a23*a32) - a12(a21*a33 - a23*a31) + a13(a21*a32 - a22*a31)
    
    println!("\nComputing determinant:");
    println!("a11 = matrix[0] = {}", matrix[0]);
    println!("a12 = matrix[1] = {}", matrix[1]);
    println!("a13 = matrix[2] = {}", matrix[2]);
    println!("a21 = matrix[3] = {}", matrix[3]);
    println!("a22 = matrix[4] = {}", matrix[4]);
    println!("a23 = matrix[5] = {}", matrix[5]);
    println!("a31 = matrix[6] = {}", matrix[6]);
    println!("a32 = matrix[7] = {}", matrix[7]);
    println!("a33 = matrix[8] = {}", matrix[8]);
    
    let term1_inner = matrix[4] * matrix[8] - matrix[5] * matrix[7];
    println!("\nterm1_inner = a22*a33 - a23*a32 = {} * {} - {} * {} = {}", 
        matrix[4], matrix[8], matrix[5], matrix[7], term1_inner);
    
    let a = matrix[0] * term1_inner;
    println!("a = a11 * term1_inner = {} * {} = {}", matrix[0], term1_inner, a);
    
    let term2_inner = matrix[5] * matrix[6] - matrix[3] * matrix[8];
    println!("\nterm2_inner = a23*a31 - a21*a33 = {} * {} - {} * {} = {}", 
        matrix[5], matrix[6], matrix[3], matrix[8], term2_inner);
    
    let b = matrix[1] * term2_inner;
    println!("b = a12 * term2_inner = {} * {} = {}", matrix[1], term2_inner, b);
    
    let term3_inner = matrix[3] * matrix[7] - matrix[4] * matrix[6];
    println!("\nterm3_inner = a21*a32 - a22*a31 = {} * {} - {} * {} = {}", 
        matrix[3], matrix[7], matrix[4], matrix[6], term3_inner);
    
    let c = matrix[2] * term3_inner;
    println!("c = a13 * term3_inner = {} * {} = {}", matrix[2], term3_inner, c);
    
    let det = a - b + c;
    println!("\ndet = a - b + c = {} - {} + {} = {}", a, b, c, det);
    
    println!("\nNote: b is negative, so -b is positive!");
    println!("det = {} - ({}) + {} = {} + {} + {} = {}", a, b, c, a, -b, c, a - b + c);
}