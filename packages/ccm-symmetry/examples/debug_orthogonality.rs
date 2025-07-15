//! Debug orthogonality check

fn main() {
    let rotation = vec![
        -0.33333, 0.66667, 0.66667,
        0.66667, -0.33333, 0.66667,
        0.66667, 0.66667, -0.33333
    ];
    
    println!("Rotation matrix:");
    for i in 0..3 {
        println!("Row {}: [{:8.5}, {:8.5}, {:8.5}]", i,
            rotation[i*3], rotation[i*3+1], rotation[i*3+2]);
    }
    
    println!("\nChecking R^T * R = I");
    println!("This means row i dot row j should give delta_ij");
    
    for i in 0..3 {
        for j in 0..3 {
            let mut sum = 0.0;
            for k in 0..3 {
                // Row i dot row j
                sum += rotation[i * 3 + k] * rotation[j * 3 + k];
            }
            let expected = if i == j { 1.0 } else { 0.0 };
            println!("Row {} · Row {} = {:8.5} (expected {})", i, j, sum, expected);
        }
    }
    
    println!("\nThe test was doing (incorrect):");
    for i in 0..3 {
        for j in 0..3 {
            let mut sum = 0.0;
            for k in 0..3 {
                // This is column i dot column j
                sum += rotation[k * 3 + i] * rotation[k * 3 + j];
            }
            let expected = if i == j { 1.0 } else { 0.0 };
            println!("Col {} · Col {} = {:8.5} (expected {})", i, j, sum, expected);
        }
    }
}