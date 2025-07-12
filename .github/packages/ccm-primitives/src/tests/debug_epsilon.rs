//! Debug epsilon and tolerance values

#[cfg(test)]
mod tests {
    #[test]
    fn debug_epsilon() {
        let epsilon = f64::EPSILON;
        println!("f64::EPSILON = {}", epsilon);
        println!("epsilon * 1000 = {}", epsilon * 1000.0);

        let sum = 687.1101183515111_f64;
        let expected = 687.110133051847_f64;
        let error = (sum - expected).abs();

        println!("Sum = {}", sum);
        println!("Expected = {}", expected);
        println!("Error = {}", error);
        println!("Error < epsilon * 1000? {}", error < epsilon * 1000.0);
        println!("Error < epsilon * 10000? {}", error < epsilon * 10000.0);
        println!("Error < epsilon * 100000? {}", error < epsilon * 100000.0);

        // Check relative error
        let relative_error = error / expected;
        println!("Relative error = {}", relative_error);
        println!("Relative error < 1e-10? {}", relative_error < 1e-10);
        println!("Relative error < 1e-8? {}", relative_error < 1e-8);
    }
}
