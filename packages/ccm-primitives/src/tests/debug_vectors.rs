//! Debug test vector file format

#[cfg(test)]
mod tests {
    use std::fs::File;
    use std::io::Read;

    #[test]
    fn debug_test_vector_file() {
        let mut file =
            File::open("tests/data/bjc_test_vectors.bin").expect("Failed to open test vector file");

        let mut buffer = vec![0u8; 200];
        let bytes_read = file.read(&mut buffer).expect("Failed to read file");

        println!("First 200 bytes of test vector file:");
        for (i, chunk) in buffer[..bytes_read].chunks(16).enumerate() {
            print!("{:04x}: ", i * 16);
            for byte in chunk {
                print!("{:02x} ", byte);
            }
            print!("  ");
            for byte in chunk {
                if byte.is_ascii_graphic() {
                    print!("{}", *byte as char);
                } else {
                    print!(".");
                }
            }
            println!();
        }

        // Parse header
        println!("\nHeader:");
        println!(
            "  Magic: {}{}{}{}",
            buffer[0] as char, buffer[1] as char, buffer[2] as char, buffer[3] as char
        );
        println!("  Version: {}", buffer[4]);
        println!("  N count: {}", buffer[5]);

        // Parse first test set
        println!("\nFirst test set:");
        let mut offset = 8;
        println!("  n: {}", buffer[offset]);
        offset += 1;
        println!("  alpha len: {}", buffer[offset]);
        offset += 1;

        // Skip alpha values
        let alpha_len = buffer[offset - 1] as usize;
        offset += alpha_len * 8;

        // Vector count
        let vector_count = u32::from_be_bytes([
            buffer[offset],
            buffer[offset + 1],
            buffer[offset + 2],
            buffer[offset + 3],
        ]);
        println!("  Vector count: {}", vector_count);
        offset += 4;

        // First test case
        println!("\nFirst test case:");
        println!("  n: {}", buffer[offset]);
        println!("  log2_k: {}", buffer[offset + 1]);
        let input_len = u16::from_be_bytes([buffer[offset + 2], buffer[offset + 3]]);
        let packet_len = u16::from_be_bytes([buffer[offset + 4], buffer[offset + 5]]);
        println!("  input_len: {}", input_len);
        println!("  packet_len: {}", packet_len);

        offset += 6;
        println!("  Input: {:02x}", buffer[offset]);
        offset += input_len as usize;

        println!("  Packet bytes:");
        for i in 0..packet_len.min(20) {
            print!("{:02x} ", buffer[offset + i as usize]);
        }
        println!();
    }
}
