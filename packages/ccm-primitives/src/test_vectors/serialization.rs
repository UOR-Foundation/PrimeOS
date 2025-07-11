//! Binary and JSON serialization for test vectors

use super::{BinaryHeader, BinaryTestCase, TestVector, TestVectorSet};
use crate::{Float, FloatEncoding};

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::vec::Vec;

#[cfg(feature = "std")]
use std::{
    io::{Read, Write},
    vec::Vec,
};

/// Magic bytes for test vector files
pub const MAGIC: [u8; 4] = *b"BJCT"; // BJC Test

/// Current version of the test vector format
pub const VERSION: u8 = 1;

/// Write test vectors to binary format
#[cfg(feature = "std")]
pub fn write_binary<P: Float + FloatEncoding, W: Write>(
    writer: &mut W,
    test_sets: &[TestVectorSet<P>],
) -> std::io::Result<()> {
    // Write header
    let header = BinaryHeader {
        magic: MAGIC,
        version: VERSION,
        n_count: test_sets.len() as u8,
        reserved: [0, 0],
    };

    writer.write_all(&header.magic)?;
    writer.write_all(&[header.version])?;
    writer.write_all(&[header.n_count])?;
    writer.write_all(&header.reserved)?;

    // Write each test set
    for set in test_sets {
        // Write n value
        writer.write_all(&[set.n])?;

        // Write alpha vector length
        writer.write_all(&[set.alpha.len() as u8])?;

        // Write alpha values (as f64)
        for i in 0..set.alpha.len() {
            let value = set.alpha[i].to_f64().unwrap_or(0.0);
            writer.write_all(&value.to_be_bytes())?;
        }

        // Write number of test vectors
        let vector_count = set.vectors.len() as u32;
        writer.write_all(&vector_count.to_be_bytes())?;

        // Write each test vector
        for vector in &set.vectors {
            write_test_case(writer, vector)?;
        }
    }

    Ok(())
}

/// Write a single test case
#[cfg(feature = "std")]
fn write_test_case<P: Float, W: Write>(
    writer: &mut W,
    vector: &TestVector<P>,
) -> std::io::Result<()> {
    // Serialize packet to bytes
    let packet_bytes = serialize_packet(&vector.expected_packet);

    let test_case = BinaryTestCase {
        n: vector.n,
        log2_k: (vector.k as f64).log2() as u8,
        input_len: vector.input.len() as u16,
        packet_len: packet_bytes.len() as u16,
    };

    // Write test case header
    writer.write_all(&[test_case.n])?;
    writer.write_all(&[test_case.log2_k])?;
    writer.write_all(&test_case.input_len.to_be_bytes())?;
    writer.write_all(&test_case.packet_len.to_be_bytes())?;

    // Write input bytes
    writer.write_all(&vector.input)?;

    // Write packet bytes
    writer.write_all(&packet_bytes)?;

    // Write description length and bytes
    let desc_bytes = vector.description.as_bytes();
    writer.write_all(&[desc_bytes.len() as u8])?;
    writer.write_all(desc_bytes)?;

    Ok(())
}

/// Deserialize bytes to BjcPacket
fn deserialize_packet(bytes: &[u8]) -> std::io::Result<crate::BjcPacket> {
    if bytes.len() < 6 {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "Packet too short",
        ));
    }

    // Check magic
    if &bytes[0..3] != b"BJC" {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "Invalid packet magic",
        ));
    }

    let n_bits = bytes[3];
    let log2_k = bytes[4];

    // Determine r_min size - packet stores actual n, not marked with binary128 flag
    let r_min_size = 8; // For now, all our test n values use 8 bytes

    if bytes.len() < 5 + r_min_size + 1 {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!(
                "Packet too short: need {} bytes, got {}",
                5 + r_min_size + 1,
                bytes.len()
            ),
        ));
    }

    let r_min = bytes[5..5 + r_min_size].to_vec();
    let flips = bytes[5 + r_min_size];

    let mut offset = 6 + r_min_size;

    // Read page if k > 1
    let page = if log2_k > 0 {
        let page_bytes = log2_k.div_ceil(8) as usize;
        if bytes.len() < offset + page_bytes {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Packet too short for page",
            ));
        }
        let page = bytes[offset..offset + page_bytes].to_vec();
        offset += page_bytes;
        page
    } else {
        Vec::new()
    };

    // Check for hash (if remaining bytes = 32)
    let hash = if bytes.len() - offset == 32 {
        let mut hash_array = [0u8; 32];
        hash_array.copy_from_slice(&bytes[offset..offset + 32]);
        Some(hash_array)
    } else {
        None
    };

    Ok(crate::BjcPacket {
        n_bits,
        log2_k,
        r_min,
        flips,
        page,
        hash,
    })
}

/// Serialize a BjcPacket to bytes
fn serialize_packet(packet: &crate::BjcPacket) -> Vec<u8> {
    let mut bytes = Vec::new();

    // Magic bytes (BJC or BJC0)
    bytes.extend_from_slice(b"BJC");

    // n_bits
    bytes.push(packet.n_bits);

    // log2_k
    bytes.push(packet.log2_k);

    // r_min bytes
    bytes.extend_from_slice(&packet.r_min);

    // flips
    bytes.push(packet.flips);

    // page (if k > 1)
    if !packet.page.is_empty() {
        bytes.extend_from_slice(&packet.page);
    }

    // hash (if present)
    if let Some(hash) = &packet.hash {
        bytes.extend_from_slice(hash);
    }

    bytes
}

/// Read test vectors from binary format
#[cfg(feature = "std")]
pub fn read_binary<R: Read>(reader: &mut R) -> std::io::Result<Vec<TestVectorSet<f64>>> {
    let mut header_bytes = [0u8; 8];
    reader.read_exact(&mut header_bytes)?;

    // Verify magic
    if &header_bytes[0..4] != b"BJCT" {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "Invalid magic bytes",
        ));
    }

    let version = header_bytes[4];
    if version != VERSION {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!("Unsupported version: {version}"),
        ));
    }

    let n_count = header_bytes[5];
    let mut test_sets = Vec::new();

    for _ in 0..n_count {
        // Read n value
        let mut n_byte = [0u8];
        reader.read_exact(&mut n_byte)?;
        let n = n_byte[0];

        // Read alpha vector
        let mut alpha_len_byte = [0u8];
        reader.read_exact(&mut alpha_len_byte)?;
        let alpha_len = alpha_len_byte[0] as usize;

        let mut alpha_values = Vec::new();
        for _ in 0..alpha_len {
            let mut value_bytes = [0u8; 8];
            reader.read_exact(&mut value_bytes)?;
            alpha_values.push(f64::from_be_bytes(value_bytes));
        }

        let alpha = crate::AlphaVec::try_from(alpha_values).map_err(|e| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("Invalid alpha: {e:?}"),
            )
        })?;

        // Read vector count
        let mut count_bytes = [0u8; 4];
        reader.read_exact(&mut count_bytes)?;
        let vector_count = u32::from_be_bytes(count_bytes) as usize;

        // Read test vectors
        let mut vectors = Vec::new();
        for _ in 0..vector_count {
            // Read test case header
            let mut header = [0u8; 6];
            reader.read_exact(&mut header)?;

            let n = header[0];
            let log2_k = header[1];
            let input_len = u16::from_be_bytes([header[2], header[3]]) as usize;
            let packet_len = u16::from_be_bytes([header[4], header[5]]) as usize;

            // Read input bytes
            let mut input = vec![0u8; input_len];
            reader.read_exact(&mut input)?;

            // Read packet bytes
            let mut packet_bytes = vec![0u8; packet_len];
            reader.read_exact(&mut packet_bytes)?;

            // Read description
            let mut desc_len = [0u8];
            reader.read_exact(&mut desc_len)?;
            let mut desc_bytes = vec![0u8; desc_len[0] as usize];
            reader.read_exact(&mut desc_bytes)?;
            let description = std::str::from_utf8(&desc_bytes).map_err(|_| {
                std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    "Invalid UTF-8 in description",
                )
            })?;

            // Deserialize packet
            let packet = deserialize_packet(&packet_bytes)?;

            vectors.push(crate::test_vectors::TestVector {
                n,
                input,
                alpha: alpha.clone(),
                k: 1 << log2_k,
                expected_packet: packet,
                description: match description {
                    "All zeros" => "All zeros",
                    "All ones" => "All ones",
                    "Alternating bits (0xAA...)" => "Alternating bits (0xAA...)",
                    "Klein group edge (last 2 bits set)" => "Klein group edge (last 2 bits set)",
                    "Minimum resonance pattern" => "Minimum resonance pattern",
                    "Maximum resonance pattern" => "Maximum resonance pattern",
                    "Single bit pattern" => "Single bit pattern",
                    "Power of 2 pattern" => "Power of 2 pattern",
                    "Exhaustive coverage" => "Exhaustive coverage",
                    "Random test vector" => "Random test vector",
                    _ => "Unknown pattern",
                },
            });
        }

        test_sets.push(TestVectorSet { n, alpha, vectors });
    }

    Ok(test_sets)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(feature = "std")]
    fn test_binary_header_serialization() {
        let mut buffer = Vec::new();
        let test_sets: Vec<crate::test_vectors::TestVectorSet<f64>> = vec![];

        write_binary(&mut buffer, &test_sets).unwrap();

        // Check header
        assert_eq!(&buffer[0..4], b"BJCT");
        assert_eq!(buffer[4], VERSION);
        assert_eq!(buffer[5], 0); // n_count
    }
}
