# Test Data Directory

This directory should contain the 256KB test vector suite from Appendix A of the CCM-BJC v1.0 specification.

## Expected Files

- `bjc_test_vectors.bin` - Binary test vectors (256KB)
- `bjc_test_vectors.json` - JSON format test vectors (optional)

## Format

Each test vector should include:
- Input bit pattern (raw)
- Alpha vector values
- Expected packet bytes
- Expected decoded output

The test vectors should cover all nominated n values: 3, 4, 8, 10, 16, 32, 64

## Current Status

The test vector files are not included in this repository. They should be obtained from the official CCM specification repository.