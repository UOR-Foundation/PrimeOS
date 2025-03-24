# Enhanced SVD Implementation Documentation

## Overview

The Enhanced SVD (Singular Value Decomposition) implementation provides a more robust and numerically stable algorithm for decomposing matrices, especially those with extreme values. This implementation is now the default for all SVD operations in PrimeOS.

## Features

- **Adaptive Algorithm Selection**: Automatically selects the most appropriate algorithm based on matrix characteristics:
  - Jacobi method for small matrices (≤ 32×32) and matrices with extreme values
  - QR method for medium-sized, well-conditioned matrices (≤ 128×128)
  - Power iteration for large matrices and those with high dynamic range

- **Extreme Value Handling**: Properly handles matrices with very large (> 1e100) or very small (< 1e-100) values through adaptive scaling and specialized algorithms

- **Comprehensive Error Handling**: Provides detailed error information and context to help diagnose and fix issues

- **Automatic Recovery**: Attempts multiple fallback strategies when the primary algorithm fails

- **Metadata**: Returns extensive metadata about the computation, including condition number estimates, algorithm used, and numerical stability metrics

## API

### Basic Usage

```javascript
const { SVD } = require('primeos/math');

// Simple usage with default options
const matrix = [[1, 2], [3, 4]];
const { U, S, V } = SVD(matrix);

// Usage with options
const result = SVD(matrix, {
  algorithm: 'jacobi',  // 'jacobi', 'qr', 'powerIteration', or 'auto'
  useScaling: true,     // Enable scaling for extreme values
  maxIterations: 150,   // Maximum iterations for convergence
  tolerance: 1e-14,     // Convergence tolerance
  thin: false           // Whether to compute thin SVD
});

// Access decomposition
const { U, S, V, metadata } = result;

// Access detailed metadata
console.log(`Algorithm used: ${metadata.algorithm}`);
console.log(`Condition number: ${metadata.estimatedConditionNumber}`);
```

### Options

| Option | Type | Default | Description |
|--------|------|---------|-------------|
| `algorithm` | string | 'auto' | Algorithm to use ('jacobi', 'qr', 'powerIteration', or 'auto') |
| `useScaling` | boolean | true | Whether to use scaling for extreme values |
| `maxIterations` | number | 150 | Maximum number of iterations for convergence |
| `tolerance` | number | 1e-14 | Convergence tolerance |
| `thin` | boolean | false | Whether to compute thin SVD |
| `throwOnFallbackFailure` | boolean | false | Whether to throw an error when all fallbacks fail |

### Return Value

The SVD function returns an object with the following properties:

- `U`: Left singular vectors (orthogonal matrix)
- `S`: Singular values (diagonal matrix)
- `V`: Right singular vectors (orthogonal matrix)
- `dimensions`: Original matrix dimensions
- `algorithm`: Algorithm used for computation
- `metadata`: Detailed information about the computation

#### Metadata

The `metadata` object contains:

- `dynamicRange`: Ratio of the largest to smallest non-zero values
- `needsScaling`: Whether scaling was applied
- `scaleFactor`: Scaling factor used (if any)
- `maxAbsValue`: Maximum absolute value in the original matrix
- `minNonZeroValue`: Minimum non-zero absolute value in the original matrix
- `estimatedConditionNumber`: Estimated condition number of the matrix

## Error Handling

The enhanced SVD implementation provides detailed error information through specialized error classes:

- `MatrixSingularityError`: Thrown when the matrix is singular or near-singular
- `NumericalInstabilityError`: Thrown when numerical instability is detected
- `ConvergenceError`: Thrown when the algorithm fails to converge
- `DimensionMismatchError`: Thrown when matrix dimensions are invalid
- `ValidationError`: Thrown when input validation fails

All errors include detailed context information to help diagnose and fix issues:

```javascript
try {
  const result = SVD(matrix);
} catch (error) {
  console.error(`Error: ${error.message}`);
  console.error(`Operation: ${error.context.operation}`);
  console.error(`Matrix dimensions: ${error.context.dimensions}`);
  console.error(`Dynamic range: ${error.context.dynamicRange}`);
}
```

## Performance Considerations

- For very large matrices (> 1000×1000), consider using the thin SVD option
- For matrices with extreme values, the enhanced SVD may be slower but more accurate
- The 'auto' algorithm selection provides a good balance between speed and accuracy

## Examples

### Handling Ill-Conditioned Matrices

```javascript
const { SVD } = require('primeos/math');

// Create an ill-conditioned matrix
const matrix = [
  [1e-8, 2e10],
  [3e-9, 4e-7]
];

// Use enhanced SVD with detailed metadata
const result = SVD(matrix, { useScaling: true });

console.log(`Condition number: ${result.metadata.estimatedConditionNumber}`);
console.log(`Algorithm used: ${result.algorithm}`);
console.log(`Scaling factor: ${result.metadata.scaleFactor}`);
```

### Reconstructing the Original Matrix

```javascript
const { SVD, Matrix } = require('primeos/math');

const matrix = [[1, 2], [3, 4]];
const { U, S, V } = SVD(matrix);

// Reconstruct the original matrix: A = U * S * V^T
const ST = Matrix.transpose(S);
const VT = Matrix.transpose(V);
const reconstructed = Matrix.multiply(U, Matrix.multiply(ST, VT));
```

## Migration from Previous SVD Implementation

See the [Migration Guide](./SVD-MIGRATION-GUIDE.md) for details on migrating from the previous SVD implementation.