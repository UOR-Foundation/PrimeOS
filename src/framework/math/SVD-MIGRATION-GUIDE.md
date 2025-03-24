# SVD Migration Guide

This guide helps users migrate from the previous Singular Value Decomposition (SVD) implementation to the enhanced SVD implementation, which is now the default in PrimeOS.

## Overview of Changes

The enhanced SVD implementation offers:

- Better numerical stability for matrices with extreme values
- More detailed error information and recovery strategies
- Adaptive algorithm selection based on matrix characteristics
- Additional metadata about the computation

Most code using the previous SVD implementation should continue to work without changes, as the enhanced SVD maintains the same interface. However, there are some differences to be aware of.

## API Differences

### Input Format

The enhanced SVD accepts the same input formats as the previous implementation:

```javascript
// Both implementations accept:
SVD(matrix);                   // 2D array
SVD(matrix, options);          // 2D array with options
PrimeMath.svd(matrixObject);   // Matrix object
```

### Options

The enhanced SVD implementation offers additional options:

```javascript
// Previous implementation
const result = SVD(matrix, {
  thin: false,                // Whether to compute thin SVD
  useScaling: true,           // Whether to use scaling
  maxIterations: 100,         // Maximum iterations
  tolerance: 1e-10            // Convergence tolerance
});

// Enhanced implementation (adds more options)
const result = SVD(matrix, {
  algorithm: 'auto',           // 'jacobi', 'qr', 'powerIteration', or 'auto'
  thin: false,                 // Whether to compute thin SVD
  useScaling: true,            // Whether to use scaling
  maxIterations: 150,          // Maximum iterations (default increased)
  tolerance: 1e-14,            // Convergence tolerance (default increased)
  throwOnFallbackFailure: false // Whether to throw when all fallbacks fail
});
```

### Return Value

The basic decomposition result remains the same:

```javascript
const { U, S, V } = SVD(matrix);
```

However, the enhanced SVD returns additional information:

```javascript
const result = SVD(matrix);

// Basic decomposition (same as before)
const { U, S, V } = result;

// New information
const { 
  dimensions,    // Original matrix dimensions
  algorithm,     // Algorithm used for computation
  metadata       // Detailed metadata
} = result;

// Access metadata
console.log(`Condition number: ${metadata.estimatedConditionNumber}`);
console.log(`Algorithm used: ${algorithm}`);
```

### Matrix Format Differences

The previous SVD implementation returned S as a diagonal matrix. The enhanced implementation may return S as:

1. A diagonal matrix (preferred format)
2. A 1D array of singular values (for compatibility with some libraries)

To handle both formats:

```javascript
function useDecomposition(result) {
  const { U, S, V } = result;
  
  // Check if S is a 1D array or a diagonal matrix
  if (Array.isArray(S) && !Array.isArray(S[0])) {
    // S is a 1D array - convert to diagonal matrix if needed
    const diagonalS = createDiagonalMatrix(S);
    // Use diagonalS...
  } else {
    // S is already a diagonal matrix
    // Use S directly...
  }
}
```

## Error Handling Improvements

The enhanced SVD provides more detailed error information:

```javascript
// Previous implementation
try {
  const result = SVD(matrix);
} catch (error) {
  console.error(`Error: ${error.message}`);
  // Limited error information
}

// Enhanced implementation
try {
  const result = SVD(matrix);
} catch (error) {
  console.error(`Error: ${error.message}`);
  
  // Rich error context (if using enhanced error handling)
  if (error.context) {
    console.error(`Operation: ${error.context.operation}`);
    console.error(`Matrix dimensions: ${error.context.dimensions}`);
    console.error(`Dynamic range: ${error.context.dynamicRange}`);
    console.error(`Attempted algorithm: ${error.context.attemptedAlgorithm}`);
  }
}
```

## Common Migration Issues

### Issue: S Format Differences

**Symptom**: Code assuming S is always a diagonal matrix may fail.

**Solution**: Check the format of S before using it:

```javascript
function isSingularValueArray(S) {
  return Array.isArray(S) && !Array.isArray(S[0]);
}

function getDiagonalS(S) {
  if (isSingularValueArray(S)) {
    // Convert 1D array to diagonal matrix
    return S.map((value, i) => {
      const row = new Array(S.length).fill(0);
      row[i] = value;
      return row;
    });
  }
  return S; // Already a diagonal matrix
}
```

### Issue: Error Handling Changes

**Symptom**: Code catching specific error types may need adjustment.

**Solution**: Update error handling to use the enhanced error hierarchy:

```javascript
// Previous approach
try {
  const result = SVD(matrix);
} catch (error) {
  if (error.message.includes("singular")) {
    // Handle singularity...
  } else if (error.message.includes("dimension")) {
    // Handle dimension issues...
  }
}

// Enhanced approach
try {
  const result = SVD(matrix);
} catch (error) {
  if (error instanceof MatrixSingularityError) {
    // Handle singularity...
  } else if (error instanceof DimensionMismatchError) {
    // Handle dimension issues...
  } else if (error instanceof NumericalInstabilityError) {
    // Handle numerical instability...
  }
}
```

### Issue: Performance Differences

**Symptom**: The enhanced SVD may be slower for certain matrices, especially when handling extreme values.

**Solution**: Use the `algorithm` option to select the most appropriate algorithm for your specific use case:

```javascript
// For small matrices (≤ 32×32)
const result = SVD(matrix, { algorithm: 'jacobi' });

// For medium-sized, well-conditioned matrices (≤ 128×128)
const result = SVD(matrix, { algorithm: 'qr' });

// For larger matrices with high dynamic range
const result = SVD(matrix, { algorithm: 'powerIteration' });
```

## Testing Your Migration

When migrating to the enhanced SVD:

1. Run your existing tests to verify that results are within acceptable numerical precision
2. Test with edge cases, especially matrices with extreme values
3. Verify that error handling works correctly with the enhanced error information

## Using Both Implementations Simultaneously

If you need to use both implementations during migration:

```javascript
// Use legacy SVD implementation
const legacyResult = require('primeos/math/legacy').SVD(matrix);

// Use enhanced SVD implementation
const enhancedResult = require('primeos/math').SVD(matrix);
```

## Getting Help

If you encounter issues during migration, please:

1. Check the [Enhanced SVD Documentation](./ENHANCED-SVD-DOCUMENTATION.md)
2. Review the examples in the `examples/math/svd` directory
3. File an issue on the PrimeOS repository with detailed reproduction steps