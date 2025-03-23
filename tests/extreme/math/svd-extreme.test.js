/**
 * PrimeOS Extreme Tests - SVD Extreme Values
 * 
 * Tests for singular value decomposition under extreme numerical conditions.
 */

const Prime = require('../../../src/mathematics.js');
const { Assertions, Setup, Fixtures } = require('../../utils');

// Configure environment for extreme testing
Setup.configureExtendedPrecision();

describe('SVD Extreme Values', () => {
  beforeAll(() => {
    // Enable extended precision mode for all tests in this suite
    process.env.EXTENDED_PRECISION = 'true';
  });

  describe('SVD with Extreme Values', () => {
    test('computes SVD for matrix with extremely large values', () => {
      // Create a matrix with extremely large values but low condition number
      const matrix = [
        [1e15, 0],
        [0, 2e15]
      ];
      
      // Perform SVD
      const { U, S, V } = Prime.Math.Matrix.svd(matrix);
      
      // Verify dimensions
      expect(U.length).toBe(2);
      expect(U[0].length).toBe(2);
      expect(S.length).toBe(2);
      expect(V.length).toBe(2);
      expect(V[0].length).toBe(2);
      
      // Verify singular values
      Assertions.assertAdaptivePrecision(S[0], 2e15, 1e5);
      Assertions.assertAdaptivePrecision(S[1], 1e15, 1e5);
      
      // Verify orthogonality of U and V
      const UTU = Prime.Math.Matrix.multiply(
        Prime.Math.Matrix.transpose(U),
        U
      );
      
      const VTV = Prime.Math.Matrix.multiply(
        Prime.Math.Matrix.transpose(V),
        V
      );
      
      // Check that U'U and V'V are approximately identity matrices
      Assertions.assertAdaptivePrecision(UTU[0][0], 1, 1e-10);
      Assertions.assertAdaptivePrecision(UTU[0][1], 0, 1e-10);
      Assertions.assertAdaptivePrecision(UTU[1][0], 0, 1e-10);
      Assertions.assertAdaptivePrecision(UTU[1][1], 1, 1e-10);
      
      Assertions.assertAdaptivePrecision(VTV[0][0], 1, 1e-10);
      Assertions.assertAdaptivePrecision(VTV[0][1], 0, 1e-10);
      Assertions.assertAdaptivePrecision(VTV[1][0], 0, 1e-10);
      Assertions.assertAdaptivePrecision(VTV[1][1], 1, 1e-10);
    });
    
    test('computes SVD for matrix with extremely small values', () => {
      // Create a matrix with extremely small values
      const matrix = [
        [1e-15, 2e-15],
        [3e-15, 4e-15]
      ];
      
      // Perform SVD
      const { U, S, V } = Prime.Math.Matrix.svd(matrix);
      
      // Verify dimensions
      expect(U.length).toBe(2);
      expect(U[0].length).toBe(2);
      expect(S.length).toBe(2);
      expect(V.length).toBe(2);
      expect(V[0].length).toBe(2);
      
      // Verify the reconstruction of the original matrix
      const diagonalS = Prime.Math.Matrix.diag(S);
      const reconstructed = Prime.Math.Matrix.multiply(
        Prime.Math.Matrix.multiply(U, diagonalS),
        Prime.Math.Matrix.transpose(V)
      );
      
      // Compare with original matrix using adaptive precision
      for (let i = 0; i < matrix.length; i++) {
        for (let j = 0; j < matrix[0].length; j++) {
          Assertions.assertAdaptivePrecision(
            reconstructed[i][j],
            matrix[i][j],
            1e-25
          );
        }
      }
    });
    
    test('computes SVD for ill-conditioned matrix', () => {
      // Create an ill-conditioned matrix (one singular value much smaller than the other)
      const matrix = [
        [1, 0],
        [0, 1e-10]
      ];
      
      // Perform SVD
      const { U, S, V } = Prime.Math.Matrix.svd(matrix);
      
      // Verify singular values
      Assertions.assertAdaptivePrecision(S[0], 1, 1e-10);
      Assertions.assertAdaptivePrecision(S[1], 1e-10, 1e-15);
      
      // Verify the reconstruction accuracy
      const diagonalS = Prime.Math.Matrix.diag(S);
      const reconstructed = Prime.Math.Matrix.multiply(
        Prime.Math.Matrix.multiply(U, diagonalS),
        Prime.Math.Matrix.transpose(V)
      );
      
      // Compare with original matrix using adaptive precision
      for (let i = 0; i < matrix.length; i++) {
        for (let j = 0; j < matrix[0].length; j++) {
          Assertions.assertAdaptivePrecision(
            reconstructed[i][j],
            matrix[i][j],
            1e-15
          );
        }
      }
    });
    
    test('handles matrices with zero singular values', () => {
      // Create a matrix with a zero singular value (rank deficient)
      const matrix = [
        [1, 2],
        [2, 4]  // second row is 2x first row
      ];
      
      // Perform SVD
      const { U, S, V } = Prime.Math.Matrix.svd(matrix);
      
      // Sort the singular values in descending order
      const sortedS = [...S].sort((a, b) => b - a);
      
      // The second singular value should be very close to zero
      expect(sortedS[0]).toBeGreaterThan(4);  // Largest singular value should be > 4
      expect(sortedS[1]).toBeLessThan(1e-10); // Smallest should be approximately 0
      
      // Verify nullspace properties (V[:,1] should be in nullspace)
      const nullspaceVector = [V[0][1], V[1][1]]; // Second column of V
      
      // Av should be approximately zero
      const result = [
        matrix[0][0] * nullspaceVector[0] + matrix[0][1] * nullspaceVector[1],
        matrix[1][0] * nullspaceVector[0] + matrix[1][1] * nullspaceVector[1]
      ];
      
      expect(Math.abs(result[0])).toBeLessThan(1e-10);
      expect(Math.abs(result[1])).toBeLessThan(1e-10);
    });
    
    test('handles matrices with mixed extreme values', () => {
      // Create a matrix with mixed extreme values
      const matrix = [
        [1e15, 1e-15],
        [1e-15, 1e15]
      ];
      
      // Perform SVD
      const { U, S, V } = Prime.Math.Matrix.svd(matrix);
      
      // Verify the singular values
      // Should be approximately 1e15 * sqrt(2) and 1e15 * sqrt(2)
      const expectedS1 = 1e15 * Math.sqrt(2);
      const expectedS2 = 1e15 * Math.sqrt(2);
      
      // Allow for some numerical error given the extreme values
      Assertions.assertAdaptivePrecision(S[0], expectedS1, 1e5);
      Assertions.assertAdaptivePrecision(S[1], expectedS2, 1e5);
      
      // Verify orthogonality is maintained even with extreme values
      const UTU = Prime.Math.Matrix.multiply(
        Prime.Math.Matrix.transpose(U),
        U
      );
      
      Assertions.assertAdaptivePrecision(UTU[0][0], 1, 1e-10);
      Assertions.assertAdaptivePrecision(Math.abs(UTU[0][1]), 0, 1e-10);
      Assertions.assertAdaptivePrecision(Math.abs(UTU[1][0]), 0, 1e-10);
      Assertions.assertAdaptivePrecision(UTU[1][1], 1, 1e-10);
    });
  });
  
  describe('SVD Catastrophic Cancellation', () => {
    test('avoids catastrophic cancellation in SVD computations', () => {
      // Create a matrix prone to catastrophic cancellation
      const epsilon = 1e-8;
      const matrix = [
        [1 + epsilon, 1],
        [1, 1 - epsilon]
      ];
      
      // The determinant is (1+ε)(1-ε) - 1 = -ε²
      // This is a small value that could be lost due to catastrophic cancellation
      
      // Perform SVD
      const { U, S, V } = Prime.Math.Matrix.svd(matrix);
      
      // Calculate the determinant from singular values
      // det(A) = Π(σᵢ) for square matrix
      const detFromSVD = S[0] * S[1];
      
      // Direct calculation (prone to cancellation)
      const directDet = matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0];
      
      // Both should be approximately ε²
      const expectedDet = epsilon * epsilon;
      
      // The SVD-based determinant should be more accurate
      const directDetError = Math.abs(directDet - expectedDet) / expectedDet;
      const svdDetError = Math.abs(detFromSVD - expectedDet) / expectedDet;
      
      // This tests whether SVD helps avoid catastrophic cancellation
      expect(svdDetError).toBeLessThanOrEqual(directDetError);
      
      // Both methods should still be reasonably accurate
      expect(directDetError).toBeLessThan(0.1); // Allow up to 10% error
      expect(svdDetError).toBeLessThan(0.1);    // Allow up to 10% error
    });
  });
  
  describe('SVD Performance with Extreme Values', () => {
    test('maintains reasonable performance with extreme values', () => {
      // Skip this test in CI environment
      if (process.env.CI) {
        return;
      }
      
      // Create a larger matrix with extreme values
      const n = 10; // 10x10 matrix
      const matrix = Array(n).fill().map(() => Array(n).fill(0));
      
      // Fill with extreme values in a structured way to maintain well-conditioning
      for (let i = 0; i < n; i++) {
        for (let j = 0; j < n; j++) {
          if (i === j) {
            // Diagonal has decreasing extreme values
            matrix[i][j] = 1e15 / Math.pow(10, i);
          } else if ((i + j) % 2 === 0) {
            // Even sum indices get medium values
            matrix[i][j] = 1e-5;
          } else {
            // Odd sum indices get small values
            matrix[i][j] = 1e-15;
          }
        }
      }
      
      // Measure the time to compute SVD
      const startTime = Date.now();
      const { U, S, V } = Prime.Math.Matrix.svd(matrix);
      const endTime = Date.now();
      const executionTime = endTime - startTime;
      
      // We're not setting hard limits on execution time, just verifying it completes
      // and produces valid results
      
      // Verify that results are valid
      expect(S.length).toBe(n);
      expect(U.length).toBe(n);
      expect(U[0].length).toBe(n);
      expect(V.length).toBe(n);
      expect(V[0].length).toBe(n);
      
      // Verify that the singular values are sorted in descending order
      for (let i = 0; i < S.length - 1; i++) {
        expect(S[i]).toBeGreaterThanOrEqual(S[i + 1]);
      }
      
      // Log the time taken (useful for performance monitoring)
      console.log(`SVD of ${n}x${n} matrix with extreme values took ${executionTime}ms`);
    });
  });
});