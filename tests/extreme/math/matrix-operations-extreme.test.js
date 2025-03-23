/**
 * PrimeOS Extreme Math Tests - Matrix Operations with Extreme Values
 * 
 * Consolidated tests for matrix operations with extreme values:
 * - SVD decomposition with extreme values
 * - LU decomposition with extreme values
 * - Matrix inversion with ill-conditioned matrices
 * - Matrix operations with large magnitude differences
 * - Matrix operations with special values (NaN, Infinity)
 */

const Prime = require("../../../src/core");
require("../../../src/math/matrix");
require("../../../src/framework/math");

// Import PrimeMath and Matrix class directly
const PrimeMath = require("../../../src/framework/math/prime-math.js");
const { Matrix } = require("../../../src/framework/math/linalg");

describe("Matrix Operations with Extreme Values", () => {
  
  // Helper function to check if two matrices are approximately equal
  const matrixApproxEqual = (A, B, epsilon = 1e-10) => {
    if (!A || !B) return false;
    if (A.length !== B.length) return false;
    
    for (let i = 0; i < A.length; i++) {
      if (A[i].length !== B[i].length) return false;
      
      for (let j = 0; j < A[i].length; j++) {
        if (Math.abs(A[i][j] - B[i][j]) > epsilon) return false;
      }
    }
    
    return true;
  };
  
  // Helper function to check matrix reconstruction
  const checkMatrixReconstruction = (original, U, S, V, epsilon = 1e-10) => {
    // Reconstruct the matrix from U, S, V
    const reconstructed = Prime.Math.Matrix.matrixMultiply(
      Prime.Math.Matrix.matrixMultiply(U, S),
      Prime.Math.Matrix.transpose(V)
    );
    
    // Check if the reconstructed matrix is approximately equal to the original
    return matrixApproxEqual(original, reconstructed, epsilon);
  };
  
  describe("SVD Decomposition with Extreme Values", () => {
    test("handles matrices with large magnitude differences", () => {
      // Create a matrix with extreme value ranges
      const matrixWithExtremes = [
        [1e-8, 2e-6, 3e-4],
        [4e2, 5e4, 6e6],
        [7, 8e-2, 9e-4]
      ];
      
      // Compute SVD
      const { U, S, V } = Prime.Math.Matrix.svd(matrixWithExtremes);
      
      // Check if U, S, V are defined
      expect(U).toBeDefined();
      expect(S).toBeDefined();
      expect(V).toBeDefined();
      
      // Check matrix reconstruction within a reasonable tolerance
      expect(checkMatrixReconstruction(matrixWithExtremes, U, S, V, 1e-8)).toBe(true);
    });
    
    test("handles nearly singular matrices", () => {
      // Create a nearly singular matrix
      const nearlySingular = [
        [1, 2, 3],
        [4, 8, 12.000001], // Almost linearly dependent
        [5, 10, 14.9]
      ];
      
      // Compute SVD
      const { U, S, V } = Prime.Math.Matrix.svd(nearlySingular);
      
      // Check if U, S, V are defined
      expect(U).toBeDefined();
      expect(S).toBeDefined();
      expect(V).toBeDefined();
      
      // Verify singular values (one should be very small)
      const singularValues = S.map(row => row.filter(val => val !== 0)[0] || 0);
      expect(singularValues[singularValues.length - 1]).toBeLessThan(1e-5);
      
      // Check matrix reconstruction (with higher tolerance)
      expect(checkMatrixReconstruction(nearlySingular, U, S, V, 1e-5)).toBe(true);
    });
    
    test("handles very small matrices without numerical overflow", () => {
      // Create a matrix with very small values
      const verySmallMatrix = [
        [1e-12, 2e-13, 3e-14],
        [4e-15, 5e-16, 6e-17],
        [7e-18, 8e-19, 9e-20]
      ];
      
      // Compute SVD
      const { U, S, V } = Prime.Math.Matrix.svd(verySmallMatrix);
      
      // Check if U, S, V are defined
      expect(U).toBeDefined();
      expect(S).toBeDefined();
      expect(V).toBeDefined();
      
      // Check that singular values are scaled appropriately
      const singularValues = S.map(row => row.filter(val => val !== 0)[0] || 0);
      expect(singularValues[0]).toBeLessThan(1e-11); // Should be very small but not zero
      
      // Verify orthogonality of U
      const UTU = Prime.Math.Matrix.matrixMultiply(
        Prime.Math.Matrix.transpose(U),
        U
      );
      
      // Diagonal elements should be close to 1
      for (let i = 0; i < UTU.length; i++) {
        expect(Math.abs(UTU[i][i] - 1.0)).toBeLessThan(1e-10);
      }
      
      // Check matrix reconstruction with a relaxed tolerance
      expect(checkMatrixReconstruction(verySmallMatrix, U, S, V, 1e-10)).toBe(true);
    });
    
    test("handles ill-conditioned matrices with special techniques", () => {
      // Create a Hilbert matrix, which is notoriously ill-conditioned
      const hilbertMatrix = [];
      const n = 5;
      
      for (let i = 0; i < n; i++) {
        hilbertMatrix[i] = [];
        for (let j = 0; j < n; j++) {
          hilbertMatrix[i][j] = 1.0 / (i + j + 1);
        }
      }
      
      // Compute SVD
      const { U, S, V } = Prime.Math.Matrix.svd(hilbertMatrix);
      
      // Check if U, S, V are defined
      expect(U).toBeDefined();
      expect(S).toBeDefined();
      expect(V).toBeDefined();
      
      // Verify condition number is high (ratio of largest to smallest singular value)
      const singularValues = S.map(row => row.filter(val => val !== 0)[0] || 0);
      const conditionNumber = singularValues[0] / singularValues[singularValues.length - 1];
      expect(conditionNumber).toBeGreaterThan(1e5); // Very high condition number expected
      
      // Verify orthogonality of V
      const VTV = Prime.Math.Matrix.matrixMultiply(
        Prime.Math.Matrix.transpose(V),
        V
      );
      
      // Diagonal elements should be close to 1
      for (let i = 0; i < VTV.length; i++) {
        expect(Math.abs(VTV[i][i] - 1.0)).toBeLessThan(1e-10);
      }
      
      // Reconstruction tolerance must be relaxed for ill-conditioned matrices
      expect(checkMatrixReconstruction(hilbertMatrix, U, S, V, 1e-5)).toBe(true);
    });
  });
  
  describe("LU Decomposition with Extreme Values", () => {
    test("handles matrices with large magnitude differences", () => {
      // Create a matrix with extreme value ranges
      const matrixWithExtremes = [
        [1e-8, 2e-6, 3e-4],
        [4e2, 5e4, 6e6],
        [7, 8e-2, 9e-4]
      ];
      
      // Compute LU decomposition
      const { L, U, P } = Prime.Math.Matrix.lu(matrixWithExtremes);
      
      // Check if L, U, P are defined
      expect(L).toBeDefined();
      expect(U).toBeDefined();
      expect(P).toBeDefined();
      
      // Reconstruct the matrix
      const PT = Prime.Math.Matrix.transpose(P);
      const LU = Prime.Math.Matrix.matrixMultiply(L, U);
      const reconstructed = Prime.Math.Matrix.matrixMultiply(PT, LU);
      
      // Check if the reconstructed matrix is approximately equal to the original
      expect(matrixApproxEqual(matrixWithExtremes, reconstructed, 1e-8)).toBe(true);
    });
    
    test("handles exactly singular matrices", () => {
      // Create a singular matrix
      const singularMatrix = [
        [1, 2, 3],
        [4, 8, 12],
        [5, 10, 15]
      ];
      
      // Expect the LU decomposition to handle singularity
      expect(() => {
        const { L, U, P } = Prime.Math.Matrix.lu(singularMatrix);
        
        // Verify U has zeros in the last row (if using complete pivoting)
        // or the last column has at least one zero on the diagonal
        const lastRowZero = U[U.length - 1].every(val => Math.abs(val) < 1e-10);
        const diagonalZero = Math.abs(U[U.length - 1][U[0].length - 1]) < 1e-10;
        
        expect(lastRowZero || diagonalZero).toBe(true);
      }).not.toThrow();
    });
    
    test("handles poorly scaled matrices", () => {
      // Create a poorly scaled matrix
      const poorlyScaled = [
        [1e10, 2e10, 3e-10],
        [4e-10, 5e-10, 6e10],
        [7e-10, 8e10, 9e-10]
      ];
      
      // Compute LU decomposition
      const { L, U, P } = Prime.Math.Matrix.lu(poorlyScaled);
      
      // Check if L, U, P are defined
      expect(L).toBeDefined();
      expect(U).toBeDefined();
      expect(P).toBeDefined();
      
      // Verify L has 1's on the diagonal
      for (let i = 0; i < L.length; i++) {
        expect(Math.abs(L[i][i] - 1.0)).toBeLessThan(1e-10);
      }
      
      // Reconstruct the matrix
      const PT = Prime.Math.Matrix.transpose(P);
      const LU = Prime.Math.Matrix.matrixMultiply(L, U);
      const reconstructed = Prime.Math.Matrix.matrixMultiply(PT, LU);
      
      // Use a relatively relaxed tolerance due to the extreme scale differences
      expect(matrixApproxEqual(poorlyScaled, reconstructed, 1e-5)).toBe(true);
    });
  });
  
  describe("Matrix Inversion with Extreme Values", () => {
    test("handles well-conditioned matrices", () => {
      // Identity matrix is perfectly conditioned
      const identity = [
        [1, 0, 0],
        [0, 1, 0],
        [0, 0, 1]
      ];
      
      // Compute inverse
      const inverse = Prime.Math.Matrix.inverse(identity);
      
      // Check if identity * inverse = identity
      const product = Prime.Math.Matrix.matrixMultiply(identity, inverse);
      expect(matrixApproxEqual(identity, product, 1e-12)).toBe(true);
    });
    
    test("handles ill-conditioned matrices using SVD", () => {
      // Create a Hilbert matrix, which is notoriously ill-conditioned
      const hilbertMatrix = [];
      const n = 4; // Keeping size small as the condition number grows rapidly
      
      for (let i = 0; i < n; i++) {
        hilbertMatrix[i] = [];
        for (let j = 0; j < n; j++) {
          hilbertMatrix[i][j] = 1.0 / (i + j + 1);
        }
      }
      
      // Compute inverse using SVD (if available)
      let inverse;
      if (Prime.Math.Matrix.inverseSVD) {
        inverse = Prime.Math.Matrix.inverseSVD(hilbertMatrix);
      } else {
        // Fall back to regular inverse
        inverse = Prime.Math.Matrix.inverse(hilbertMatrix);
      }
      
      // Multiply original by inverse
      const product = Prime.Math.Matrix.matrixMultiply(hilbertMatrix, inverse);
      
      // Check diagonal entries (should be close to 1)
      for (let i = 0; i < n; i++) {
        expect(Math.abs(product[i][i] - 1.0)).toBeLessThan(1e-2); // Relaxed tolerance
      }
      
      // Check off-diagonal entries (should be close to 0)
      for (let i = 0; i < n; i++) {
        for (let j = 0; j < n; j++) {
          if (i !== j) {
            expect(Math.abs(product[i][j])).toBeLessThan(1e-2); // Relaxed tolerance
          }
        }
      }
    });
    
    test("handles matrices with special values (NaN, Infinity)", () => {
      // Create a matrix with special values
      const specialMatrix = [
        [1, 0, 0],
        [0, NaN, 0],
        [0, 0, Infinity]
      ];
      
      // Attempt to compute inverse
      expect(() => {
        try {
          const inverse = Prime.Math.Matrix.inverse(specialMatrix);
          
          // If it doesn't throw, the implementation should handle special values
          // by replacing them with something meaningful or setting the result to undefined
          if (inverse) {
            // NaN entries should be handled or avoided
            for (let i = 0; i < inverse.length; i++) {
              for (let j = 0; j < inverse[i].length; j++) {
                expect(Number.isFinite(inverse[i][j]) || inverse[i][j] === undefined).toBe(true);
              }
            }
          }
        } catch (e) {
          // It's acceptable for the inverse function to throw with special values
          expect(e.message).toMatch(/NaN|Infinity|special/i);
        }
      }).not.toThrow();
    });
  });
  
  describe("Matrix Operations with Extreme Values", () => {
    test("handles matrices with very large values", () => {
      // Create matrices with large values
      const A = [
        [1e15, 2e15],
        [3e15, 4e15]
      ];
      
      const B = [
        [5e15, 6e15],
        [7e15, 8e15]
      ];
      
      // Compute addition
      const sum = Prime.Math.Matrix.add(A, B);
      
      // Check result
      expect(sum[0][0]).toBe(6e15);
      expect(sum[1][1]).toBe(12e15);
      
      // Compute multiplication
      const product = Prime.Math.Matrix.matrixMultiply(A, B);
      
      // Check that we get finite results
      expect(Number.isFinite(product[0][0])).toBe(true);
      expect(Number.isFinite(product[1][1])).toBe(true);
    });
    
    test("handles matrices with very small values", () => {
      // Create matrices with small values
      const A = [
        [1e-15, 2e-15],
        [3e-15, 4e-15]
      ];
      
      const B = [
        [5e-15, 6e-15],
        [7e-15, 8e-15]
      ];
      
      // Compute addition
      const sum = Prime.Math.Matrix.add(A, B);
      
      // Check result (uses approximate matching due to floating point precision)
      expect(sum[0][0]).toBeCloseTo(6e-15, 25);
      expect(sum[1][1]).toBeCloseTo(12e-15, 25);
      
      // Compute multiplication
      const product = Prime.Math.Matrix.matrixMultiply(A, B);
      
      // Check that we get non-zero results (despite potential underflow)
      expect(product[0][0]).not.toBe(0);
      expect(product[1][1]).not.toBe(0);
    });
    
    test("handles mixed precision operations", () => {
      // Create matrices with mixed precision values
      const A = [
        [1e10, 2],
        [3e-10, 4]
      ];
      
      const B = [
        [5, 6e10],
        [7e-10, 8]
      ];
      
      // Compute addition
      const sum = Prime.Math.Matrix.add(A, B);
      
      // Check result
      expect(sum[0][0]).toBeCloseTo(1e10 + 5, 5);
      expect(sum[0][1]).toBeCloseTo(2 + 6e10, 5);
      expect(sum[1][0]).toBeCloseTo(3e-10 + 7e-10, 15);
      expect(sum[1][1]).toBeCloseTo(4 + 8, 10);
      
      // Compute multiplication
      const product = Prime.Math.Matrix.matrixMultiply(A, B);
      
      // Check for finite values
      for (let i = 0; i < product.length; i++) {
        for (let j = 0; j < product[i].length; j++) {
          expect(Number.isFinite(product[i][j])).toBe(true);
        }
      }
    });
  });
});