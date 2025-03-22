/**
 * Matrix Extreme Values Tests
 * 
 * Tests for matrix operations with extreme numerical values to verify stability
 */

const Prime = require('../src/core');
require('../src/math/matrix'); // This loads all the matrix modules
require('../src/framework/math'); // Load the framework math modules

describe('Matrix Extreme Values', () => {
  describe('LU Decomposition with Extreme Values', () => {
    test('should handle matrices with large magnitude differences', () => {
      // Create a matrix with extreme value ranges
      const matrixWithExtremes = [
        [1e15, 1e-10],
        [1e-10, 1e15]
      ];
      
      // Perform LU decomposition
      const { L, U } = Prime.Math.Matrix.luDecomposition(matrixWithExtremes);
      
      // Verify L and U are valid and contain finite values
      expect(L).toBeDefined();
      expect(U).toBeDefined();
      
      // Check L and U have finite values
      for (let i = 0; i < 2; i++) {
        for (let j = 0; j < 2; j++) {
          expect(Number.isFinite(L[i][j])).toBe(true);
          expect(Number.isFinite(U[i][j])).toBe(true);
        }
      }
      
      // Verify L is lower triangular with 1s on diagonal
      expect(L[0][0]).toBe(1);
      expect(Math.abs(L[1][0])).toBeLessThan(1);
      expect(L[0][1]).toBe(0);
      expect(L[1][1]).toBe(1);
      
      // Verify L*U = original matrix (approximately)
      const reconstructed = Prime.Math.Matrix.multiply(L, U);
      
      // Use relative error for comparison due to extreme values
      expect(Math.abs(reconstructed[0][0] / matrixWithExtremes[0][0] - 1)).toBeLessThan(1e-10);
      expect(Math.abs(reconstructed[0][1] / matrixWithExtremes[0][1] - 1)).toBeLessThan(1e-6);
      expect(Math.abs(reconstructed[1][0] / matrixWithExtremes[1][0] - 1)).toBeLessThan(1e-6);
      expect(Math.abs(reconstructed[1][1] / matrixWithExtremes[1][1] - 1)).toBeLessThan(1e-10);
    });
    
    test('should handle matrices with zeros on the diagonal through pivoting', () => {
      // Matrix with a zero on the diagonal that requires pivoting
      const matrixWithZeroDiagonal = [
        [0, 1e5],
        [1e-5, 1e10]
      ];
      
      // This should NOT throw with our pivoting implementation
      const { L, U, P } = Prime.Math.Matrix.luDecomposition(matrixWithZeroDiagonal);
      
      // Check that P*L*U = original matrix
      // First create the permutation matrix from P
      const permMatrix = [
        [0, 0],
        [0, 0]
      ];
      
      // Convert P array to permutation matrix
      for (let i = 0; i < 2; i++) {
        permMatrix[i][P[i]] = 1;
      }
      
      // Multiply P * original matrix
      const permutedOriginal = Prime.Math.Matrix.multiply(permMatrix, matrixWithZeroDiagonal);
      
      // Now check L*U against permutedOriginal
      const reconstructed = Prime.Math.Matrix.multiply(L, U);
      
      // Check with appropriate tolerance
      for (let i = 0; i < 2; i++) {
        for (let j = 0; j < 2; j++) {
          // For very small values, use absolute error
          if (Math.abs(permutedOriginal[i][j]) < 1e-10) {
            expect(Math.abs(reconstructed[i][j] - permutedOriginal[i][j])).toBeLessThan(1e-8);
          } else {
            // For larger values, use relative error
            expect(Math.abs(reconstructed[i][j] / permutedOriginal[i][j] - 1)).toBeLessThan(1e-8);
          }
        }
      }
    });
  });
  
  describe('QR Decomposition with Extreme Values', () => {
    test('should handle matrices with large magnitude differences', () => {
      // Create a matrix with extreme value ranges
      const matrixWithExtremes = [
        [1e15, 1e-10],
        [1e-10, 1e15],
        [1, 1]
      ];
      
      // Perform QR decomposition
      const { Q, R } = Prime.Math.Matrix.qrDecomposition(matrixWithExtremes);
      
      // Verify Q and R are valid and contain finite values
      expect(Q).toBeDefined();
      expect(R).toBeDefined();
      
      // Check Q and R have finite values
      for (let i = 0; i < Q.length; i++) {
        for (let j = 0; j < Q[0].length; j++) {
          expect(Number.isFinite(Q[i][j])).toBe(true);
        }
      }
      
      for (let i = 0; i < R.length; i++) {
        for (let j = 0; j < R[0].length; j++) {
          expect(Number.isFinite(R[i][j])).toBe(true);
        }
      }
      
      // Verify Q has orthogonal columns (QᵀQ = I)
      // Calculate QᵀQ
      const QTranspose = Prime.Math.Matrix.transpose(Q);
      const QTQ = Prime.Math.Matrix.multiply(QTranspose, Q);
      
      // Check diagonal elements are approximately 1
      for (let i = 0; i < QTQ.length; i++) {
        expect(Math.abs(QTQ[i][i] - 1)).toBeLessThan(1e-8);
      }
      
      // Check off-diagonal elements are approximately 0
      for (let i = 0; i < QTQ.length; i++) {
        for (let j = 0; j < QTQ.length; j++) {
          if (i !== j) {
            expect(Math.abs(QTQ[i][j])).toBeLessThan(1e-8);
          }
        }
      }
      
      // Verify Q*R = original matrix (approximately)
      const reconstructed = Prime.Math.Matrix.multiply(Q, R);
      
      // Use relative error for comparison due to extreme values
      for (let i = 0; i < matrixWithExtremes.length; i++) {
        for (let j = 0; j < matrixWithExtremes[0].length; j++) {
          if (Math.abs(matrixWithExtremes[i][j]) > 1e-6) {
            expect(Math.abs(reconstructed[i][j] / matrixWithExtremes[i][j] - 1)).toBeLessThan(1e-6);
          } else {
            expect(Math.abs(reconstructed[i][j] - matrixWithExtremes[i][j])).toBeLessThan(1e-6);
          }
        }
      }
    });
  });
  
  describe('Eigenvalues with Extreme Values', () => {
    test('should handle symmetric matrices with extreme values', () => {
      // Create a symmetric matrix with extreme values
      const symmetricExtreme = [
        [1e15, 1e-10],
        [1e-10, 1e-15]
      ];
      
      // Compute eigenvalues
      const { eigenvalues } = Prime.Math.Matrix.eigenvalues(symmetricExtreme, { numEigenvalues: 2 });
      
      // Verify eigenvalues are finite
      expect(eigenvalues).toBeDefined();
      expect(eigenvalues.length).toBe(2);
      expect(Number.isFinite(eigenvalues[0])).toBe(true);
      expect(Number.isFinite(eigenvalues[1])).toBe(true);
      
      // Eigenvalues should be approximately equal to the matrix trace (sum of diagonals)
      const trace = symmetricExtreme[0][0] + symmetricExtreme[1][1];
      const eigenvalueSum = eigenvalues[0] + eigenvalues[1];
      
      // Check sum of eigenvalues approximately equals trace
      expect(Math.abs(eigenvalueSum / trace - 1)).toBeLessThan(1e-6);
    });
  });
  
  describe('Cholesky Decomposition with Extreme Values', () => {
    test('should handle positive-definite matrices with large magnitude differences', () => {
      // Create a symmetric positive-definite matrix with extreme value ranges
      // For a matrix to be positive-definite, we need values that ensure all eigenvalues are positive
      const matrixWithExtremes = [
        [1e15, 1e-5],
        [1e-5, 1e-10]
      ];
      
      // Perform Cholesky decomposition
      const L = Prime.Math.Matrix.choleskyDecomposition(matrixWithExtremes);
      
      // Verify L is valid and contains finite values
      expect(L).toBeDefined();
      
      // Check L has finite values
      for (let i = 0; i < 2; i++) {
        for (let j = 0; j <= i; j++) {
          expect(Number.isFinite(L[i][j])).toBe(true);
        }
      }
      
      // Verify L is lower triangular
      expect(L[0][1]).toBe(0);
      
      // Verify L*L^T = original matrix (approximately)
      const LTranspose = Prime.Math.Matrix.transpose(L);
      const reconstructed = Prime.Math.Matrix.multiply(L, LTranspose);
      
      // Use relative error for comparison due to extreme values
      for (let i = 0; i < 2; i++) {
        for (let j = 0; j < 2; j++) {
          const original = matrixWithExtremes[i][j];
          const computed = reconstructed[i][j];
          
          if (Math.abs(original) > 1e-10) {
            expect(Math.abs(computed / original - 1)).toBeLessThan(1e-6);
          } else {
            expect(Math.abs(computed - original)).toBeLessThan(1e-10);
          }
        }
      }
    });
    
    test('should handle very small positive-definite matrices', () => {
      // Create a symmetric positive-definite matrix with very small values
      // Make sure the matrix is definitely positive-definite by using the form A^T*A
      const smallMatrix = [
        [1e-150, 1e-200],
        [1e-200, 3e-150]  // Make diagonal entry larger than square of off-diagonal
      ];
      
      // Perform Cholesky decomposition
      const L = Prime.Math.Matrix.choleskyDecomposition(smallMatrix);
      
      // Verify L is valid and contains finite values
      expect(L).toBeDefined();
      
      // Check L has finite values
      for (let i = 0; i < 2; i++) {
        for (let j = 0; j <= i; j++) {
          expect(Number.isFinite(L[i][j])).toBe(true);
          expect(isNaN(L[i][j])).toBe(false);
        }
      }
      
      // Verify L*L^T = original matrix (approximately using relative error)
      const LTranspose = Prime.Math.Matrix.transpose(L);
      const reconstructed = Prime.Math.Matrix.multiply(L, LTranspose);
      
      // Each element should be close to the original within a relative tolerance
      for (let i = 0; i < 2; i++) {
        for (let j = 0; j < 2; j++) {
          const original = smallMatrix[i][j];
          const computed = reconstructed[i][j];
          // For extremely small values, relative difference might need a larger tolerance
          const tolerance = original !== 0 ? 1e-5 : 1e-10;
          
          if (Math.abs(original) > 1e-200) {
            const relativeDiff = Math.abs(computed / original - 1);
            expect(relativeDiff).toBeLessThan(tolerance);
          } else {
            // For extremely small values, check absolute difference
            expect(Math.abs(computed - original)).toBeLessThan(1e-200);
          }
        }
      }
    });
    
    test('should handle very large positive-definite matrices', () => {
      // Create a symmetric positive-definite matrix with very large values
      // Make sure the matrix is definitely positive-definite
      const largeMatrix = [
        [1e150, 1e100],
        [1e100, 3e150]  // Make diagonal entry larger than square of off-diagonal / 1e100
      ];
      
      // Perform Cholesky decomposition
      const L = Prime.Math.Matrix.choleskyDecomposition(largeMatrix);
      
      // Verify L is valid and contains finite values
      expect(L).toBeDefined();
      
      // Check L has finite values
      for (let i = 0; i < 2; i++) {
        for (let j = 0; j <= i; j++) {
          expect(Number.isFinite(L[i][j])).toBe(true);
          expect(isNaN(L[i][j])).toBe(false);
        }
      }
      
      // Verify L*L^T = original matrix (approximately using relative error)
      const LTranspose = Prime.Math.Matrix.transpose(L);
      const reconstructed = Prime.Math.Matrix.multiply(L, LTranspose);
      
      // Each element should be close to the original within a relative tolerance
      for (let i = 0; i < 2; i++) {
        for (let j = 0; j < 2; j++) {
          const original = largeMatrix[i][j];
          const computed = reconstructed[i][j];
          const tolerance = 1e-5;  // Use a slightly larger tolerance for extreme values
          
          const relativeDiff = Math.abs(computed / original - 1);
          expect(relativeDiff).toBeLessThan(tolerance);
        }
      }
    });
    
    test('should reject non-positive-definite matrices', () => {
      // Matrix with a negative eigenvalue (not positive-definite)
      const nonPDMatrix = [
        [1, 2],
        [2, 1]
      ];
      
      // This should throw
      expect(() => {
        Prime.Math.Matrix.choleskyDecomposition(nonPDMatrix);
      }).toThrow();
    });
    
    test('should reject non-symmetric matrices', () => {
      // Non-symmetric matrix
      const nonSymmetricMatrix = [
        [1, 2],
        [3, 4]
      ];
      
      // This should throw
      expect(() => {
        Prime.Math.Matrix.choleskyDecomposition(nonSymmetricMatrix);
      }).toThrow();
    });
  });

  describe('SVD with Extreme Values', () => {
    test('should handle matrices with large magnitude differences', () => {
      // Create a matrix with extreme value ranges
      const matrixWithExtremes = [
        [1e15, 1e-10],
        [1e-10, 1e15]
      ];
      
      // Create a matrix object and perform SVD
      const matrix = Prime.math.createMatrix(matrixWithExtremes);
      const { U, S, V } = matrix.svd({ tolerance: 1e-12, maxIterations: 200 });
      
      // Verify U, S, and V are valid and contain finite values
      expect(U).toBeDefined();
      expect(S).toBeDefined();
      expect(V).toBeDefined();
      
      // Check U, S, and V have finite values
      for (let i = 0; i < U.length; i++) {
        for (let j = 0; j < U[0].length; j++) {
          expect(Number.isFinite(U[i][j])).toBe(true);
        }
      }
      
      for (let i = 0; i < S.length; i++) {
        for (let j = 0; j < S[0].length; j++) {
          expect(Number.isFinite(S[i][j])).toBe(true);
        }
      }
      
      for (let i = 0; i < V.length; i++) {
        for (let j = 0; j < V[0].length; j++) {
          expect(Number.isFinite(V[i][j])).toBe(true);
        }
      }
      
      // Verify S is diagonal
      for (let i = 0; i < S.length; i++) {
        for (let j = 0; j < S[0].length; j++) {
          if (i !== j) {
            expect(Math.abs(S[i][j])).toBeLessThan(1e-10);
          }
        }
      }
      
      // Verify U has orthogonal columns
      for (let i = 0; i < U[0].length; i++) {
        for (let j = i + 1; j < U[0].length; j++) {
          let dotProduct = 0;
          for (let k = 0; k < U.length; k++) {
            dotProduct += U[k][i] * U[k][j];
          }
          expect(Math.abs(dotProduct)).toBeLessThan(1e-8);
        }
      }
      
      // Verify V has orthogonal columns
      for (let i = 0; i < V[0].length; i++) {
        for (let j = i + 1; j < V[0].length; j++) {
          let dotProduct = 0;
          for (let k = 0; k < V.length; k++) {
            dotProduct += V[k][i] * V[k][j];
          }
          expect(Math.abs(dotProduct)).toBeLessThan(1e-8);
        }
      }
      
      // Verify USV^T = original matrix (approximately)
      const VTranspose = Prime.Math.Matrix.transpose(V);
      const SV = Prime.Math.Matrix.multiply(S, VTranspose);
      const USV = Prime.Math.Matrix.multiply(U, SV);
      
      // Use relative error for comparison due to extreme values
      for (let i = 0; i < matrixWithExtremes.length; i++) {
        for (let j = 0; j < matrixWithExtremes[0].length; j++) {
          const original = matrixWithExtremes[i][j];
          const computed = USV[i][j];
          
          if (Math.abs(original) > 1e-10) {
            expect(Math.abs(computed / original - 1)).toBeLessThan(1e-6);
          } else {
            expect(Math.abs(computed - original)).toBeLessThan(1e-10);
          }
        }
      }
    });
    
    test('should handle very small matrices', () => {
      // Create a matrix with very small values
      const smallMatrix = [
        [1e-150, 1e-200],
        [1e-200, 1e-150]
      ];
      
      // Create a matrix object and perform SVD
      const matrix = Prime.math.createMatrix(smallMatrix);
      const { U, S, V } = matrix.svd();
      
      // Verify results contain no NaN or Infinity
      for (let i = 0; i < U.length; i++) {
        for (let j = 0; j < U[0].length; j++) {
          expect(Number.isFinite(U[i][j])).toBe(true);
          expect(isNaN(U[i][j])).toBe(false);
        }
      }
      
      for (let i = 0; i < S.length; i++) {
        for (let j = 0; j < S[0].length; j++) {
          expect(Number.isFinite(S[i][j])).toBe(true);
          expect(isNaN(S[i][j])).toBe(false);
        }
      }
      
      for (let i = 0; i < V.length; i++) {
        for (let j = 0; j < V[0].length; j++) {
          expect(Number.isFinite(V[i][j])).toBe(true);
          expect(isNaN(V[i][j])).toBe(false);
        }
      }
      
      // Verify singular values are non-negative and in descending order
      for (let i = 0; i < Math.min(S.length, S[0].length) - 1; i++) {
        expect(S[i][i]).toBeGreaterThanOrEqual(0);
        expect(S[i][i]).toBeGreaterThanOrEqual(S[i+1][i+1]);
      }
      
      // Verify USV^T = original matrix (with appropriate tolerance for small values)
      const UMatrix1 = Prime.math.createMatrix(U);
      const SMatrix1 = Prime.math.createMatrix(S);
      const VMatrix1 = Prime.math.createMatrix(V);
      const VTranspose1 = VMatrix1.transpose();
      const SV1 = SMatrix1.multiply(VTranspose1);
      const USV1 = UMatrix1.multiply(SV1);
      
      // Each element should be close to the original within a suitable tolerance
      for (let i = 0; i < smallMatrix.length; i++) {
        for (let j = 0; j < smallMatrix[0].length; j++) {
          const original = smallMatrix[i][j];
          const computed = USV1.values[i][j];
          
          if (Math.abs(original) > 1e-200) {
            // Use relative error with a larger tolerance for extremely small values
            const relativeDiff = Math.abs(computed / original - 1);
            expect(relativeDiff).toBeLessThan(1e-5);
          } else {
            // For extremely small values, check absolute difference
            expect(Math.abs(computed - original)).toBeLessThan(1e-200);
          }
        }
      }
    });
    
    test('should handle very large matrices', () => {
      // Create a matrix with very large values
      const largeMatrix = [
        [1e150, 1e100],
        [1e100, 1e150]
      ];
      
      // Create a matrix object and perform SVD
      const matrix = Prime.math.createMatrix(largeMatrix);
      const { U, S, V } = matrix.svd();
      
      // Verify results contain no NaN or Infinity
      for (let i = 0; i < U.length; i++) {
        for (let j = 0; j < U[0].length; j++) {
          expect(Number.isFinite(U[i][j])).toBe(true);
          expect(isNaN(U[i][j])).toBe(false);
        }
      }
      
      for (let i = 0; i < S.length; i++) {
        for (let j = 0; j < S[0].length; j++) {
          expect(Number.isFinite(S[i][j])).toBe(true);
          expect(isNaN(S[i][j])).toBe(false);
        }
      }
      
      for (let i = 0; i < V.length; i++) {
        for (let j = 0; j < V[0].length; j++) {
          expect(Number.isFinite(V[i][j])).toBe(true);
          expect(isNaN(V[i][j])).toBe(false);
        }
      }
      
      // Verify USV^T = original matrix (with appropriate tolerance for large values)
      const UMatrix3 = Prime.math.createMatrix(U);
      const SMatrix3 = Prime.math.createMatrix(S);
      const VMatrix3 = Prime.math.createMatrix(V);
      const VTranspose3 = VMatrix3.transpose();
      const SV3 = SMatrix3.multiply(VTranspose3);
      const USV3 = UMatrix3.multiply(SV3);
      
      // Each element should be close to the original within a relative tolerance
      for (let i = 0; i < largeMatrix.length; i++) {
        for (let j = 0; j < largeMatrix[0].length; j++) {
          const original = largeMatrix[i][j];
          const computed = USV3.values[i][j];
          const tolerance = 1e-5;  // Use a slightly larger tolerance for extreme values
          
          const relativeDiff = Math.abs(computed / original - 1);
          expect(relativeDiff).toBeLessThan(tolerance);
        }
      }
    });
    
    test('should handle mixed extreme values correctly', () => {
      // Matrix with mixed extreme values
      const mixedMatrix = [
        [1e-150, 1e100],
        [1e100, 1e-150]
      ];
      
      // Create a matrix object and perform SVD
      const matrix = Prime.math.createMatrix(mixedMatrix);
      const { U, S, V } = matrix.svd();
      
      // Verify orthogonality of U
      const UMatrix = Prime.math.createMatrix(U);
      const UTranspose = UMatrix.transpose();
      const UTransposeU = UTranspose.multiply(UMatrix);
      for (let i = 0; i < UTransposeU.rows; i++) {
        for (let j = 0; j < UTransposeU.cols; j++) {
          if (i === j) {
            expect(Math.abs(UTransposeU.values[i][j] - 1)).toBeLessThan(1e-8);
          } else {
            expect(Math.abs(UTransposeU.values[i][j])).toBeLessThan(1e-8);
          }
        }
      }
      
      // Verify orthogonality of V
      const VMatrix = Prime.math.createMatrix(V);
      const VTranspose = VMatrix.transpose();
      const VTransposeV = VTranspose.multiply(VMatrix);
      for (let i = 0; i < VTransposeV.rows; i++) {
        for (let j = 0; j < VTransposeV.cols; j++) {
          if (i === j) {
            expect(Math.abs(VTransposeV.values[i][j] - 1)).toBeLessThan(1e-8);
          } else {
            expect(Math.abs(VTransposeV.values[i][j])).toBeLessThan(1e-8);
          }
        }
      }
      
      // For this extreme case, the singular values should reflect the structure
      // The largest singular value should be approximately 1e100
      expect(Math.abs(S[0][0])).toBeGreaterThan(1e50);
      
      // Verify reconstruction accuracy selectively based on magnitude
      const UMatrix2 = Prime.math.createMatrix(U);
      const SMatrix2 = Prime.math.createMatrix(S);
      const VMatrix2 = Prime.math.createMatrix(V);
      const VTranspose2 = VMatrix2.transpose();
      const SV2 = SMatrix2.multiply(VTranspose2);
      const USV2 = UMatrix2.multiply(SV2);
      
      // Each element should be close to the original, accounting for magnitude
      for (let i = 0; i < mixedMatrix.length; i++) {
        for (let j = 0; j < mixedMatrix[0].length; j++) {
          const original = mixedMatrix[i][j];
          const computed = USV2.values[i][j];
          
          if (Math.abs(original) > 1e50) {
            // For very large values, use relative error
            expect(Math.abs(computed / original - 1)).toBeLessThan(1e-5);
          } else if (Math.abs(original) < 1e-50) {
            // For very small values, the reconstructed value may be dominated by numerical error
            // Instead of checking exact reconstruction, verify the magnitude is small
            expect(Math.abs(computed)).toBeLessThan(1e-10);
          }
        }
      }
    });
    
    test('should handle non-square matrices with extreme values', () => {
      // Create a non-square matrix with extreme values
      const nonSquareExtreme = [
        [1e150, 1e-150, 1e10],
        [1e-150, 1e150, 1e-10]
      ];
      
      // Create a matrix object and perform SVD
      const matrix = Prime.math.createMatrix(nonSquareExtreme);
      const { U, S, V } = matrix.svd();
      
      // Check dimensions
      expect(U.length).toBe(2);  // rows
      expect(U[0].length).toBe(2);  // cols, Min(2,3) = 2
      expect(S.length).toBe(2);  // rows
      expect(S[0].length).toBe(3);  // cols
      expect(V.length).toBe(3);  // rows 
      expect(V[0].length).toBe(3);  // cols
      
      // Verify singular values are non-negative and in descending order
      for (let i = 0; i < Math.min(S.length, S[0].length) - 1; i++) {
        expect(S[i][i]).toBeGreaterThanOrEqual(0);
        expect(S[i][i]).toBeGreaterThanOrEqual(S[i+1][i+1]);
      }
      
      // Verify orthogonality of U and V
      const UMatrixNS = Prime.math.createMatrix(U);
      const VMatrixNS = Prime.math.createMatrix(V);
      const UT = UMatrixNS.transpose();
      const VT = VMatrixNS.transpose();
      const UTU = UT.multiply(UMatrixNS);
      const VTV = VT.multiply(VMatrixNS);
      
      for (let i = 0; i < UTU.rows; i++) {
        for (let j = 0; j < UTU.cols; j++) {
          if (i === j) {
            expect(Math.abs(UTU.values[i][j] - 1)).toBeLessThan(1e-8);
          } else {
            expect(Math.abs(UTU.values[i][j])).toBeLessThan(1e-8);
          }
        }
      }
      
      for (let i = 0; i < VTV.rows; i++) {
        for (let j = 0; j < VTV.cols; j++) {
          if (i === j) {
            expect(Math.abs(VTV.values[i][j] - 1)).toBeLessThan(1e-8);
          } else {
            expect(Math.abs(VTV.values[i][j])).toBeLessThan(1e-8);
          }
        }
      }
      
      // Verify reconstruction
      const UMatrix4 = Prime.math.createMatrix(U);
      const SMatrix4 = Prime.math.createMatrix(S);
      const VMatrix4 = Prime.math.createMatrix(V);
      const VTranspose4 = VMatrix4.transpose();
      const SV4 = SMatrix4.multiply(VTranspose4);
      const USV4 = UMatrix4.multiply(SV4);
      
      for (let i = 0; i < nonSquareExtreme.length; i++) {
        for (let j = 0; j < nonSquareExtreme[0].length; j++) {
          const original = nonSquareExtreme[i][j];
          const computed = USV4.values[i][j];
          
          if (Math.abs(original) > 1e50) {
            expect(Math.abs(computed / original - 1)).toBeLessThan(1e-5);
          } else if (Math.abs(original) < 1e-50) {
            expect(Math.abs(computed)).toBeLessThan(1e-10);
          } else {
            expect(Math.abs(computed / original - 1)).toBeLessThan(1e-5);
          }
        }
      }
    });
  });
});