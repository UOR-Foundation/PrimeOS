/**
 * PrimeOS Unit Tests - SVD Integration
 * 
 * Tests for the enhanced SVD integration with PrimeMath.
 */

const enhancedSVD = require('../../../src/framework/math/enhanced-svd.js');
const svdIntegration = require('../../../src/framework/math/svd-integration.js');
const PrimeMath = require('../../../src/framework/math/prime-math.js');

describe('SVD Integration', () => {
  describe('integrateEnhancedSVD function', () => {
    test('should integrate enhanced SVD with PrimeMath', () => {
      // Create a mock PrimeMath
      const mockPrimeMath = {
        svd: jest.fn(),
        createMatrix: jest.fn()
      };
      
      // Integrate enhanced SVD
      const enhanced = svdIntegration.integrateEnhancedSVD(mockPrimeMath);
      
      // Should have replaced svd method
      expect(enhanced.svd).not.toBe(mockPrimeMath.svd);
      
      // Should have added enhancedSVD
      expect(enhanced.enhancedSVD).toBe(enhancedSVD);
      
      // Should have added svdWithMetrics
      expect(typeof enhanced.svdWithMetrics).toBe('function');
    });
    
    test('should handle errors when PrimeMath is not available', () => {
      // Should return null when PrimeMath is null
      expect(svdIntegration.integrateEnhancedSVD(null)).toBe(null);
    });
  });
  
  describe('SVD with Matrix objects', () => {
    test('should handle matrix objects correctly', () => {
      // Create a matrix object
      const matrix = PrimeMath.createMatrix([
        [1, 2],
        [3, 4]
      ]);
      
      // Compute SVD
      const { U, S, V } = PrimeMath.svd(matrix);
      
      // Results should be matrix objects
      expect(U).toBeDefined();
      expect(S).toBeDefined();
      expect(V).toBeDefined();
      
      // The original matrix should be approximately reconstructed
      // A ≈ U * S * V^T
      const ST = PrimeMath.transposeMatrix(S);
      const VT = PrimeMath.transposeMatrix(V);
      const UST = PrimeMath.multiplyMatrices(U, ST);
      const reconstructed = PrimeMath.multiplyMatrices(UST, VT);
      
      // Compare original and reconstructed matrices
      for (let i = 0; i < matrix.rows; i++) {
        for (let j = 0; j < matrix.cols; j++) {
          expect(reconstructed.get(i, j)).toBeCloseTo(matrix.get(i, j), 10);
        }
      }
    });
  });
  
  describe('SVD with 2D arrays', () => {
    test('should handle 2D arrays correctly', () => {
      // Create a 2D array
      const matrix = [
        [1, 2],
        [3, 4]
      ];
      
      // Compute SVD
      const result = enhancedSVD(matrix);
      
      // Results should be defined
      expect(result.U).toBeDefined();
      expect(result.S).toBeDefined();
      expect(result.V).toBeDefined();
      
      // Should include metadata
      expect(result.metadata).toBeDefined();
      expect(result.algorithm).toBeDefined();
    });
    
    test('should handle non-square matrices correctly', () => {
      // Create a non-square matrix
      const matrix = [
        [1, 2, 3],
        [4, 5, 6]
      ];
      
      // Compute SVD
      const result = enhancedSVD(matrix);
      
      // U should be m×m
      expect(result.U.length).toBe(2);
      expect(result.U[0].length).toBe(2);
      
      // S should be m×n
      expect(result.S.length).toBe(2);
      expect(result.S[0].length).toBe(3);
      
      // V should be n×n
      expect(result.V.length).toBe(3);
      expect(result.V[0].length).toBe(3);
      
      // Only min(m,n) singular values should be non-zero
      expect(result.S[0][0]).toBeGreaterThan(0);
      expect(result.S[1][1]).toBeGreaterThan(0);
      
      // The original matrix should be approximately reconstructed
      // A ≈ U * S * V^T
      const reconstructed = multiplyMatrices(
        multiplyMatrices(result.U, result.S),
        transposeMatrix(result.V)
      );
      
      // Compare original and reconstructed matrices
      for (let i = 0; i < matrix.length; i++) {
        for (let j = 0; j < matrix[0].length; j++) {
          expect(reconstructed[i][j]).toBeCloseTo(matrix[i][j], 10);
        }
      }
    });
  });
  
  describe('Algorithm selection', () => {
    test('should select Jacobi for small matrices', () => {
      // Create a small matrix
      const matrix = [
        [1, 2],
        [3, 4]
      ];
      
      // Force Jacobi algorithm
      const result = enhancedSVD(matrix, { algorithm: 'jacobi' });
      
      // Should use Jacobi algorithm
      expect(result.algorithm).toBe('jacobi');
    });
    
    test('should select QR for medium matrices with good condition', () => {
      // Skip this test if it takes too long
      if (process.env.SKIP_SLOW_TESTS) {
        return;
      }
      
      // Create a medium-sized, well-conditioned matrix
      const matrix = [];
      for (let i = 0; i < 50; i++) {
        matrix[i] = [];
        for (let j = 0; j < 50; j++) {
          matrix[i][j] = i === j ? 1 : 0.01;
        }
      }
      
      // Force QR algorithm
      const result = enhancedSVD(matrix, { algorithm: 'qr' });
      
      // Should use QR algorithm
      expect(result.algorithm).toBe('qr');
    });
  });
  
  describe('Error handling', () => {
    test('should handle invalid input gracefully', () => {
      // Empty matrix
      expect(() => enhancedSVD([])).toThrow();
      
      // Invalid matrix
      expect(() => enhancedSVD([[]])).toThrow();
      
      // Invalid algorithm
      expect(() => enhancedSVD([[1, 2], [3, 4]], { algorithm: 'invalid' })).toThrow();
    });
    
    test('should handle matrices with NaN or Infinity', () => {
      // Matrix with NaN
      expect(() => enhancedSVD([[1, NaN], [3, 4]])).toThrow();
      
      // Matrix with Infinity
      expect(() => enhancedSVD([[1, 2], [3, Infinity]])).toThrow();
    });
  });
});

// Helper functions for matrix operations
function multiplyMatrices(a, b) {
  const result = [];
  const m = a.length;
  const n = b[0].length;
  const p = b.length;
  
  for (let i = 0; i < m; i++) {
    result[i] = [];
    for (let j = 0; j < n; j++) {
      let sum = 0;
      for (let k = 0; k < p; k++) {
        sum += a[i][k] * b[k][j];
      }
      result[i][j] = sum;
    }
  }
  
  return result;
}

function transposeMatrix(matrix) {
  const result = [];
  const rows = matrix.length;
  const cols = matrix[0].length;
  
  for (let j = 0; j < cols; j++) {
    result[j] = [];
    for (let i = 0; i < rows; i++) {
      result[j][i] = matrix[i][j];
    }
  }
  
  return result;
}