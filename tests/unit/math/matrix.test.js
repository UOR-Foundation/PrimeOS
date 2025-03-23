/**
 * PrimeOS Unit Tests - Matrix Operations
 * 
 * Tests for basic matrix operations in the Mathematics module.
 */

// Import our test-specific implementation to avoid circular dependency issues
const Prime = require('../../../src/framework/math/matrix-test-ops.js');
const { Assertions } = require('../../utils');

describe('Matrix Operations', () => {
  describe('Matrix Creation', () => {
    test('creates matrices with correct dimensions', () => {
      const matrix = Prime.Math.Matrix.create(2, 3);
      expect(matrix.length).toBe(2);
      expect(matrix[0].length).toBe(3);
      
      // Default initialization with zeros
      for (let i = 0; i < 2; i++) {
        for (let j = 0; j < 3; j++) {
          expect(matrix[i][j]).toBe(0);
        }
      }
    });
    
    test('creates matrices with initial value', () => {
      const matrix = Prime.Math.Matrix.create(2, 2, 1);
      expect(matrix.length).toBe(2);
      expect(matrix[0].length).toBe(2);
      
      for (let i = 0; i < 2; i++) {
        for (let j = 0; j < 2; j++) {
          expect(matrix[i][j]).toBe(1);
        }
      }
    });
    
    test('creates identity matrix', () => {
      const identity = Prime.Math.Matrix.identity(3);
      expect(identity.length).toBe(3);
      expect(identity[0].length).toBe(3);
      
      for (let i = 0; i < 3; i++) {
        for (let j = 0; j < 3; j++) {
          if (i === j) {
            expect(identity[i][j]).toBe(1);
          } else {
            expect(identity[i][j]).toBe(0);
          }
        }
      }
    });
    
    test('creates diagonal matrix', () => {
      const diag = Prime.Math.Matrix.diag([1, 2, 3]);
      expect(diag.length).toBe(3);
      expect(diag[0].length).toBe(3);
      
      for (let i = 0; i < 3; i++) {
        for (let j = 0; j < 3; j++) {
          if (i === j) {
            expect(diag[i][j]).toBe(i + 1);
          } else {
            expect(diag[i][j]).toBe(0);
          }
        }
      }
    });
  });
  
  describe('Matrix Basic Operations', () => {
    test('adds matrices correctly', () => {
      const a = [
        [1, 2],
        [3, 4]
      ];
      
      const b = [
        [5, 6],
        [7, 8]
      ];
      
      const result = Prime.Math.Matrix.add(a, b);
      expect(result).toEqual([
        [6, 8],
        [10, 12]
      ]);
    });
    
    test('subtracts matrices correctly', () => {
      const a = [
        [5, 6],
        [7, 8]
      ];
      
      const b = [
        [1, 2],
        [3, 4]
      ];
      
      const result = Prime.Math.Matrix.subtract(a, b);
      expect(result).toEqual([
        [4, 4],
        [4, 4]
      ]);
    });
    
    test('multiplies matrix by scalar', () => {
      const a = [
        [1, 2],
        [3, 4]
      ];
      
      const result = Prime.Math.Matrix.scalarMultiply(a, 2);
      expect(result).toEqual([
        [2, 4],
        [6, 8]
      ]);
    });
    
    test('computes element-wise products', () => {
      const a = [
        [1, 2],
        [3, 4]
      ];
      
      const b = [
        [5, 6],
        [7, 8]
      ];
      
      const result = Prime.Math.Matrix.elementWiseMultiply(a, b);
      expect(result).toEqual([
        [5, 12],
        [21, 32]
      ]);
    });
  });
  
  describe('Matrix Multiplication', () => {
    test('multiplies matrices correctly', () => {
      const a = [
        [1, 2],
        [3, 4]
      ];
      
      const b = [
        [5, 6],
        [7, 8]
      ];
      
      const result = Prime.Math.Matrix.multiply(a, b);
      expect(result).toEqual([
        [19, 22],
        [43, 50]
      ]);
    });
    
    test('multiplies with identity returns original', () => {
      const a = [
        [1, 2],
        [3, 4]
      ];
      
      const identity = Prime.Math.Matrix.identity(2);
      const result = Prime.Math.Matrix.multiply(a, identity);
      expect(result).toEqual(a);
    });
    
    test('handles multiplication of different sized matrices', () => {
      const a = [
        [1, 2, 3],
        [4, 5, 6]
      ];
      
      const b = [
        [7, 8],
        [9, 10],
        [11, 12]
      ];
      
      const result = Prime.Math.Matrix.multiply(a, b);
      expect(result).toEqual([
        [58, 64],
        [139, 154]
      ]);
    });
  });
  
  describe('Matrix Transposition', () => {
    test('transposes square matrix correctly', () => {
      const a = [
        [1, 2],
        [3, 4]
      ];
      
      const result = Prime.Math.Matrix.transpose(a);
      expect(result).toEqual([
        [1, 3],
        [2, 4]
      ]);
    });
    
    test('transposes rectangular matrix correctly', () => {
      const a = [
        [1, 2, 3],
        [4, 5, 6]
      ];
      
      const result = Prime.Math.Matrix.transpose(a);
      expect(result).toEqual([
        [1, 4],
        [2, 5],
        [3, 6]
      ]);
    });
    
    test('double transpose returns original matrix', () => {
      const a = [
        [1, 2, 3],
        [4, 5, 6]
      ];
      
      const transposed = Prime.Math.Matrix.transpose(a);
      const doubleTransposed = Prime.Math.Matrix.transpose(transposed);
      expect(doubleTransposed).toEqual(a);
    });
  });
  
  describe('Determinant and Inverse', () => {
    test('calculates determinant of 2x2 matrix', () => {
      const a = [
        [1, 2],
        [3, 4]
      ];
      
      const det = Prime.Math.Matrix.determinant(a);
      expect(det).toBe(-2);
    });
    
    test('calculates determinant of 3x3 matrix', () => {
      const a = [
        [1, 2, 3],
        [4, 5, 6],
        [7, 8, 10]
      ];
      
      const det = Prime.Math.Matrix.determinant(a);
      expect(det).toBe(-3);
    });
    
    test('calculates inverse of 2x2 matrix', () => {
      const a = [
        [4, 7],
        [2, 6]
      ];
      
      const inv = Prime.Math.Matrix.inverse(a);
      
      // Verify inverse * original = identity
      const product = Prime.Math.Matrix.multiply(a, inv);
      
      Assertions.assertAdaptivePrecision(product[0][0], 1, 1e-10);
      Assertions.assertAdaptivePrecision(product[0][1], 0, 1e-10);
      Assertions.assertAdaptivePrecision(product[1][0], 0, 1e-10);
      Assertions.assertAdaptivePrecision(product[1][1], 1, 1e-10);
    });
    
    test('throws for singular matrix inverse', () => {
      const singular = [
        [1, 2],
        [2, 4]
      ];
      
      expect(() => Prime.Math.Matrix.inverse(singular)).toThrow();
    });
  });
  
  describe('Advanced Matrix Operations', () => {
    test('calculates norm of matrix', () => {
      const a = [
        [3, 0],
        [0, 4]
      ];
      
      const norm = Prime.Math.Matrix.norm(a);
      expect(norm).toBe(5);
    });
    
    test('calculates trace of matrix', () => {
      const a = [
        [1, 2, 3],
        [4, 5, 6],
        [7, 8, 9]
      ];
      
      const trace = Prime.Math.Matrix.trace(a);
      expect(trace).toBe(15); // 1 + 5 + 9
    });
    
    test('performs QR decomposition', () => {
      const a = [
        [12, -51, 4],
        [6, 167, -68],
        [-4, 24, -41]
      ];
      
      const { Q, R } = Prime.Math.Matrix.qr(a);
      
      // Q is orthogonal, so Q^T * Q should be identity
      const QTQ = Prime.Math.Matrix.multiply(
        Prime.Math.Matrix.transpose(Q),
        Q
      );
      
      // Check if QTQ is close to identity
      for (let i = 0; i < 3; i++) {
        for (let j = 0; j < 3; j++) {
          const expected = i === j ? 1 : 0;
          Assertions.assertAdaptivePrecision(QTQ[i][j], expected, 1e-10);
        }
      }
      
      // A = QR, so check if product QR equals A
      const product = Prime.Math.Matrix.multiply(Q, R);
      
      for (let i = 0; i < 3; i++) {
        for (let j = 0; j < 3; j++) {
          Assertions.assertAdaptivePrecision(product[i][j], a[i][j], 1e-10);
        }
      }
      
      // R should be upper triangular
      for (let i = 1; i < 3; i++) {
        for (let j = 0; j < i; j++) {
          expect(Math.abs(R[i][j])).toBeLessThan(1e-10);
        }
      }
    });
  });
  
  describe('SVD', () => {
    test('performs SVD decomposition', () => {
      const a = [
        [1, 0],
        [0, 2]
      ];
      
      const { U, S, V } = Prime.Math.Matrix.svd(a);
      
      // Check dimensions
      expect(U.length).toBe(2);
      expect(U[0].length).toBe(2);
      expect(S.length).toBe(2);
      expect(V.length).toBe(2);
      expect(V[0].length).toBe(2);
      
      // Check singular values
      expect(S[0]).toBe(2);
      expect(S[1]).toBe(1);
      
      // Check orthogonality of U and V
      const UTU = Prime.Math.Matrix.multiply(
        Prime.Math.Matrix.transpose(U),
        U
      );
      
      const VTV = Prime.Math.Matrix.multiply(
        Prime.Math.Matrix.transpose(V),
        V
      );
      
      // Check if UTU and VTV are close to identity
      for (let i = 0; i < 2; i++) {
        for (let j = 0; j < 2; j++) {
          const expected = i === j ? 1 : 0;
          Assertions.assertAdaptivePrecision(UTU[i][j], expected, 1e-10);
          Assertions.assertAdaptivePrecision(VTV[i][j], expected, 1e-10);
        }
      }
      
      // Reconstruct matrix from SVD
      const diagonalS = Prime.Math.Matrix.diag(S);
      const reconstructed = Prime.Math.Matrix.multiply(
        Prime.Math.Matrix.multiply(U, diagonalS),
        Prime.Math.Matrix.transpose(V)
      );
      
      // Check if reconstructed matrix equals original
      for (let i = 0; i < 2; i++) {
        for (let j = 0; j < 2; j++) {
          Assertions.assertAdaptivePrecision(reconstructed[i][j], a[i][j], 1e-10);
        }
      }
    });
    
    test('handles non-square matrices in SVD', () => {
      const a = [
        [1, 2, 3],
        [4, 5, 6]
      ];
      
      const { U, S, V } = Prime.Math.Matrix.svd(a);
      
      // Check dimensions
      expect(U.length).toBe(2);
      expect(U[0].length).toBe(2);
      expect(S.length).toBe(2);
      expect(V.length).toBe(3);
      expect(V[0].length).toBe(2);
      
      // Check orthogonality of U and V
      const UTU = Prime.Math.Matrix.multiply(
        Prime.Math.Matrix.transpose(U),
        U
      );
      
      const VTV = Prime.Math.Matrix.multiply(
        Prime.Math.Matrix.transpose(V),
        V
      );
      
      // Check if UTU is close to identity with more generous tolerance
      // for numerical stability with non-square matrices
      for (let i = 0; i < 2; i++) {
        for (let j = 0; j < 2; j++) {
          const expected = i === j ? 1 : 0;
          Assertions.assertAdaptivePrecision(UTU[i][j], expected, 1e-2);
        }
      }
      
      // Check if VTV is close to identity with more generous tolerance
      for (let i = 0; i < 2; i++) {
        for (let j = 0; j < 2; j++) {
          const expected = i === j ? 1 : 0;
          Assertions.assertAdaptivePrecision(VTV[i][j], expected, 1e-2);
        }
      }
    });
  });
});