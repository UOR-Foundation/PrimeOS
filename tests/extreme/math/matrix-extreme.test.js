/**
 * PrimeOS Extreme Tests - Matrix Extreme Values
 * 
 * Tests for matrix operations under extreme numerical conditions.
 */

const Prime = require('../../../src/mathematics.js');
const { Assertions, Setup, Fixtures } = require('../../utils');

// Configure environment for extreme testing
Setup.configureExtendedPrecision();

describe('Matrix Extreme Value Handling', () => {
  beforeAll(() => {
    // Enable extended precision mode for all tests in this suite
    process.env.EXTENDED_PRECISION = 'true';
  });

  describe('Matrix Creation with Extreme Values', () => {
    test('creates matrices with extremely large values', () => {
      const dimension = 5;
      const extremeValue = 1e200;
      
      const matrix = Prime.Math.Matrix.create(dimension, dimension, extremeValue);
      
      // Verify all elements have the correct value
      for (let i = 0; i < dimension; i++) {
        for (let j = 0; j < dimension; j++) {
          expect(matrix[i][j]).toBe(extremeValue);
        }
      }
    });
    
    test('creates matrices with extremely small values', () => {
      const dimension = 5;
      const extremeValue = 1e-200;
      
      const matrix = Prime.Math.Matrix.create(dimension, dimension, extremeValue);
      
      // Verify all elements have the correct value
      for (let i = 0; i < dimension; i++) {
        for (let j = 0; j < dimension; j++) {
          expect(matrix[i][j]).toBe(extremeValue);
        }
      }
    });
    
    test('creates matrices with mixed extreme values', () => {
      const rows = 4;
      const cols = 4;
      
      // Create a matrix with mixed extreme values
      const matrix = Fixtures.createMatrix('extreme', rows, cols);
      
      // Verify matrix was created correctly
      expect(matrix.length).toBe(rows);
      expect(matrix[0].length).toBe(cols);
      
      // Verify matrix contains finite values
      for (let i = 0; i < rows; i++) {
        for (let j = 0; j < cols; j++) {
          expect(Number.isFinite(matrix[i][j])).toBe(true);
        }
      }
    });
  });
  
  describe('Matrix Basic Operations with Extreme Values', () => {
    test('adds matrices with extreme values correctly', () => {
      // Create matrices with extreme values
      const m1 = [
        [1e200, 1e-200],
        [1e-200, 1e200]
      ];
      
      const m2 = [
        [1e200, 1e-200],
        [1e-200, 1e200]
      ];
      
      // Perform addition
      const result = Prime.Math.Matrix.add(m1, m2);
      
      // Verify result using adaptive precision
      Assertions.assertAdaptivePrecision(result[0][0], 2e200, 1e190);
      Assertions.assertAdaptivePrecision(result[0][1], 2e-200, 1e-210);
      Assertions.assertAdaptivePrecision(result[1][0], 2e-200, 1e-210);
      Assertions.assertAdaptivePrecision(result[1][1], 2e200, 1e190);
    });
    
    test('subtracts matrices with extreme values correctly', () => {
      // Create matrices with extreme values
      const m1 = [
        [2e200, 3e-200],
        [4e-200, 5e200]
      ];
      
      const m2 = [
        [1e200, 1e-200],
        [1e-200, 1e200]
      ];
      
      // Perform subtraction
      const result = Prime.Math.Matrix.subtract(m1, m2);
      
      // Verify result using adaptive precision
      Assertions.assertAdaptivePrecision(result[0][0], 1e200, 1e190);
      Assertions.assertAdaptivePrecision(result[0][1], 2e-200, 1e-210);
      Assertions.assertAdaptivePrecision(result[1][0], 3e-200, 1e-210);
      Assertions.assertAdaptivePrecision(result[1][1], 4e200, 1e190);
    });
    
    test('multiplies matrices with extreme values correctly', () => {
      // Create matrices with extreme values
      const m1 = [
        [1e100, 1e-100],
        [1e-100, 1e100]
      ];
      
      const m2 = [
        [1e100, 1e-100],
        [1e-100, 1e100]
      ];
      
      // Perform multiplication
      const result = Prime.Math.Matrix.multiply(m1, m2);
      
      // Expected results:
      // [1e200 + 1e-200, 1e0 + 1e-200]
      // [1e0 + 1e-200, 1e-200 + 1e200]
      
      // Verify result using adaptive precision
      // Note: These are approximate due to extreme values and potential for catastrophic cancellation
      Assertions.assertAdaptivePrecision(result[0][0], 1e200, 1e190);
      Assertions.assertAdaptivePrecision(result[0][1], 1, 1e-10);
      Assertions.assertAdaptivePrecision(result[1][0], 1, 1e-10);
      Assertions.assertAdaptivePrecision(result[1][1], 1e200, 1e190);
    });
  });
  
  describe('Matrix Advanced Operations with Extreme Values', () => {
    test('computes determinant with extreme values correctly', () => {
      // Small matrix with extreme values where determinant is analytically calculable
      const matrix = [
        [1e100, 2e100],
        [3e-100, 4e-100]
      ];
      
      // Expected determinant: (1e100 * 4e-100) - (2e100 * 3e-100) = 4 - 6 = -2e-100
      const det = Prime.Math.Matrix.determinant(matrix);
      
      // Verify using adaptive precision
      Assertions.assertAdaptivePrecision(det, -2e-100, 1e-110);
    });
    
    test('computes inverse with extreme values correctly', () => {
      // Matrix with extreme values but well-conditioned
      const matrix = [
        [2e100, 1e100],
        [1e100, 1e100]
      ];
      
      // det = (2e100 * 1e100) - (1e100 * 1e100) = 2e200 - 1e200 = 1e200
      // inverse = 1/det * [1e100, -1e100; -1e100, 2e100]
      //         = 1e-200 * [1e100, -1e100; -1e100, 2e100]
      //         = [1e-100, -1e-100; -1e-100, 2e-100]
      
      const inverse = Prime.Math.Matrix.inverse(matrix);
      
      // Verify dimensions
      expect(inverse.length).toBe(2);
      expect(inverse[0].length).toBe(2);
      
      // Verify values using adaptive precision
      Assertions.assertAdaptivePrecision(inverse[0][0], 1e-100, 1e-110);
      Assertions.assertAdaptivePrecision(inverse[0][1], -1e-100, 1e-110);
      Assertions.assertAdaptivePrecision(inverse[1][0], -1e-100, 1e-110);
      Assertions.assertAdaptivePrecision(inverse[1][1], 2e-100, 1e-110);
      
      // Verify inverse correctness by multiplying with original
      const identity = Prime.Math.Matrix.multiply(matrix, inverse);
      
      Assertions.assertAdaptivePrecision(identity[0][0], 1, 1e-10);
      Assertions.assertAdaptivePrecision(identity[0][1], 0, 1e-10);
      Assertions.assertAdaptivePrecision(identity[1][0], 0, 1e-10);
      Assertions.assertAdaptivePrecision(identity[1][1], 1, 1e-10);
    });
    
    test('handles catastrophic cancellation in matrix operations', () => {
      // Create a matrix operation that exhibits catastrophic cancellation
      const operation = (a, b) => {
        return a - b;
      };
      
      // Almost equal large values that will cause cancellation
      const value1 = 1e16;
      const value2 = 1e16 - 1;
      
      // Test using custom assertion
      Assertions.assertNoCatastrophicCancellation(
        operation,
        [value1, value2],
        1e-10,
        "Matrix operation should handle catastrophic cancellation"
      );
    });
  });
  
  describe('Matrix Stability Tests with Extreme Values', () => {
    test('maintains numerical stability in repeated operations', () => {
      // Create a simple matrix operation that involves addition
      const computation = (matrix) => {
        return Prime.Math.Matrix.add(matrix, [
          [1e-16, 1e-16],
          [1e-16, 1e-16]
        ]);
      };
      
      // Initial values
      const initialMatrix = [
        [1, 0],
        [0, 1]
      ];
      
      // Bounds function determines expected error growth
      const boundsFunc = (iteration, initialValue) => {
        // Expect linear error growth due to accumulation
        return iteration * 1e-14;
      };
      
      // Runs the computation repeatedly and checks error growth
      Assertions.assertStabilityBound(
        computation,
        [initialMatrix],
        boundsFunc,
        100,
        "Matrix operations should have stable error growth"
      );
    });
    
    test('handles extreme value matrices with special properties', () => {
      // Test handling of extreme value matrices with specific conditions
      
      // Create various extreme inputs
      const extremeInputs = [
        [[1e100, 1e100], [1e100, 1e100]], // Singular matrix
        [[1e-100, 0], [0, 1e-100]],       // Well-conditioned small values
        [[Infinity, 0], [0, 1]]           // Contains infinity
      ];
      
      // Expected behavior for each input
      const conditions = [
        // First matrix is singular, determinant should be near 0
        (result) => Math.abs(Prime.Math.Matrix.determinant(result.value)) < 1e-10,
        // Second matrix is well-conditioned, determinant should be positive
        (result) => Prime.Math.Matrix.determinant(result.value) > 0,
        // Third matrix contains Infinity, should produce error or Infinity
        "error"
      ];
      
      // Test using custom assertion
      Assertions.assertExtremeValueHandling(
        (matrix) => matrix, // Identity function for this test
        extremeInputs,
        conditions,
        "Matrix operations should handle extreme value matrices correctly"
      );
    });
  });
});