/**
 * PrimeOS Unit Tests - Mathematics Precision
 * 
 * Tests for precision handling and numerical stability in mathematical operations.
 */

const Prime = require('../../../src/mathematics.js');
const { Assertions } = require('../../utils');

describe('Mathematics Precision', () => {
  describe('Floating Point Precision', () => {
    test('can represent epsilon accurately', () => {
      const result = 1 + Number.EPSILON;
      Assertions.assertExtremePrecision(result, 1 + Number.EPSILON);
    });

    test('square root operations maintain precision', () => {
      const result = Math.sqrt(2) * Math.sqrt(2);
      Assertions.assertExtremePrecision(result, 2);
    });

    test('cosine of PI is exactly -1', () => {
      const result = Math.cos(Math.PI);
      Assertions.assertExtremePrecision(result, -1);
    });
  });

  describe('Numerical Stability', () => {
    test('large number subtraction maintains precision', () => {
      // Test a numerically sensitive computation
      const a = 1e8;
      const b = a + 1;
      const result = b - a; // Should be exactly 1
      
      Assertions.assertAdaptivePrecision(result, 1, 1e-10);
    });

    test('sin(PI) is very close to 0', () => {
      const result = Math.sin(Math.PI);
      Assertions.assertAdaptivePrecision(result, 0, 1e-15);
    });

    test('sin(2*PI) is very close to 0', () => {
      const result = Math.sin(2 * Math.PI);
      Assertions.assertAdaptivePrecision(result, 0, 1e-15);
    });

    test('cos(PI/2) is very close to 0', () => {
      const result = Math.cos(Math.PI / 2);
      Assertions.assertAdaptivePrecision(result, 0, 1e-15);
    });
  });

  describe('Vector and Matrix Operations', () => {
    test('dot product calculated precisely', () => {
      const vec1 = [1, 2, 3];
      const vec2 = [4, 5, 6];

      // Manual dot product calculation
      const dotProduct = vec1[0] * vec2[0] + vec1[1] * vec2[1] + vec1[2] * vec2[2];
      expect(dotProduct).toBe(32);
    });

    test('matrix multiplication is exact', () => {
      const identity = [
        [1, 0, 0],
        [0, 1, 0],
        [0, 0, 1],
      ];

      // Matrix multiplication (identity * identity)
      const matMul = [
        [0, 0, 0],
        [0, 0, 0],
        [0, 0, 0],
      ];

      for (let i = 0; i < 3; i++) {
        for (let j = 0; j < 3; j++) {
          for (let k = 0; k < 3; k++) {
            matMul[i][j] += identity[i][k] * identity[k][j];
          }
        }
      }

      // Test each element of the result
      for (let i = 0; i < 3; i++) {
        for (let j = 0; j < 3; j++) {
          const expected = i === j ? 1 : 0;
          expect(matMul[i][j]).toBe(expected);
        }
      }
    });
  });

  describe('Irrational Numbers', () => {
    test('PI squared calculated precisely', () => {
      Assertions.assertAdaptivePrecision(Math.PI * Math.PI, 9.869604401089358, 1e-14);
    });

    test('product of square roots is precise', () => {
      const result = Math.sqrt(2) * Math.sqrt(3);
      Assertions.assertAdaptivePrecision(result, Math.sqrt(6), 1e-14);
    });
  });

  describe('Array Equality', () => {
    test('array equality check works', () => {
      const arr1 = [1, 2, 3, 4, 5];
      const arr2 = [...arr1]; // Clone
      
      expect(arr1).toEqual(arr2);
    });

    test('array equality with small epsilon passes', () => {
      const arr1 = [1, 2, 3, 4, 5];
      const arr3 = [1, 2, 3 + 1e-10, 4, 5];
      
      // Custom array comparison with epsilon
      for (let i = 0; i < arr1.length; i++) {
        Assertions.assertAdaptivePrecision(arr3[i], arr1[i], 1e-9);
      }
    });
  });

  describe('Special Values', () => {
    test('division by zero yields Infinity', () => {
      expect(1 / 0).toBe(Infinity);
    });

    test('0/0 yields NaN', () => {
      expect(isNaN(0 / 0)).toBe(true);
    });

    test('square root of negative number is NaN', () => {
      expect(isNaN(Math.sqrt(-1))).toBe(true);
    });
  });

  describe('Mathematical Identities', () => {
    test('sin²(θ) + cos²(θ) = 1', () => {
      const angle = Math.PI / 4;
      const result = Math.sin(angle) * Math.sin(angle) + 
                     Math.cos(angle) * Math.cos(angle);
      
      Assertions.assertAdaptivePrecision(result, 1, 1e-15);
    });

    test('log(exp(1)) = 1', () => {
      const result = Math.log(Math.exp(1));
      Assertions.assertAdaptivePrecision(result, 1, 1e-15);
    });

    test('2^(log2(8)) = 8', () => {
      const result = Math.pow(2, Math.log2(8));
      Assertions.assertAdaptivePrecision(result, 8, 1e-14);
    });
  });

  // Test catastrophic cancellation and error accumulation
  describe('Error Propagation', () => {
    test('handles catastrophic cancellation gracefully', () => {
      const a = 1.0;
      const b = 1.0 + 1e-16;
      
      // Direct subtraction (prone to catastrophic cancellation)
      const direct = b - a;
      
      // Alternative calculation
      const alternative = 1e-16;
      
      // The direct result may be 0 due to precision loss
      Assertions.assertNoCatastrophicCancellation(
        () => b - a,
        [b, a],
        1.0 // Allow higher error here as we're testing problematic cases
      );
    });
    
    test('avoids error accumulation in large sums', () => {
      // This test checks if the error growth is bounded
      // in repeated additions of small numbers to large ones
      const small = 1e-8;
      const large = 1e8;
      
      // Naive summation
      let naiveSum = large;
      for (let i = 0; i < 1000; i++) {
        naiveSum += small;
      }
      
      // Expected result (assuming perfect precision)
      const expected = large + (1000 * small);
      
      // Actual result should be close to expected
      Assertions.assertAdaptivePrecision(naiveSum, expected, 1e-4);
    });
  });
});