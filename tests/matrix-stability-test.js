/**
 * Matrix Stability Tests
 *
 * Basic tests for matrix stability with extreme values
 */

const Prime = require("../src/core");
require("../src/math/matrix-core");
require("../src/math/matrix-advanced");
require("../src/math/matrix-validation");
require("../src/math/matrix-error-handling");

describe("Matrix Stability", () => {
  describe("Basic Validation", () => {
    test("should properly identify invalid matrices", () => {
      // Matrix with NaN
      const matrixWithNaN = [
        [1, 2],
        [3, NaN],
      ];

      // Matrix with Infinity
      const matrixWithInfinity = [
        [1, Infinity],
        [3, 4],
      ];

      // Check if validation can detect these issues
      expect(Prime.Math.MatrixValidation.hasInvalidValues(matrixWithNaN)).toBe(true);
      expect(Prime.Math.MatrixValidation.hasInvalidValues(matrixWithInfinity)).toBe(true);
    });

    test("should correctly identify nearly singular matrices", () => {
      // Create a nearly singular matrix (determinant very close to zero)
      const nearlySingular = [
        [1, 2, 3],
        [2, 4, 6.00000001], // Almost linearly dependent
        [3, 6, 9.00000002],
      ];

      // Very close to singular
      const almostSingular = [
        [1, 2],
        [1.0000000000001, 2.0000000000002],
      ];

      // Verify that the matrix validation correctly identifies the issue
      expect(Prime.Math.MatrixValidation.isNearlySingular(nearlySingular)).toBe(true);
      expect(Prime.Math.MatrixValidation.isNearlySingular(almostSingular)).toBe(true);
    });
  });

  describe("Error Handling", () => {
    test("should provide pseudoinverse for singular matrices", () => {
      // Singular matrix
      const singularMatrix = [
        [1, 2, 3],
        [4, 5, 6],
        [7, 8, 9], // Linearly dependent row
      ];

      // Create the pseudoinverse directly
      const pseudoInverse = Prime.Math.MatrixErrorHandling.pseudoInverse(singularMatrix);

      // Check basic properties
      expect(pseudoInverse).toBeDefined();
      expect(pseudoInverse.length).toBe(3);
      expect(pseudoInverse[0].length).toBe(3);

      // All values should be finite
      for (let i = 0; i < 3; i++) {
        for (let j = 0; j < 3; j++) {
          expect(Number.isFinite(pseudoInverse[i][j])).toBe(true);
        }
      }
    });

    test("should handle extreme values with scaling", () => {
      // Create a matrix with very small values
      const smallMatrix = [
        [1e-150, 1e-200],
        [1e-200, 1e-150],
      ];

      // Use error handling directly
      const result = Prime.Math.MatrixErrorHandling.handleExtremeValues(
        Prime.Math.MatrixAdvanced.determinant,
        [smallMatrix]
      );

      // Result should be finite
      expect(Number.isFinite(result)).toBe(true);
    });
  });

  describe("Matrix Decompositions", () => {
    test("should compute stable Cholesky decomposition", () => {
      // Create a positive-definite matrix with extreme values
      const extremeMatrix = [
        [1e200, 0],
        [0, 1e-200],
      ];

      // First create a symmetric matrix
      const symmetricMatrix = [
        [1e-150, 1e-200],
        [1e-200, 3e-150], // Make diagonal entry larger than square of off-diagonal
      ];

      // Should be symmetric
      expect(Prime.Math.MatrixValidation.isSymmetric(symmetricMatrix)).toBe(true);

      // Use error handling for Cholesky decomposition
      const result = Prime.Math.MatrixErrorHandling.handleExtremeValues(
        Prime.Math.MatrixAdvanced.choleskyDecomposition,
        [symmetricMatrix]
      );

      // Result should be a lower triangular matrix
      expect(result).toBeDefined();
      expect(result[0][1]).toBe(0); // Upper triangular part should be zero
      expect(Number.isFinite(result[1][0])).toBe(true); // Lower triangular part should be finite
    });
  });
});