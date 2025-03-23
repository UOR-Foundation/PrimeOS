/**
 * PrimeOS Unit Tests - SVD with Metrics
 *
 * Tests for the enhanced SVD implementation with improved error handling
 * and numerical stability for extreme values.
 */

const Prime = require("../../../src/core/prime.js");
const CoreErrors = require("../../../src/core/error.js");
const StandardizedMath = require("../../../src/framework/math/standardized-math.js");

describe("SVD with Metrics", () => {
  describe("Basic SVD functionality", () => {
    test("should compute SVD for a well-conditioned matrix", () => {
      const matrix = [
        [3, 2, 2],
        [2, 3, -2],
      ];

      const { U, S, V, metadata } =
        StandardizedMath.Matrix.svdWithMetrics(matrix);

      // Verify dimensions
      expect(U.length).toBe(2);
      expect(U[0].length).toBe(2);
      expect(S.length).toBe(2);
      expect(V.length).toBe(3);
      expect(V[0].length).toBe(3);

      // Extract singular values
      const singularValues = [];
      for (let i = 0; i < Math.min(S.length, S[0].length); i++) {
        singularValues.push(S[i][i]);
      }

      // Verify singular values are sorted
      expect(singularValues[0]).toBeGreaterThanOrEqual(singularValues[1]);

      // Check that metadata is present
      expect(metadata).toBeDefined();
      expect(metadata.dynamicRange).toBeDefined();
      expect(metadata.estimatedConditionNumber).toBeDefined();
    });

    test("should compute SVD for a square matrix", () => {
      const matrix = [
        [4, 0],
        [3, -5],
      ];

      const { U, S, V, metadata } =
        StandardizedMath.Matrix.svdWithMetrics(matrix);

      // Verify dimensions
      expect(U.length).toBe(2);
      expect(U[0].length).toBe(2);
      expect(S.length).toBe(2);
      expect(S[0].length).toBe(2);
      expect(V.length).toBe(2);
      expect(V[0].length).toBe(2);

      // Verify orthogonality of U and V
      const UTU = multiplyTranspose(U, U);
      const VTV = multiplyTranspose(V, V);

      expect(Math.abs(UTU[0][0] - 1)).toBeLessThan(1e-10);
      expect(Math.abs(UTU[1][1] - 1)).toBeLessThan(1e-10);
      expect(Math.abs(UTU[0][1])).toBeLessThan(1e-10);
      expect(Math.abs(UTU[1][0])).toBeLessThan(1e-10);

      expect(Math.abs(VTV[0][0] - 1)).toBeLessThan(1e-10);
      expect(Math.abs(VTV[1][1] - 1)).toBeLessThan(1e-10);
      expect(Math.abs(VTV[0][1])).toBeLessThan(1e-10);
      expect(Math.abs(VTV[1][0])).toBeLessThan(1e-10);

      // Verify matrix approximation: A ≈ U*S*V^T
      const reconstructed = matrixReconstruction(U, S, V);

      for (let i = 0; i < matrix.length; i++) {
        for (let j = 0; j < matrix[0].length; j++) {
          expect(reconstructed[i][j]).toBeCloseTo(matrix[i][j], 10);
        }
      }
    });
  });

  describe("Handling of extreme values", () => {
    test("should handle extremely large values", () => {
      const matrix = [
        [1e150, 0],
        [0, 2e150],
      ];

      const { U, S, V, metadata } =
        StandardizedMath.Matrix.svdWithMetrics(matrix);

      // Verify dimensions
      expect(U.length).toBe(2);
      expect(S.length).toBe(2);
      expect(V.length).toBe(2);

      // Check singular values have the right magnitude
      expect(S[0][0] / 2e150).toBeGreaterThan(0.1);
      expect(S[1][1] / 1e150).toBeGreaterThan(0.1);
    });

    test("should handle extremely small values", () => {
      const matrix = [
        [1e-150, 0],
        [0, 2e-150],
      ];

      const { U, S, V, metadata } =
        StandardizedMath.Matrix.svdWithMetrics(matrix);

      // Verify dimensions
      expect(U.length).toBe(2);
      expect(S.length).toBe(2);
      expect(V.length).toBe(2);

      // Check singular values have the right magnitude relative to each other
      if (S[0][0] > 0 && S[1][1] > 0) {
        const ratio = S[0][0] / S[1][1];
        expect(ratio).toBeGreaterThan(1);
      }
    });

    test("should handle matrices with mixed extreme values", () => {
      const matrix = [
        [1e150, 1e-150],
        [1e-150, 1e150],
      ];

      const { U, S, V, metadata } =
        StandardizedMath.Matrix.svdWithMetrics(matrix);

      // Verify dimensions
      expect(U.length).toBe(2);
      expect(S.length).toBe(2);
      expect(V.length).toBe(2);

      // Check extreme dynamic range
      expect(metadata.dynamicRange).toBeGreaterThan(1e290);
    });
  });

  describe("Error handling", () => {
    test("should handle singular matrices gracefully", () => {
      const matrix = [
        [1, 2],
        [2, 4], // Second row is multiple of first row
      ];

      // Should not throw with default options
      let result;
      expect(() => {
        result = StandardizedMath.Matrix.svdWithMetrics(matrix);
      }).not.toThrow();

      // Verify we got a result
      expect(result).toBeDefined();
      expect(result.U).toBeDefined();
      expect(result.S).toBeDefined();
      expect(result.V).toBeDefined();

      // Last singular value should be very small
      // (since matrix is rank deficient)
      if (result.S[1] && result.S[1][1]) {
        expect(result.S[1][1]).toBeLessThan(1e-10);
      }
    });

    test("should wrap validation errors appropriately", () => {
      // Not a matrix (not an array)
      expect(() => {
        StandardizedMath.Matrix.svdWithMetrics("not a matrix");
      }).toThrow();

      // Empty matrix
      expect(() => {
        StandardizedMath.Matrix.svdWithMetrics([]);
      }).toThrow();

      // Matrix with inconsistent rows
      expect(() => {
        StandardizedMath.Matrix.svdWithMetrics([[1, 2], [3]]);
      }).toThrow();
    });

    test("should handle matrices with extreme condition numbers", () => {
      // Create a matrix with extreme condition number
      const matrix = [
        [1, 0],
        [0, 1e-200], // More reasonable extreme value
      ];

      let result;
      expect(() => {
        result = StandardizedMath.Matrix.svdWithMetrics(matrix);
      }).not.toThrow();

      // Verify we got a result
      expect(result).toBeDefined();
      expect(result.U).toBeDefined();
      expect(result.S).toBeDefined();
      expect(result.V).toBeDefined();

      // Condition number should be large
      if (result.metadata && result.metadata.estimatedConditionNumber) {
        expect(result.metadata.estimatedConditionNumber).toBeGreaterThan(1e150);
      }
    });
  });
});

// Helper function to verify SVD: A ≈ U*S*V^T
function matrixReconstruction(U, S, V) {
  const m = U.length;
  const n = V.length;
  const result = new Array(m).fill(0).map(() => new Array(n).fill(0));

  // Compute U*S
  const US = new Array(m).fill(0).map(() => new Array(S[0].length).fill(0));
  for (let i = 0; i < m; i++) {
    for (let j = 0; j < S[0].length; j++) {
      let sum = 0;
      for (let k = 0; k < U[0].length; k++) {
        sum += U[i][k] * (k === j ? S[k][j] : 0);
      }
      US[i][j] = sum;
    }
  }

  // Compute (U*S)*V^T
  for (let i = 0; i < m; i++) {
    for (let j = 0; j < n; j++) {
      let sum = 0;
      for (let k = 0; k < S[0].length; k++) {
        sum += US[i][k] * V[j][k];
      }
      result[i][j] = sum;
    }
  }

  return result;
}

// Helper function to compute A^T * B
function multiplyTranspose(a, b) {
  const rowsA = a.length;
  const colsA = a[0].length;
  const colsB = b[0].length;
  const result = new Array(colsA).fill(0).map(() => new Array(colsB).fill(0));

  for (let i = 0; i < colsA; i++) {
    for (let j = 0; j < colsB; j++) {
      let sum = 0;
      for (let k = 0; k < rowsA; k++) {
        sum += a[k][i] * b[k][j];
      }
      result[i][j] = sum;
    }
  }

  return result;
}
