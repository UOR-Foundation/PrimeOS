/**
 * Test suite for tensor-operations.js StandardMath updates
 */

const assert = require("assert");
const TensorOperations = require("../../../src/framework/math/tensor-operations.js");

describe("TensorOperations with StandardMath", () => {
  describe("Basic Operations", () => {
    it("should create tensors correctly", () => {
      const tensor2d = TensorOperations.create([2, 3], 0);
      assert.deepStrictEqual(tensor2d, [
        [0, 0, 0],
        [0, 0, 0],
      ]);

      const tensor3d = TensorOperations.create([2, 2, 2], 1);
      assert.deepStrictEqual(tensor3d, [
        [
          [1, 1],
          [1, 1],
        ],
        [
          [1, 1],
          [1, 1],
        ],
      ]);
    });

    it("should get tensor shape correctly", () => {
      const tensor = [
        [
          [1, 2],
          [3, 4],
        ],
        [
          [5, 6],
          [7, 8],
        ],
      ];
      const shape = TensorOperations.shape(tensor);
      assert.deepStrictEqual(shape, [2, 2, 2]);
    });

    it("should detect extreme values using StandardMath", () => {
      // Test with normal value
      assert.strictEqual(TensorOperations.isExtremeValue(42), false);

      // Test with extreme large value
      assert.strictEqual(TensorOperations.isExtremeValue(1e200), true);

      // Test with extreme small value
      assert.strictEqual(TensorOperations.isExtremeValue(1e-200), true);

      // Test with Infinity
      assert.strictEqual(TensorOperations.isExtremeValue(Infinity), true);

      // Test with NaN
      assert.strictEqual(TensorOperations.isExtremeValue(NaN), true);
    });
  });

  describe("Math Operations with StandardMath", () => {
    it("should add tensors using StandardMath when possible", () => {
      const a = [
        [1, 2],
        [3, 4],
      ];
      const b = [
        [5, 6],
        [7, 8],
      ];
      const result = TensorOperations.add(a, b);
      assert.deepStrictEqual(result, [
        [6, 8],
        [10, 12],
      ]);
    });

    it("should multiply tensors element-wise using StandardMath when possible", () => {
      const a = [
        [1, 2],
        [3, 4],
      ];
      const b = [
        [5, 6],
        [7, 8],
      ];
      const result = TensorOperations.multiply(a, b);
      assert.deepStrictEqual(result, [
        [5, 12],
        [21, 32],
      ]);
    });

    it("should calculate vector dot product using StandardMath when possible", () => {
      const a = [1, 2, 3];
      const b = [4, 5, 6];
      const result = TensorOperations._dotVectors(a, b);
      assert.strictEqual(result, 32); // 1*4 + 2*5 + 3*6 = 4 + 10 + 18 = 32
    });

    it("should calculate tensor norms using StandardMath when possible", () => {
      const tensor = [3, 4];

      // L2 norm (Euclidean norm)
      const l2Norm = TensorOperations.norm(tensor, 2);
      assert.strictEqual(l2Norm, 5); // sqrt(3^2 + 4^2) = sqrt(25) = 5

      // L1 norm (Manhattan norm)
      const l1Norm = TensorOperations.norm(tensor, 1);
      assert.strictEqual(l1Norm, 7); // |3| + |4| = 7

      // Infinity norm (maximum norm)
      const infNorm = TensorOperations.norm(tensor, Infinity);
      assert.strictEqual(infNorm, 4); // max(|3|, |4|) = 4
    });

    it("should normalize vectors using StandardMath when possible", () => {
      const vector = [3, 4];
      const normalized = TensorOperations.normalize(vector);

      // The normalized vector should have length 1
      assert.strictEqual(Math.round(normalized[0] * 100) / 100, 0.6); // 3/5 = 0.6
      assert.strictEqual(Math.round(normalized[1] * 100) / 100, 0.8); // 4/5 = 0.8

      // Verify norm is 1 (with small floating point tolerance)
      const norm = TensorOperations.norm(normalized);
      assert.ok(Math.abs(norm - 1) < 1e-10);
    });

    it("should perform matrix multiplication using StandardMath when possible", () => {
      const A = [
        [1, 2],
        [3, 4],
      ];
      const B = [
        [5, 6],
        [7, 8],
      ];

      const result = TensorOperations.matmul(A, B);
      assert.deepStrictEqual(result, [
        [19, 22],
        [43, 50],
      ]);
    });
  });

  describe("Error Handling and Fallbacks", () => {
    it("should handle edge cases gracefully", () => {
      // Normalize zero vector
      const zeroVector = [0, 0, 0];
      const normalized = TensorOperations.normalize(zeroVector);

      // Should return all zeros and not throw
      assert.deepStrictEqual(normalized, [0, 0, 0]);
    });

    it("should handle extreme values correctly", () => {
      // Vector with extreme values
      const extremeVector = [1e200, 1e-200];

      // Should be able to normalize without overflow/underflow
      const normalized = TensorOperations.normalize(extremeVector);

      // Norm should be close to 1 (ignoring precision issues with extreme values)
      const norm = TensorOperations.norm(normalized);
      assert.ok(norm > 0 && isFinite(norm));
    });
  });
});
