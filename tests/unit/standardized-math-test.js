/**
 * Tests for the standardized math interface
 */

const Prime = require("../../src/core/prime.js");
const StandardMath = require("../../src/framework/math/index.js").Standard;

// Add tests to the test suite
describe("StandardizedMath", function () {
  describe("Constants", function () {
    it("should have all required constants", function () {
      assert.ok(StandardMath.constants);
      assert.closeTo(StandardMath.constants.PI, Math.PI, 1e-15);
      assert.closeTo(StandardMath.constants.E, Math.E, 1e-15);
      assert.ok(StandardMath.constants.EPSILON);
      assert.ok(StandardMath.constants.MACHINE_EPSILON);
    });
  });

  describe("Vector operations", function () {
    it("should create vectors", function () {
      const v1 = StandardMath.Vector.create([1, 2, 3]);
      assert.ok(v1);
      assert.deepEqual(v1.values, [1, 2, 3]);

      const v2 = StandardMath.Vector.zeros(3);
      assert.deepEqual(v2.values, [0, 0, 0]);

      const v3 = StandardMath.Vector.ones(3);
      assert.deepEqual(v3.values, [1, 1, 1]);
    });

    it("should perform vector addition", function () {
      const v1 = StandardMath.Vector.create([1, 2, 3]);
      const v2 = StandardMath.Vector.create([4, 5, 6]);
      const result = StandardMath.Vector.add(v1, v2);
      assert.deepEqual(result.values, [5, 7, 9]);
    });

    it("should calculate vector norms", function () {
      const v = StandardMath.Vector.create([3, 4]);
      const norm = StandardMath.Vector.norm(v);
      assert.closeTo(norm, 5, 1e-10);
    });

    it("should normalize vectors", function () {
      const v = StandardMath.Vector.create([3, 4]);
      const normalized = StandardMath.Vector.normalize(v);
      assert.closeTo(normalized.values[0], 0.6, 1e-10);
      assert.closeTo(normalized.values[1], 0.8, 1e-10);
    });

    it("should calculate dot products", function () {
      const v1 = StandardMath.Vector.create([1, 2, 3]);
      const v2 = StandardMath.Vector.create([4, 5, 6]);
      const dot = StandardMath.Vector.dot(v1, v2);
      assert.equal(dot, 32);
    });
  });

  describe("Matrix operations", function () {
    it("should create matrices", function () {
      const m1 = StandardMath.Matrix.create([
        [1, 2],
        [3, 4],
      ]);
      assert.ok(m1);
      assert.equal(m1.rows, 2);
      assert.equal(m1.cols, 2);

      const m2 = StandardMath.Matrix.zeros(2, 3);
      assert.equal(m2.rows, 2);
      assert.equal(m2.cols, 3);
      assert.equal(m2.get(0, 0), 0);

      const m3 = StandardMath.Matrix.identity(3);
      assert.equal(m3.get(0, 0), 1);
      assert.equal(m3.get(1, 1), 1);
      assert.equal(m3.get(2, 2), 1);
      assert.equal(m3.get(0, 1), 0);
    });

    it("should perform matrix addition", function () {
      const m1 = StandardMath.Matrix.create([
        [1, 2],
        [3, 4],
      ]);
      const m2 = StandardMath.Matrix.create([
        [5, 6],
        [7, 8],
      ]);
      const result = StandardMath.Matrix.add(m1, m2);
      assert.equal(result.get(0, 0), 6);
      assert.equal(result.get(0, 1), 8);
      assert.equal(result.get(1, 0), 10);
      assert.equal(result.get(1, 1), 12);
    });

    it("should perform matrix multiplication", function () {
      const m1 = StandardMath.Matrix.create([
        [1, 2],
        [3, 4],
      ]);
      const m2 = StandardMath.Matrix.create([
        [5, 6],
        [7, 8],
      ]);
      const result = StandardMath.Matrix.multiply(m1, m2);
      assert.equal(result.get(0, 0), 19);
      assert.equal(result.get(0, 1), 22);
      assert.equal(result.get(1, 0), 43);
      assert.equal(result.get(1, 1), 50);
    });

    it("should calculate matrix determinant", function () {
      const m = StandardMath.Matrix.create([
        [1, 2],
        [3, 4],
      ]);
      const det = StandardMath.Matrix.determinant(m);
      assert.equal(det, -2);
    });

    it("should calculate matrix inverse", function () {
      const m = StandardMath.Matrix.create([
        [1, 2],
        [3, 4],
      ]);
      const inv = StandardMath.Matrix.inverse(m);
      assert.closeTo(inv.get(0, 0), -2, 1e-10);
      assert.closeTo(inv.get(0, 1), 1, 1e-10);
      assert.closeTo(inv.get(1, 0), 1.5, 1e-10);
      assert.closeTo(inv.get(1, 1), -0.5, 1e-10);
    });
  });

  describe("Tensor operations", function () {
    it("should create tensors", function () {
      const t1 = new StandardMath.Tensor([2, 3]);
      assert.ok(t1);
      assert.deepEqual(t1.getShape(), [2, 3]);

      const t2 = StandardMath.Tensor.zeros([2, 2, 2]);
      assert.deepEqual(t2.getShape(), [2, 2, 2]);
      assert.equal(t2.get([0, 0, 0]), 0);

      const t3 = StandardMath.Tensor.fromArray([
        [
          [1, 2],
          [3, 4],
        ],
        [
          [5, 6],
          [7, 8],
        ],
      ]);
      assert.deepEqual(t3.getShape(), [2, 2, 2]);
      assert.equal(t3.get([0, 0, 0]), 1);
      assert.equal(t3.get([1, 1, 1]), 8);
    });

    it("should perform tensor addition", function () {
      const t1 = StandardMath.Tensor.fromArray([
        [1, 2],
        [3, 4],
      ]);
      const t2 = StandardMath.Tensor.fromArray([
        [5, 6],
        [7, 8],
      ]);
      const result = t1.add(t2);
      assert.equal(result.get([0, 0]), 6);
      assert.equal(result.get([0, 1]), 8);
      assert.equal(result.get([1, 0]), 10);
      assert.equal(result.get([1, 1]), 12);
    });

    it("should perform tensor multiplication", function () {
      const t1 = StandardMath.Tensor.fromArray([
        [1, 2],
        [3, 4],
      ]);
      const t2 = StandardMath.Tensor.fromArray([
        [5, 6],
        [7, 8],
      ]);
      const result = t1.matmul(t2);
      assert.equal(result.get([0, 0]), 19);
      assert.equal(result.get([0, 1]), 22);
      assert.equal(result.get([1, 0]), 43);
      assert.equal(result.get([1, 1]), 50);
    });

    it("should calculate tensor norms", function () {
      const t = StandardMath.Tensor.fromArray([3, 4]);
      const norm = t.norm();
      assert.closeTo(norm, 5, 1e-10);
    });

    it("should reshape tensors", function () {
      const t = StandardMath.Tensor.fromArray([
        [1, 2],
        [3, 4],
      ]);
      const reshaped = t.reshape([4]);
      assert.deepEqual(reshaped.getShape(), [4]);
      assert.equal(reshaped.get([0]), 1);
      assert.equal(reshaped.get([1]), 2);
      assert.equal(reshaped.get([2]), 3);
      assert.equal(reshaped.get([3]), 4);
    });
  });

  describe("Advanced math operations", function () {
    it("should calculate square root with enhanced precision", function () {
      assert.equal(StandardMath.sqrt(4), 2);
      assert.closeTo(StandardMath.sqrt(2), Math.SQRT2, 1e-15);
    });

    it("should calculate powers with enhanced precision", function () {
      assert.equal(StandardMath.pow(2, 3), 8);
      assert.equal(StandardMath.pow(10, -2), 0.01);
    });

    it("should calculate exponential function with enhanced precision", function () {
      assert.equal(StandardMath.exp(0), 1);
      assert.closeTo(StandardMath.exp(1), Math.E, 1e-15);
    });

    it("should interpolate values", function () {
      assert.equal(StandardMath.lerp(0, 10, 0.5), 5);
      assert.equal(StandardMath.lerp(0, 10, 0), 0);
      assert.equal(StandardMath.lerp(0, 10, 1), 10);
    });

    it("should clamp values", function () {
      assert.equal(StandardMath.clamp(5, 0, 10), 5);
      assert.equal(StandardMath.clamp(-5, 0, 10), 0);
      assert.equal(StandardMath.clamp(15, 0, 10), 10);
    });
  });

  describe("Statistics operations", function () {
    it("should calculate mean", function () {
      assert.equal(StandardMath.Statistics.mean([1, 2, 3, 4, 5]), 3);
    });

    it("should calculate variance", function () {
      assert.equal(StandardMath.Statistics.variance([1, 2, 3, 4, 5]), 2);
    });

    it("should calculate standard deviation", function () {
      assert.closeTo(
        StandardMath.Statistics.standardDeviation([1, 2, 3, 4, 5]),
        Math.sqrt(2),
        1e-10,
      );
    });
  });
});
