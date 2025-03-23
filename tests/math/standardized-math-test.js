/**
 * Tests for the standardized math interface
 */

const Prime = require("../../src/core/prime.js");
const StandardMath = require("../../src/framework/math/index.js").Standard;

describe("StandardizedMath", () => {
  describe("Constants", () => {
    test("should have all required constants", () => {
      expect(StandardMath.constants).toBeDefined();
      expect(StandardMath.constants.PI).toBeCloseTo(Math.PI, 15);
      expect(StandardMath.constants.E).toBeCloseTo(Math.E, 15);
      expect(StandardMath.constants.EPSILON).toBeDefined();
      expect(StandardMath.constants.MACHINE_EPSILON).toBeDefined();
    });
  });

  describe("Vector operations", () => {
    test("should create vectors", () => {
      const v1 = StandardMath.Vector.create([1, 2, 3]);
      expect(v1).toBeDefined();
      expect(v1.values).toEqual([1, 2, 3]);

      const v2 = StandardMath.Vector.zeros(3);
      expect(v2.values).toEqual([0, 0, 0]);

      const v3 = StandardMath.Vector.ones(3);
      expect(v3.values).toEqual([1, 1, 1]);
    });

    test("should perform vector addition", () => {
      const v1 = StandardMath.Vector.create([1, 2, 3]);
      const v2 = StandardMath.Vector.create([4, 5, 6]);
      const result = StandardMath.Vector.add(v1, v2);
      expect(result.values).toEqual([5, 7, 9]);
    });

    test("should calculate vector norms", () => {
      const v = StandardMath.Vector.create([3, 4]);
      const norm = StandardMath.Vector.norm(v);
      expect(norm).toBeCloseTo(5, 10);
    });

    test("should normalize vectors", () => {
      const v = StandardMath.Vector.create([3, 4]);
      const normalized = StandardMath.Vector.normalize(v);
      expect(normalized.values[0]).toBeCloseTo(0.6, 10);
      expect(normalized.values[1]).toBeCloseTo(0.8, 10);
    });

    test("should calculate dot products", () => {
      const v1 = StandardMath.Vector.create([1, 2, 3]);
      const v2 = StandardMath.Vector.create([4, 5, 6]);
      const dot = StandardMath.Vector.dot(v1, v2);
      expect(dot).toEqual(32);
    });
  });

  describe("Matrix operations", () => {
    test("should create matrices", () => {
      const m1 = StandardMath.Matrix.create([
        [1, 2],
        [3, 4],
      ]);
      expect(m1).toBeDefined();
      expect(m1.rows).toEqual(2);
      expect(m1.cols).toEqual(2);

      const m2 = StandardMath.Matrix.zeros(2, 3);
      expect(m2.rows).toEqual(2);
      expect(m2.cols).toEqual(3);
      expect(m2.get(0, 0)).toEqual(0);

      const m3 = StandardMath.Matrix.identity(3);
      expect(m3.get(0, 0)).toEqual(1);
      expect(m3.get(1, 1)).toEqual(1);
      expect(m3.get(2, 2)).toEqual(1);
      expect(m3.get(0, 1)).toEqual(0);
    });

    test("should perform matrix addition", () => {
      const m1 = StandardMath.Matrix.create([
        [1, 2],
        [3, 4],
      ]);
      const m2 = StandardMath.Matrix.create([
        [5, 6],
        [7, 8],
      ]);
      const result = StandardMath.Matrix.add(m1, m2);
      expect(result.get(0, 0)).toEqual(6);
      expect(result.get(0, 1)).toEqual(8);
      expect(result.get(1, 0)).toEqual(10);
      expect(result.get(1, 1)).toEqual(12);
    });

    test("should perform matrix multiplication", () => {
      const m1 = StandardMath.Matrix.create([
        [1, 2],
        [3, 4],
      ]);
      const m2 = StandardMath.Matrix.create([
        [5, 6],
        [7, 8],
      ]);
      const result = StandardMath.Matrix.multiply(m1, m2);
      expect(result.get(0, 0)).toEqual(19);
      expect(result.get(0, 1)).toEqual(22);
      expect(result.get(1, 0)).toEqual(43);
      expect(result.get(1, 1)).toEqual(50);
    });

    test("should calculate matrix determinant", () => {
      const m = StandardMath.Matrix.create([
        [1, 2],
        [3, 4],
      ]);
      const det = StandardMath.Matrix.determinant(m);
      expect(det).toEqual(-2);
    });

    test("should calculate matrix inverse", () => {
      const m = StandardMath.Matrix.create([
        [1, 2],
        [3, 4],
      ]);
      const inv = StandardMath.Matrix.inverse(m);
      expect(inv.get(0, 0)).toBeCloseTo(-2, 10);
      expect(inv.get(0, 1)).toBeCloseTo(1, 10);
      expect(inv.get(1, 0)).toBeCloseTo(1.5, 10);
      expect(inv.get(1, 1)).toBeCloseTo(-0.5, 10);
    });
  });

  describe("Tensor operations", () => {
    test("should create tensors", () => {
      const t1 = new StandardMath.Tensor([2, 3]);
      expect(t1).toBeDefined();
      expect(t1.getShape()).toEqual([2, 3]);

      const t2 = StandardMath.Tensor.zeros([2, 2, 2]);
      expect(t2.getShape()).toEqual([2, 2, 2]);
      expect(t2.get([0, 0, 0])).toEqual(0);

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
      expect(t3.getShape()).toEqual([2, 2, 2]);
      expect(t3.get([0, 0, 0])).toEqual(1);
      expect(t3.get([1, 1, 1])).toEqual(8);
    });

    test("should perform tensor addition", () => {
      const t1 = StandardMath.Tensor.fromArray([
        [1, 2],
        [3, 4],
      ]);
      const t2 = StandardMath.Tensor.fromArray([
        [5, 6],
        [7, 8],
      ]);
      const result = t1.add(t2);
      expect(result.get([0, 0])).toEqual(6);
      expect(result.get([0, 1])).toEqual(8);
      expect(result.get([1, 0])).toEqual(10);
      expect(result.get([1, 1])).toEqual(12);
    });

    test("should perform tensor multiplication", () => {
      const t1 = StandardMath.Tensor.fromArray([
        [1, 2],
        [3, 4],
      ]);
      const t2 = StandardMath.Tensor.fromArray([
        [5, 6],
        [7, 8],
      ]);
      const result = t1.matmul(t2);
      expect(result.get([0, 0])).toEqual(19);
      expect(result.get([0, 1])).toEqual(22);
      expect(result.get([1, 0])).toEqual(43);
      expect(result.get([1, 1])).toEqual(50);
    });

    test("should calculate tensor norms", () => {
      const t = StandardMath.Tensor.fromArray([3, 4]);
      const norm = t.norm();
      expect(norm).toBeCloseTo(5, 10);
    });

    test("should reshape tensors", () => {
      const t = StandardMath.Tensor.fromArray([
        [1, 2],
        [3, 4],
      ]);
      const reshaped = t.reshape([4]);
      expect(reshaped.getShape()).toEqual([4]);
      expect(reshaped.get([0])).toEqual(1);
      expect(reshaped.get([1])).toEqual(2);
      expect(reshaped.get([2])).toEqual(3);
      expect(reshaped.get([3])).toEqual(4);
    });
  });

  describe("Advanced math operations", () => {
    test("should calculate square root with enhanced precision", () => {
      expect(StandardMath.sqrt(4)).toEqual(2);
      expect(StandardMath.sqrt(2)).toBeCloseTo(Math.SQRT2, 15);
    });

    test("should calculate powers with enhanced precision", () => {
      expect(StandardMath.pow(2, 3)).toEqual(8);
      expect(StandardMath.pow(10, -2)).toEqual(0.01);
    });

    test("should calculate exponential function with enhanced precision", () => {
      expect(StandardMath.exp(0)).toEqual(1);
      expect(StandardMath.exp(1)).toBeCloseTo(Math.E, 15);
    });

    test("should calculate derivatives", () => {
      const f = (x) => x * x;
      const derivative = StandardMath.derivative(f, 2);
      expect(derivative).toBeCloseTo(4, 5);
    });

    test("should calculate integrals", () => {
      const f = (x) => x;
      const integral = StandardMath.integrate(f, 0, 1);
      expect(integral).toBeCloseTo(0.5, 5);
    });

    test("should interpolate values", () => {
      expect(StandardMath.lerp(0, 10, 0.5)).toEqual(5);
      expect(StandardMath.lerp(0, 10, 0)).toEqual(0);
      expect(StandardMath.lerp(0, 10, 1)).toEqual(10);
    });

    test("should clamp values", () => {
      expect(StandardMath.clamp(5, 0, 10)).toEqual(5);
      expect(StandardMath.clamp(-5, 0, 10)).toEqual(0);
      expect(StandardMath.clamp(15, 0, 10)).toEqual(10);
    });
  });

  describe("Statistics operations", () => {
    test("should calculate mean", () => {
      expect(StandardMath.Statistics.mean([1, 2, 3, 4, 5])).toEqual(3);
    });

    test("should calculate variance", () => {
      expect(StandardMath.Statistics.variance([1, 2, 3, 4, 5])).toEqual(2);
    });

    test("should calculate standard deviation", () => {
      expect(
        StandardMath.Statistics.standardDeviation([1, 2, 3, 4, 5]),
      ).toBeCloseTo(Math.sqrt(2), 10);
    });
  });

  describe("Error handling", () => {
    test("should validate inputs properly", () => {
      // Vector operations
      expect(() => StandardMath.Vector.create("not an array")).toThrow();

      // Matrix operations
      expect(() => StandardMath.Matrix.determinant([[1, 2], [3]])).toThrow();

      // Tensor operations
      expect(() => new StandardMath.Tensor([-1, 2])).toThrow();

      // Advanced math operations
      expect(() => StandardMath.sqrt(-1)).toThrow();
    });

    test("should handle numerical stability edge cases", () => {
      // Test with extreme values
      const largeValue = 1e100;
      const smallValue = 1e-100;

      // These operations should not throw or return NaN/Infinity
      expect(isFinite(StandardMath.adaptiveEpsilon(largeValue))).toBe(true);
      expect(isFinite(StandardMath.adaptiveEpsilon(smallValue))).toBe(true);

      // Kahan sum should handle extreme values
      const sumResult = StandardMath.kahanSum([
        largeValue,
        smallValue,
        -largeValue,
      ]);
      expect(isFinite(sumResult.sum)).toBe(true);
    });
  });
});
