/**
 * PrimeOS Unit Tests - Clifford Algebra
 *
 * Tests for the Clifford Algebra implementation in the Mathematics module.
 */

const Prime = require("../../../src/mathematics.js");
const { Assertions } = require("../../utils");

describe("Clifford Algebra", () => {
  describe("Algebra Creation", () => {
    test("creates algebra with correct dimension", () => {
      const Cl3 = Prime.Clifford.create({ dimension: 3 });
      expect(Cl3.dimension).toBe(3);
      expect(Array.isArray(Cl3.signature)).toBe(true);
      expect(Cl3.signature.length).toBe(3);
      expect(Array.isArray(Cl3.basis)).toBe(true);
    });

    test("throws for negative dimension", () => {
      expect(() => Prime.Clifford.create({ dimension: -1 })).toThrow(
        Prime.ValidationError,
      );
    });

    test("throws for mismatched signature length", () => {
      expect(() =>
        Prime.Clifford.create({ dimension: 3, signature: [1, 1] }),
      ).toThrow(Prime.ValidationError);
    });

    test("preserves non-standard signature", () => {
      const ClNonStd = Prime.Clifford.create({
        dimension: 2,
        signature: [-1, -1],
      });
      expect(ClNonStd.signature).toEqual([-1, -1]);
    });
  });

  describe("Multivector Creation", () => {
    let Cl3;

    beforeEach(() => {
      Cl3 = Prime.Clifford.create({ dimension: 3 });
    });

    test("creates scalar multivector", () => {
      const scalar = Cl3.scalar(5);
      expect(Prime.Clifford.isMultivector(scalar)).toBe(true);
      expect(scalar.components[0]["1"]).toBe(5);
    });

    test("preserves tiny scalar value", () => {
      const tinyScalar = Cl3.scalar(1e-15);
      Assertions.assertExtremePrecision(tinyScalar.components[0]["1"], 1e-15);
    });

    test("creates vector multivector", () => {
      const vector = Cl3.vector([1, 2, 3]);
      expect(Prime.Clifford.isMultivector(vector)).toBe(true);
      expect(vector.components[1]["e1"]).toBe(1);
      expect(vector.components[1]["e2"]).toBe(2);
      expect(vector.components[1]["e3"]).toBe(3);
    });

    test("creates bivector multivector from matrix", () => {
      const bivectorMatrix = Cl3.bivector([
        [0, 1, 2],
        [0, 0, 3],
        [0, 0, 0],
      ]);

      expect(Prime.Clifford.isMultivector(bivectorMatrix)).toBe(true);
      expect(bivectorMatrix.components[2]["e1e2"]).toBe(1);
      expect(bivectorMatrix.components[2]["e1e3"]).toBe(2);
      expect(bivectorMatrix.components[2]["e2e3"]).toBe(3);
    });

    test("creates general multivector", () => {
      const general = Cl3.multivector({
        0: { 1: 1 },
        1: { e1: 2, e3: 3 },
        2: { e1e2: 4 },
      });

      expect(Prime.Clifford.isMultivector(general)).toBe(true);
      expect(general.components[0]["1"]).toBe(1);
      expect(general.components[1]["e1"]).toBe(2);
      expect(general.components[1]["e3"]).toBe(3);
      expect(general.components[2]["e1e2"]).toBe(4);
    });

    test("creates multivector from array", () => {
      const fromArray = Prime.Clifford.fromArray([4, 5, 6]);
      expect(Prime.Clifford.isMultivector(fromArray)).toBe(true);
      expect(fromArray.components[1]["e1"]).toBe(4);
      expect(fromArray.components[1]["e2"]).toBe(5);
      expect(fromArray.components[1]["e3"]).toBe(6);
    });

    test("preserves irrational values in fromArray", () => {
      const preciseValues = [Math.PI, Math.E, Math.sqrt(2)];
      const preciseArray = Prime.Clifford.fromArray(preciseValues);

      expect(Prime.Clifford.isMultivector(preciseArray)).toBe(true);
      Assertions.assertExtremePrecision(
        preciseArray.components[1]["e1"],
        Math.PI,
      );
      Assertions.assertExtremePrecision(
        preciseArray.components[1]["e2"],
        Math.E,
      );
      Assertions.assertExtremePrecision(
        preciseArray.components[1]["e3"],
        Math.sqrt(2),
      );
    });

    test("safely handles extreme values", () => {
      const safeValues = [
        1000000, // Large but safely representable
        0.0001, // Small but safely representable
        1 + Number.EPSILON, // Just above 1
      ];

      const safeBivector = Cl3.bivector([
        [0, safeValues[0], safeValues[1]],
        [0, 0, safeValues[2]],
        [0, 0, 0],
      ]);

      Assertions.assertExtremePrecision(
        safeBivector.components[2]["e1e2"],
        safeValues[0],
      );
      Assertions.assertExtremePrecision(
        safeBivector.components[2]["e1e3"],
        safeValues[1],
      );
      Assertions.assertExtremePrecision(
        safeBivector.components[2]["e2e3"],
        safeValues[2],
      );
    });

    test("eliminates zero values", () => {
      const zeroHandlingVector = Cl3.vector([0, 1, 0]);
      expect(zeroHandlingVector.components[1].hasOwnProperty("e1")).toBe(false);
      expect(zeroHandlingVector.components[1].hasOwnProperty("e3")).toBe(false);
      expect(zeroHandlingVector.components[1].hasOwnProperty("e2")).toBe(true);
    });
  });

  describe("Type Detection", () => {
    let Cl3, scalar;

    beforeEach(() => {
      Cl3 = Prime.Clifford.create({ dimension: 3 });
      scalar = Cl3.scalar(5);
    });

    test("isMultivector detects multivectors", () => {
      expect(Prime.Clifford.isMultivector(scalar)).toBe(true);
      expect(Prime.Clifford.isMultivector({})).toBe(false);
    });

    test("isAlgebra detects Clifford algebras", () => {
      expect(Prime.Clifford.isAlgebra(Cl3)).toBe(true);
      expect(Prime.Clifford.isAlgebra({})).toBe(false);
    });
  });

  describe("Multivector Operations", () => {
    let Cl3;

    beforeEach(() => {
      Cl3 = Prime.Clifford.create({ dimension: 3 });
    });

    describe("Scalar Operations", () => {
      test("scalar addition works", () => {
        const s1 = Cl3.scalar(5);
        const s2 = Cl3.scalar(3);
        const sum = s1.add(s2);

        expect(sum.components[0]["1"]).toBe(8);
      });

      test("scalar subtraction works", () => {
        const s1 = Cl3.scalar(5);
        const s2 = Cl3.scalar(3);
        const diff = s1.subtract(s2);

        expect(diff.components[0]["1"]).toBe(2);
      });

      test("scalar scaling works", () => {
        const s1 = Cl3.scalar(5);
        const scaled = s1.scale(2);

        expect(scaled.components[0]["1"]).toBe(10);
      });
    });

    describe("Vector Operations", () => {
      test("vector addition works", () => {
        const v1 = Cl3.vector([1, 2, 3]);
        const v2 = Cl3.vector([4, 5, 6]);
        const vSum = v1.add(v2);

        expect(vSum.components[1]["e1"]).toBe(5);
        expect(vSum.components[1]["e2"]).toBe(7);
        expect(vSum.components[1]["e3"]).toBe(9);
      });

      test("vector subtraction works", () => {
        const v1 = Cl3.vector([1, 2, 3]);
        const v2 = Cl3.vector([4, 5, 6]);
        const vDiff = v1.subtract(v2);

        expect(vDiff.components[1]["e1"]).toBe(-3);
        expect(vDiff.components[1]["e2"]).toBe(-3);
        expect(vDiff.components[1]["e3"]).toBe(-3);
      });

      test("vector scaling works", () => {
        const v1 = Cl3.vector([1, 2, 3]);
        const vScaled = v1.scale(2);

        expect(vScaled.components[1]["e1"]).toBe(2);
        expect(vScaled.components[1]["e2"]).toBe(4);
        expect(vScaled.components[1]["e3"]).toBe(6);
      });
    });

    describe("Geometric Product", () => {
      test("geometric product has correct components", () => {
        const v1 = Cl3.vector([1, 2, 3]);
        const v2 = Cl3.vector([4, 5, 6]);
        const gp = v1.multiply(v2);

        // v1·v2 = 1*4 + 2*5 + 3*6 = 4 + 10 + 18 = 32
        expect(gp.components[0]["1"]).toBe(32);

        // v1∧v2 = (1*5 - 2*4)e1∧e2 + (1*6 - 3*4)e1∧e3 + (2*6 - 3*5)e2∧e3
        //       = (5 - 8)e1∧e2 + (6 - 12)e1∧e3 + (12 - 15)e2∧e3
        //       = -3e1∧e2 - 6e1∧e3 - 3e2∧e3
        expect(gp.components[2]["e1e2"]).toBe(-3);
        expect(gp.components[2]["e1e3"]).toBe(-6);
        expect(gp.components[2]["e2e3"]).toBe(-3);
      });
    });

    describe("Inner and Outer Products", () => {
      test("dot product has correct value", () => {
        const v1 = Cl3.vector([1, 2, 3]);
        const v2 = Cl3.vector([4, 5, 6]);
        const dp = v1.dot(v2);

        expect(dp.components[0]["1"]).toBe(32);
      });

      test("wedge product has correct components", () => {
        const v1 = Cl3.vector([1, 2, 3]);
        const v2 = Cl3.vector([4, 5, 6]);
        const wp = v1.wedge(v2);

        expect(wp.components[2]["e1e2"]).toBe(-3);
        expect(wp.components[2]["e1e3"]).toBe(-6);
        expect(wp.components[2]["e2e3"]).toBe(-3);
      });
    });

    describe("Grade Extraction", () => {
      test("grade(0) extracts scalar part", () => {
        const v1 = Cl3.vector([1, 2, 3]);
        const v2 = Cl3.vector([4, 5, 6]);
        const gp = v1.multiply(v2);
        const grade0 = gp.grade(0);

        expect(grade0.components[0]["1"]).toBe(32);
        expect(grade0.components[1]).toBeUndefined();
        expect(grade0.components[2]).toBeUndefined();
      });

      test("grade(1) extracts vector part", () => {
        const v = Cl3.vector([1, 2, 3]);
        const grade1 = v.grade(1);

        expect(grade1.components[0]).toBeUndefined();
        expect(grade1.components[1]["e1"]).toBe(1);
        expect(grade1.components[2]).toBeUndefined();
      });

      test("grade(2) extracts bivector part", () => {
        const v1 = Cl3.vector([1, 2, 3]);
        const v2 = Cl3.vector([4, 5, 6]);
        const gp = v1.multiply(v2);
        const grade2 = gp.grade(2);

        expect(grade2.components[0]).toBeUndefined();
        expect(grade2.components[1]).toBeUndefined();
        expect(grade2.components[2]["e1e2"]).toBe(-3);
      });
    });

    describe("Convenience Grade Extractors", () => {
      test("scalar() extracts scalar part", () => {
        const v1 = Cl3.vector([1, 2, 3]);
        const v2 = Cl3.vector([4, 5, 6]);
        const gp = v1.multiply(v2);
        const scalar = gp.scalar();

        expect(scalar.components[0]["1"]).toBe(32);
      });

      test("vector() extracts vector part", () => {
        const v = Cl3.vector([1, 2, 3]);
        const vector = v.vector();

        expect(vector.components[1]["e1"]).toBe(1);
      });

      test("bivector() extracts bivector part", () => {
        const v1 = Cl3.vector([1, 2, 3]);
        const v2 = Cl3.vector([4, 5, 6]);
        const gp = v1.multiply(v2);
        const bivector = gp.bivector();

        expect(bivector.components[2]["e1e2"]).toBe(-3);
      });
    });

    describe("Reverse and Conjugate", () => {
      test("reverse of vector preserves components", () => {
        const v = Cl3.vector([1, 2, 3]);
        const vRev = v.reverse();

        expect(vRev.components[1]["e1"]).toBe(1);
      });

      test("reverse of bivector flips sign", () => {
        const b = Cl3.bivector([
          [0, 1, 0],
          [0, 0, 0],
          [0, 0, 0],
        ]);
        const bRev = b.reverse();

        expect(bRev.components[2]["e1e2"]).toBe(-1);
      });

      test("conjugate of vector flips sign", () => {
        const v = Cl3.vector([1, 2, 3]);
        const vConj = v.conjugate();

        expect(vConj.components[1]["e1"]).toBe(-1);
      });

      test("conjugate of bivector preserves sign", () => {
        const b = Cl3.bivector([
          [0, 1, 0],
          [0, 0, 0],
          [0, 0, 0],
        ]);
        const bConj = b.conjugate();

        expect(bConj.components[2]["e1e2"]).toBe(1);
      });
    });

    describe("Norm and Utility Methods", () => {
      test("norm of vector calculates Euclidean length", () => {
        const norm = Cl3.vector([3, 4, 0]).norm();
        Assertions.assertAdaptivePrecision(norm, 5, 1e-6);
      });

      test("norm of scalar is its absolute value", () => {
        const norm = Cl3.scalar(5).norm();
        Assertions.assertAdaptivePrecision(norm, 5, 1e-6);
      });

      test("isZero returns correct values", () => {
        expect(Cl3.vector([1, 2, 3]).isZero()).toBe(false);
        expect(Cl3.scalar(0).isZero()).toBe(true);
      });

      test("isScalar returns correct values", () => {
        expect(Cl3.scalar(5).isScalar()).toBe(true);
        expect(Cl3.vector([1, 2, 3]).isScalar()).toBe(false);
      });

      test("scalarValue returns scalar value", () => {
        expect(Cl3.scalar(5).scalarValue()).toBe(5);
      });

      test("scalarValue throws for non-scalar", () => {
        expect(() => Cl3.vector([1, 2, 3]).scalarValue()).toThrow(
          Prime.MathematicalError,
        );
      });
    });

    describe("Clone and Conversion", () => {
      test("clone creates different object with same values", () => {
        const original = Cl3.vector([1, 2, 3]);
        const clone = original.clone();

        expect(original).not.toBe(clone);
        expect(clone.components[1]["e1"]).toBe(1);
      });

      test("toArray returns correct array", () => {
        const v = Cl3.vector([1, 2, 3]);
        const array = v.toArray();

        expect(Array.isArray(array)).toBe(true);
        expect(array.length).toBe(3);
        expect(array[0]).toBe(1);
        expect(array[1]).toBe(2);
        expect(array[2]).toBe(3);
      });

      test("toString returns string representation", () => {
        const str = Cl3.scalar(5)
          .add(Cl3.vector([1, 0, 0]))
          .toString();

        expect(typeof str).toBe("string");
        expect(str.includes("5")).toBe(true);
        expect(str.includes("e1")).toBe(true);
      });
    });
  });
});
