/**
 * PrimeOS Unit Tests - Lie Groups
 *
 * Tests for the Lie Group implementation in the Mathematics module.
 */

const Prime = require("../../../src/mathematics.js");
const { Assertions } = require("../../utils");

describe("Lie Groups", () => {
  describe("SO(3) Creation", () => {
    test("creates SO(3) group with correct properties", () => {
      const so3 = Prime.Lie.SO(3);

      expect(Prime.Lie.isGroup(so3)).toBe(true);
      expect(so3.name).toBe("SO(3)");
      expect(so3.dimension).toBe(3);
      expect(Array.isArray(so3.generators)).toBe(true);
      expect(so3.generators.length).toBe(3);
    });

    test("provides correct generators", () => {
      const so3 = Prime.Lie.SO(3);
      const genX = so3.generator("X");

      expect(Prime.Lie.isAlgebraElement(genX)).toBe(true);
      expect(genX.name).toBe("X");
      expect(Array.isArray(genX.matrix)).toBe(true);
    });
  });

  describe("Rotation Creation", () => {
    test("creates rotation element with correct properties", () => {
      const so3 = Prime.Lie.SO(3);
      const rot = so3.rotation([0, 0, 1], Math.PI / 2);

      expect(Prime.Lie.isGroupElement(rot)).toBe(true);
      expect(rot.group).toBe(so3);
      expect(rot.params.type).toBe("rotation");
      expect(Array.isArray(rot.matrix)).toBe(true);
    });

    test("rotation correctly transforms vectors", () => {
      const so3 = Prime.Lie.SO(3);
      const rot = so3.rotation([0, 0, 1], Math.PI / 2);
      const vec = [1, 0, 0];
      const rotated = rot.apply(vec);

      expect(Array.isArray(rotated)).toBe(true);
      Assertions.assertAdaptivePrecision(rotated[0], 0, 1e-6);
      Assertions.assertAdaptivePrecision(rotated[1], 1, 1e-6);
      Assertions.assertAdaptivePrecision(rotated[2], 0, 1e-6);
    });
  });

  describe("Group Operations", () => {
    test("multiplies group elements correctly", () => {
      const so3 = Prime.Lie.SO(3);
      const rot1 = so3.rotation([0, 0, 1], Math.PI / 4);
      const rot2 = so3.rotation([0, 0, 1], Math.PI / 4);
      const composed = rot1.multiply(rot2);

      expect(Prime.Lie.isGroupElement(composed)).toBe(true);
      expect(composed.group).toBe(so3);

      // Test if composing two PI/4 rotations is equivalent to a PI/2 rotation
      const vec2 = [1, 0, 0];
      const composedRotated = composed.apply(vec2);

      Assertions.assertAdaptivePrecision(composedRotated[0], 0, 1e-6);
      Assertions.assertAdaptivePrecision(composedRotated[1], 1, 1e-6);
      Assertions.assertAdaptivePrecision(composedRotated[2], 0, 1e-6);
    });

    test("inverts group elements correctly", () => {
      const so3 = Prime.Lie.SO(3);
      const rot1 = so3.rotation([0, 0, 1], Math.PI / 4);
      const inv = rot1.invert();

      expect(Prime.Lie.isGroupElement(inv)).toBe(true);

      // Test if multiplying by inverse gives identity
      const prod = rot1.multiply(inv);

      // Identity matrix should have 1s on diagonal and 0s elsewhere
      Assertions.assertAdaptivePrecision(prod.matrix[0][0], 1, 1e-6);
      Assertions.assertAdaptivePrecision(prod.matrix[1][1], 1, 1e-6);
      Assertions.assertAdaptivePrecision(prod.matrix[2][2], 1, 1e-6);
      Assertions.assertAdaptivePrecision(prod.matrix[0][1], 0, 1e-6);
    });
  });

  describe("Multivector Transformations", () => {
    test("rotation transforms multivectors correctly", () => {
      const so3 = Prime.Lie.SO(3);
      const rot = so3.rotation([0, 0, 1], Math.PI / 2);
      const Cl3 = Prime.Clifford.create({ dimension: 3 });
      const mv = Cl3.vector([1, 0, 0]);

      const rotatedMv = rot.apply(mv);
      expect(Prime.Clifford.isMultivector(rotatedMv)).toBe(true);

      // Extract the vector components to check the rotation
      const mvArray = rotatedMv.toArray();
      Assertions.assertAdaptivePrecision(mvArray[0], 0, 1e-6);
      Assertions.assertAdaptivePrecision(mvArray[1], 1, 1e-6);
      Assertions.assertAdaptivePrecision(mvArray[2], 0, 1e-6);
    });
  });

  describe("Lie Algebra Operations", () => {
    test("scales algebra elements correctly", () => {
      const so3 = Prime.Lie.SO(3);
      const genX = so3.generator("X");
      const scaledGen = genX.scale(2);

      expect(Prime.Lie.isAlgebraElement(scaledGen)).toBe(true);
      expect(scaledGen.matrix[1][2]).toBe(-2);
    });

    test("adds algebra elements correctly", () => {
      const so3 = Prime.Lie.SO(3);
      const genX = so3.generator("X");
      const genY = so3.generator("Y");
      const sum = genX.add(genY);

      expect(Prime.Lie.isAlgebraElement(sum)).toBe(true);
      expect(sum.matrix[1][2]).toBe(-1);
      expect(sum.matrix[0][2]).toBe(1);
    });

    test("computes Lie bracket correctly", () => {
      const so3 = Prime.Lie.SO(3);
      const genX = so3.generator("X");
      const genY = so3.generator("Y");
      const bracket = genX.bracket(genY);

      expect(Prime.Lie.isAlgebraElement(bracket)).toBe(true);
      // [X,Y] = Z in so(3)
      expect(bracket.matrix[0][1]).not.toBe(0);
    });
  });
});

describe("SO(3) Rotations", () => {
  let so3;

  beforeEach(() => {
    so3 = Prime.Lie.SO(3);
  });

  describe("Axis Rotations", () => {
    test("rotates around X axis correctly", () => {
      const rotX = so3.rotation([1, 0, 0], Math.PI / 2);
      const vecY = [0, 1, 0];
      const rotatedY = rotX.apply(vecY);

      Assertions.assertAdaptivePrecision(rotatedY[0], 0, 1e-6);
      Assertions.assertAdaptivePrecision(rotatedY[1], 0, 1e-6);
      Assertions.assertAdaptivePrecision(rotatedY[2], 1, 1e-6);
    });

    test("rotates around Y axis correctly", () => {
      const rotY = so3.rotation([0, 1, 0], Math.PI / 2);
      const vecZ = [0, 0, 1];
      const rotatedZ = rotY.apply(vecZ);

      Assertions.assertAdaptivePrecision(rotatedZ[0], 1, 1e-6);
      Assertions.assertAdaptivePrecision(rotatedZ[1], 0, 1e-6);
      Assertions.assertAdaptivePrecision(rotatedZ[2], 0, 1e-6);
    });

    test("rotates around Z axis correctly", () => {
      const rotZ = so3.rotation([0, 0, 1], Math.PI / 2);
      const vecX = [1, 0, 0];
      const rotatedX = rotZ.apply(vecX);

      Assertions.assertAdaptivePrecision(rotatedX[0], 0, 1e-6);
      Assertions.assertAdaptivePrecision(rotatedX[1], 1, 1e-6);
      Assertions.assertAdaptivePrecision(rotatedX[2], 0, 1e-6);
    });
  });

  describe("Arbitrary Axis Rotations", () => {
    test("rotates around arbitrary axis correctly", () => {
      const axis = [1, 1, 1]; // Not normalized
      const rot = so3.rotation(axis, Math.PI);
      const v = [1, 0, 0];
      const rotated = rot.apply(v);

      // Verify that the rotation preserves the length
      const originalLength = Math.sqrt(v[0] * v[0] + v[1] * v[1] + v[2] * v[2]);
      const rotatedLength = Math.sqrt(
        rotated[0] * rotated[0] +
          rotated[1] * rotated[1] +
          rotated[2] * rotated[2],
      );

      Assertions.assertAdaptivePrecision(rotatedLength, originalLength, 1e-6);

      // Verify that applying the rotation twice returns to the original
      const rotatedTwice = rot.apply(rot.apply(v));

      Assertions.assertAdaptivePrecision(rotatedTwice[0], v[0], 1e-6);
      Assertions.assertAdaptivePrecision(rotatedTwice[1], v[1], 1e-6);
      Assertions.assertAdaptivePrecision(rotatedTwice[2], v[2], 1e-6);
    });

    test("rotation by 360° is identity", () => {
      const full = so3.rotation([0, 1, 0], 2 * Math.PI);
      const v2 = [1, 2, 3];
      const rotated2 = full.apply(v2);

      Assertions.assertAdaptivePrecision(rotated2[0], 1, 1e-6);
      Assertions.assertAdaptivePrecision(rotated2[1], 2, 1e-6);
      Assertions.assertAdaptivePrecision(rotated2[2], 3, 1e-6);
    });
  });

  describe("Rotation Composition", () => {
    test("composes rotations correctly", () => {
      const rotX = so3.rotation([1, 0, 0], Math.PI / 2);
      const rotY = so3.rotation([0, 1, 0], Math.PI / 2);
      const composed = rotX.multiply(rotY); // Apply rotY then rotX
      const v3 = [1, 0, 0];
      const result = composed.apply(v3);

      // rotY maps [1,0,0] to [0,0,-1], then rotX maps [0,0,-1] to [0,1,0]
      Assertions.assertAdaptivePrecision(result[0], 0, 1e-6);
      Assertions.assertAdaptivePrecision(result[1], 1, 1e-6);
      Assertions.assertAdaptivePrecision(result[2], 0, 1e-6);
    });
  });
});
