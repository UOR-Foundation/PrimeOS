/**
 * PrimeOS Matrix Refactoring Tests
 * Tests to verify matrix module refactoring maintains functionality
 */

const Prime = require("../src/core");
require("../src/math/matrix"); // This loads all the matrix modules

// Test suite for Matrix refactoring
describe("Matrix Refactoring", () => {
  // Set up shared test matrices
  let m1, m2, m3, m4;

  beforeEach(() => {
    // Initialize test matrices
    m1 = Prime.Math.Matrix.create(2, 2, 0);
    m1[0][0] = 1;
    m1[0][1] = 2;
    m1[1][0] = 3;
    m1[1][1] = 4;

    m2 = Prime.Math.Matrix.create(2, 2, 0);
    m2[0][0] = 5;
    m2[0][1] = 6;
    m2[1][0] = 7;
    m2[1][1] = 8;

    m3 = Prime.Math.Matrix.create(2, 2, 0);

    m4 = Prime.Math.Matrix.identity(2);
  });

  // Core matrix operations tests
  describe("Core Operations", () => {
    test("should create matrices of specified dimensions", () => {
      const matrix = Prime.Math.Matrix.create(3, 4, 0);
      expect(matrix.length).toBe(3);
      expect(matrix[0].length).toBe(4);
    });

    test("should create matrices with TypedArray support", () => {
      const matrix = Prime.Math.Matrix.create(3, 4, 0, {
        useTypedArray: true,
        arrayType: "float64",
      });
      expect(matrix._isTypedMatrix).toBe(true);
      expect(matrix._rows).toBe(3);
      expect(matrix._cols).toBe(4);
    });

    test("should create identity matrices", () => {
      const identity = Prime.Math.Matrix.identity(3);
      expect(identity[0][0]).toBe(1);
      expect(identity[1][1]).toBe(1);
      expect(identity[2][2]).toBe(1);
      expect(identity[0][1]).toBe(0);
      expect(identity[1][0]).toBe(0);
    });

    test("should add matrices correctly", () => {
      const a = Prime.Math.Matrix.create(2, 2, 1);
      const b = Prime.Math.Matrix.create(2, 2, 2);
      const result = Prime.Math.Matrix.add(a, b);

      expect(result[0][0]).toBe(3);
      expect(result[0][1]).toBe(3);
      expect(result[1][0]).toBe(3);
      expect(result[1][1]).toBe(3);
    });

    test("should subtract matrices correctly", () => {
      const a = Prime.Math.Matrix.create(2, 2, 5);
      const b = Prime.Math.Matrix.create(2, 2, 2);
      const result = Prime.Math.Matrix.subtract(a, b);

      expect(result[0][0]).toBe(3);
      expect(result[0][1]).toBe(3);
      expect(result[1][0]).toBe(3);
      expect(result[1][1]).toBe(3);
    });

    test("should multiply matrices correctly", () => {
      const a = [
        [1, 2],
        [3, 4],
      ];
      const b = [
        [5, 6],
        [7, 8],
      ];
      const result = Prime.Math.Matrix.multiply(a, b);

      expect(result[0][0]).toBe(19);
      expect(result[0][1]).toBe(22);
      expect(result[1][0]).toBe(43);
      expect(result[1][1]).toBe(50);
    });

    test("should scale matrices correctly", () => {
      const a = Prime.Math.Matrix.create(2, 2, 3);
      const result = Prime.Math.Matrix.scale(a, 2);

      expect(result[0][0]).toBe(6);
      expect(result[0][1]).toBe(6);
      expect(result[1][0]).toBe(6);
      expect(result[1][1]).toBe(6);
    });

    test("should transpose matrices correctly", () => {
      const a = [
        [1, 2, 3],
        [4, 5, 6],
      ];
      const result = Prime.Math.Matrix.transpose(a);

      expect(result.length).toBe(3);
      expect(result[0].length).toBe(2);
      expect(result[0][0]).toBe(1);
      expect(result[0][1]).toBe(4);
      expect(result[1][0]).toBe(2);
      expect(result[1][1]).toBe(5);
      expect(result[2][0]).toBe(3);
      expect(result[2][1]).toBe(6);
    });

    test("should support in-place operations", () => {
      const a = Prime.Math.Matrix.create(2, 2, 1);
      const b = Prime.Math.Matrix.create(2, 2, 2);
      const result = Prime.Math.Matrix.create(2, 2, 0);

      // Perform in-place addition
      Prime.Math.Matrix.add(a, b, result);

      expect(result[0][0]).toBe(3);
      expect(result[0][1]).toBe(3);
      expect(result[1][0]).toBe(3);
      expect(result[1][1]).toBe(3);
    });
  });

  // Advanced matrix operations tests
  describe("Advanced Operations", () => {
    test("should calculate determinant correctly", () => {
      const a = [
        [1, 2],
        [3, 4],
      ];
      const det = Prime.Math.Matrix.determinant(a);
      expect(det).toBe(-2);

      const b = [
        [1, 2, 3],
        [4, 5, 6],
        [7, 8, 9],
      ];
      const detB = Prime.Math.Matrix.determinant(b);
      expect(detB).toBe(0);
    });

    test("should calculate inverse correctly", () => {
      const a = [
        [4, 7],
        [2, 6],
      ];
      const inv = Prime.Math.Matrix.inverse(a);

      // Check that A * A^-1 = I
      const product = Prime.Math.Matrix.multiply(a, inv);

      // Allow for floating point imprecision
      expect(Math.abs(product[0][0] - 1)).toBeLessThan(1e-10);
      expect(Math.abs(product[0][1])).toBeLessThan(1e-10);
      expect(Math.abs(product[1][0])).toBeLessThan(1e-10);
      expect(Math.abs(product[1][1] - 1)).toBeLessThan(1e-10);
    });

    test("should calculate LU decomposition correctly", () => {
      const a = [
        [4, 3],
        [6, 3],
      ];

      const { L, U, P } = Prime.Math.Matrix.luDecomposition(a);

      // Check that P * A = L * U where P is the permutation matrix

      // First create the permutation matrix from P
      const permMatrix = [
        [0, 0],
        [0, 0],
      ];

      // Convert P array to permutation matrix
      for (let i = 0; i < 2; i++) {
        permMatrix[i][P[i]] = 1;
      }

      // Multiply P * A to get the permuted matrix
      const permutedA = Prime.Math.Matrix.multiply(permMatrix, a);

      // Now check L*U against permuted matrix
      const product = Prime.Math.Matrix.multiply(L, U);

      // Allow for floating point imprecision
      for (let i = 0; i < 2; i++) {
        for (let j = 0; j < 2; j++) {
          expect(Math.abs(product[i][j] - permutedA[i][j])).toBeLessThan(1e-10);
        }
      }
    });

    test("should solve linear system correctly", () => {
      // System: 3x + 2y = 8, x + y = 3
      const A = [
        [3, 2],
        [1, 1],
      ];
      const b = [8, 3];

      const solution = Prime.Math.Matrix.solve(A, b);

      // Solution should be x=2, y=1
      expect(Math.abs(solution[0] - 2)).toBeLessThan(1e-10);
      expect(Math.abs(solution[1] - 1)).toBeLessThan(1e-10);
    });
  });

  // Validation operations tests
  describe("Validation Operations", () => {
    test("should identify matrices correctly", () => {
      const validMatrix = Prime.Math.Matrix.create(2, 2, 0);
      const invalidMatrix = [1, 2, 3];

      expect(Prime.Math.Matrix.isMatrix(validMatrix)).toBe(true);
      expect(Prime.Math.Matrix.isMatrix(invalidMatrix)).toBe(false);
    });

    test("should identify square matrices correctly", () => {
      const squareMatrix = Prime.Math.Matrix.create(3, 3, 0);
      const nonSquareMatrix = Prime.Math.Matrix.create(2, 3, 0);

      expect(Prime.Math.Matrix.isSquare(squareMatrix)).toBe(true);
      expect(Prime.Math.Matrix.isSquare(nonSquareMatrix)).toBe(false);
    });

    test("should identify symmetric matrices correctly", () => {
      const symmetricMatrix = [
        [1, 2, 3],
        [2, 4, 5],
        [3, 5, 6],
      ];

      const nonSymmetricMatrix = [
        [1, 2, 3],
        [4, 5, 6],
        [7, 8, 9],
      ];

      expect(Prime.Math.Matrix.isSymmetric(symmetricMatrix)).toBe(true);
      expect(Prime.Math.Matrix.isSymmetric(nonSymmetricMatrix)).toBe(false);
    });

    test("should identify invertible matrices correctly", () => {
      const invertibleMatrix = [
        [1, 2],
        [3, 7],
      ];

      const singularMatrix = [
        [1, 2],
        [2, 4],
      ];

      expect(Prime.Math.Matrix.isInvertible(invertibleMatrix)).toBe(true);
      expect(Prime.Math.Matrix.isInvertible(singularMatrix)).toBe(false);
    });
  });

  // Memory optimization tests
  describe("Memory Optimizations", () => {
    test("should create TypedArray matrices that work with operations", () => {
      const a = Prime.Math.Matrix.create(2, 2, 1, { useTypedArray: true });
      const b = Prime.Math.Matrix.create(2, 2, 2, { useTypedArray: true });

      // Operations should work with TypedArray matrices
      const sum = Prime.Math.Matrix.add(a, b);
      expect(sum[0][0]).toBe(3);

      const product = Prime.Math.Matrix.multiply(a, b);
      expect(product[0][0]).toBe(4);

      const scaled = Prime.Math.Matrix.scale(a, 3);
      expect(scaled[0][0]).toBe(3);
    });

    test("should support in-place operations for TypedArray matrices", () => {
      const a = Prime.Math.Matrix.create(2, 2, 1, { useTypedArray: true });
      const b = Prime.Math.Matrix.create(2, 2, 2, { useTypedArray: true });
      const result = Prime.Math.Matrix.create(2, 2, 0, { useTypedArray: true });

      // Perform in-place addition
      Prime.Math.Matrix.add(a, b, result);
      expect(result[0][0]).toBe(3);

      // Perform in-place scaling
      Prime.Math.Matrix.scale(a, 5, result);
      expect(result[0][0]).toBe(5);
    });
  });

  // Regression tests
  describe("Regression Tests", () => {
    test("should preserve the API of the original matrix module", () => {
      // Verify all key methods from original matrix.js are present
      expect(typeof Prime.Math.Matrix.create).toBe("function");
      expect(typeof Prime.Math.Matrix.identity).toBe("function");
      expect(typeof Prime.Math.Matrix.add).toBe("function");
      expect(typeof Prime.Math.Matrix.subtract).toBe("function");
      expect(typeof Prime.Math.Matrix.multiply).toBe("function");
      expect(typeof Prime.Math.Matrix.scale).toBe("function");
      expect(typeof Prime.Math.Matrix.transpose).toBe("function");
      expect(typeof Prime.Math.Matrix.determinant).toBe("function");
      expect(typeof Prime.Math.Matrix.inverse).toBe("function");
      expect(typeof Prime.Math.Matrix.solve).toBe("function");
    });
  });

  // Extreme values tests
  describe("Extreme Values Handling", () => {
    test("should correctly validate symmetric matrices with extreme values", () => {
      // Create a symmetric matrix with extreme values
      const extremeSymmetric = [
        [1e-15, 1e15, 1e-10],
        [1e15, 2, 1e20],
        [1e-10, 1e20, 3],
      ];

      expect(Prime.Math.Matrix.isSymmetric(extremeSymmetric)).toBe(true);

      // Non-symmetric matrix with extreme values
      const nonSymmetric = [
        [1e-15, 1e15, 1e-10],
        [1e15, 2, 1e20],
        [1e-10, 1e20 + 1e5, 3], // Small difference in extreme value
      ];

      expect(Prime.Math.Matrix.isSymmetric(nonSymmetric)).toBe(false);
    });

    test("should correctly identify orthogonal matrices with extreme values", () => {
      // Create a rotation matrix (orthogonal) and scale some rows to extreme values
      const angle = Math.PI / 4; // 45 degrees
      const c = Math.cos(angle);
      const s = Math.sin(angle);

      const rotationMatrix = [
        [c, -s, 0],
        [s, c, 0],
        [0, 0, 1],
      ];

      expect(Prime.Math.Matrix.isOrthogonal(rotationMatrix)).toBe(true);

      // Scale a row to extreme values (this breaks orthogonality)
      const extremeRotation = [
        [c * 1e-10, -s * 1e-10, 0],
        [s, c, 0],
        [0, 0, 1],
      ];

      // This is not orthogonal because rows must have the same scale
      expect(Prime.Math.Matrix.isOrthogonal(extremeRotation)).toBe(false);

      // Special case of orthogonal matrix with uniform scaling factors
      const fullyScaledOrthogonal = [
        [c * 1e-5, -s * 1e-5, 0],
        [s * 1e-5, c * 1e-5, 0],
        [0, 0, 1e-5],
      ];

      // This isn't truly orthogonal, but it's orthogonal up to a scaling factor
      // Our implementation requires actual orthogonality (QᵀQ = I)
      expect(Prime.Math.Matrix.isOrthogonal(fullyScaledOrthogonal)).toBe(false);

      // Rescale to create a truly orthogonal matrix with mixed extreme values
      // This is a proper orthogonal matrix with unit columns
      const smallRotation = [
        [c, -s, 0],
        [s, c, 0],
        [0, 0, 1],
      ];

      expect(Prime.Math.Matrix.isOrthogonal(smallRotation)).toBe(true);
    });

    test("should handle matrix operations with extreme values", () => {
      // Create matrices with extreme values
      const a = Prime.Math.Matrix.create(2, 2, 1e15);
      const b = Prime.Math.Matrix.create(2, 2, 1e-15);

      // Addition should work with extreme values
      const sum = Prime.Math.Matrix.add(a, b);
      expect(sum[0][0]).toBeCloseTo(1e15, 5);

      // Subtraction should work with extreme values
      const diff = Prime.Math.Matrix.subtract(a, b);
      expect(diff[0][0]).toBeCloseTo(1e15, 5);

      // Multiplication should work with extreme values
      const product = Prime.Math.Matrix.multiply(a, b);
      expect(product[0][0]).toBeCloseTo(2e15 * 1e-15, 5);

      // Matrix inverse with extreme values
      const c = [
        [1e10, 0],
        [0, 1e-10],
      ];

      const cInverse = Prime.Math.Matrix.inverse(c);
      expect(cInverse[0][0]).toBeCloseTo(1e-10, 5);
      expect(cInverse[1][1]).toBeCloseTo(1e10, 5);
    });
  });
});
