/**
 * Tests for the Type Validation module
 */

// Import the type validation module
const TypeValidation = require("../../../src/framework/math/type-validation.js");

// Import Prime core to access the error classes
const Prime = require("../../../src/core/prime.js");

describe("TypeValidation", () => {
  describe("assertArray", () => {
    it("should not throw for valid arrays", () => {
      expect(() => TypeValidation.assertArray([], "emptyArray")).not.toThrow();
      expect(() =>
        TypeValidation.assertArray([1, 2, 3], "numberArray"),
      ).not.toThrow();
      expect(() =>
        TypeValidation.assertArray(["a", "b"], "stringArray"),
      ).not.toThrow();
    });

    it("should throw ValidationError for non-arrays", () => {
      expect(() =>
        TypeValidation.assertArray("not an array", "stringParam"),
      ).toThrow(Prime.ValidationError);
      expect(() => TypeValidation.assertArray(42, "numberParam")).toThrow(
        Prime.ValidationError,
      );
      expect(() => TypeValidation.assertArray({}, "objectParam")).toThrow(
        Prime.ValidationError,
      );
    });
  });

  describe("assertNumber", () => {
    it("should not throw for valid numbers", () => {
      expect(() => TypeValidation.assertNumber(0, "zero")).not.toThrow();
      expect(() => TypeValidation.assertNumber(42, "positive")).not.toThrow();
      expect(() =>
        TypeValidation.assertNumber(-3.14, "negative"),
      ).not.toThrow();
    });

    it("should throw ValidationError for non-numbers", () => {
      expect(() => TypeValidation.assertNumber("42", "stringNumber")).toThrow(
        Prime.ValidationError,
      );
      expect(() => TypeValidation.assertNumber([], "arrayParam")).toThrow(
        Prime.ValidationError,
      );
      expect(() =>
        TypeValidation.assertNumber(undefined, "undefinedParam"),
      ).toThrow(Prime.ValidationError);
    });
  });

  describe("assertPositiveNumber", () => {
    it("should not throw for positive numbers", () => {
      expect(() => TypeValidation.assertPositiveNumber(1, "one")).not.toThrow();
      expect(() =>
        TypeValidation.assertPositiveNumber(3.14, "pi"),
      ).not.toThrow();
      expect(() =>
        TypeValidation.assertPositiveNumber(1e10, "large"),
      ).not.toThrow();
    });

    it("should throw ValidationError for zero or negative numbers", () => {
      expect(() => TypeValidation.assertPositiveNumber(0, "zero")).toThrow(
        Prime.ValidationError,
      );
      expect(() => TypeValidation.assertPositiveNumber(-1, "negative")).toThrow(
        Prime.ValidationError,
      );
      expect(() =>
        TypeValidation.assertPositiveNumber(-3.14, "negativePi"),
      ).toThrow(Prime.ValidationError);
    });
  });

  describe("assertInteger", () => {
    it("should not throw for valid integers", () => {
      expect(() => TypeValidation.assertInteger(0, "zero")).not.toThrow();
      expect(() => TypeValidation.assertInteger(42, "positive")).not.toThrow();
      expect(() => TypeValidation.assertInteger(-99, "negative")).not.toThrow();
    });

    it("should throw ValidationError for non-integers", () => {
      expect(() => TypeValidation.assertInteger(3.14, "pi")).toThrow(
        Prime.ValidationError,
      );
      expect(() => TypeValidation.assertInteger("42", "stringNumber")).toThrow(
        Prime.ValidationError,
      );
      expect(() => TypeValidation.assertInteger(NaN, "notANumber")).toThrow(
        Prime.ValidationError,
      );
    });
  });

  describe("assertFinite", () => {
    it("should not throw for finite numbers", () => {
      expect(() => TypeValidation.assertFinite(0, "zero")).not.toThrow();
      expect(() => TypeValidation.assertFinite(42, "positive")).not.toThrow();
      expect(() =>
        TypeValidation.assertFinite(-99.99, "negative"),
      ).not.toThrow();
    });

    it("should throw ValidationError for non-finite numbers", () => {
      expect(() => TypeValidation.assertFinite(Infinity, "infinity")).toThrow(
        Prime.ValidationError,
      );
      expect(() =>
        TypeValidation.assertFinite(-Infinity, "negativeInfinity"),
      ).toThrow(Prime.ValidationError);
      expect(() => TypeValidation.assertFinite(NaN, "notANumber")).toThrow(
        Prime.ValidationError,
      );
    });
  });

  describe("assertFunction", () => {
    it("should not throw for valid functions", () => {
      expect(() =>
        TypeValidation.assertFunction(() => {}, "arrow"),
      ).not.toThrow();
      expect(() =>
        TypeValidation.assertFunction(function () {}, "anonymous"),
      ).not.toThrow();
    });

    it("should throw ValidationError for non-functions", () => {
      expect(() => TypeValidation.assertFunction("function", "string")).toThrow(
        Prime.ValidationError,
      );
      expect(() => TypeValidation.assertFunction(null, "null")).toThrow(
        Prime.ValidationError,
      );
      expect(() => TypeValidation.assertFunction({}, "object")).toThrow(
        Prime.ValidationError,
      );
    });
  });

  describe("assertObject", () => {
    it("should not throw for valid objects", () => {
      expect(() => TypeValidation.assertObject({}, "empty")).not.toThrow();
      expect(() =>
        TypeValidation.assertObject({ key: "value" }, "filled"),
      ).not.toThrow();
      expect(() =>
        TypeValidation.assertObject(new Date(), "date"),
      ).not.toThrow();
    });

    it("should throw ValidationError for non-objects or arrays", () => {
      expect(() => TypeValidation.assertObject([], "array")).toThrow(
        Prime.ValidationError,
      );
      expect(() => TypeValidation.assertObject("object", "string")).toThrow(
        Prime.ValidationError,
      );
      expect(() => TypeValidation.assertObject(42, "number")).toThrow(
        Prime.ValidationError,
      );
    });
  });

  describe("assertDefined", () => {
    it("should not throw for defined values", () => {
      expect(() => TypeValidation.assertDefined(0, "zero")).not.toThrow();
      expect(() =>
        TypeValidation.assertDefined("", "emptyString"),
      ).not.toThrow();
      expect(() =>
        TypeValidation.assertDefined(false, "boolean"),
      ).not.toThrow();
    });

    it("should throw ValidationError for null or undefined", () => {
      expect(() => TypeValidation.assertDefined(null, "null")).toThrow(
        Prime.ValidationError,
      );
      expect(() =>
        TypeValidation.assertDefined(undefined, "undefined"),
      ).toThrow(Prime.ValidationError);
    });
  });

  describe("assertNumberArray", () => {
    it("should not throw for valid number arrays", () => {
      expect(() => TypeValidation.assertNumberArray([], "empty")).not.toThrow();
      expect(() =>
        TypeValidation.assertNumberArray([1, 2, 3], "integers"),
      ).not.toThrow();
      expect(() =>
        TypeValidation.assertNumberArray([3.14, -2.5], "floats"),
      ).not.toThrow();
    });

    it("should throw ValidationError for arrays with non-numbers", () => {
      expect(() =>
        TypeValidation.assertNumberArray([1, "2", 3], "mixedArray"),
      ).toThrow(Prime.ValidationError);
      expect(() =>
        TypeValidation.assertNumberArray(["a", "b"], "stringArray"),
      ).toThrow(Prime.ValidationError);
    });
  });

  describe("assertMatrix", () => {
    it("should not throw for valid matrices", () => {
      expect(() => TypeValidation.assertMatrix([], "empty")).not.toThrow();
      expect(() =>
        TypeValidation.assertMatrix(
          [
            [1, 2],
            [3, 4],
          ],
          "twoByTwo",
        ),
      ).not.toThrow();
      expect(() =>
        TypeValidation.assertMatrix([[1], [2], [3]], "threeByOne"),
      ).not.toThrow();
    });

    it("should throw ValidationError for non-matrices", () => {
      expect(() => TypeValidation.assertMatrix([1, 2, 3], "vector")).toThrow(
        Prime.ValidationError,
      );
      expect(() =>
        TypeValidation.assertMatrix([[1, 2], [3]], "irregular"),
      ).toThrow(Prime.ValidationError);
      expect(() =>
        TypeValidation.assertMatrix(
          [
            [1, 2],
            ["a", 4],
          ],
          "mixedTypes",
        ),
      ).toThrow(Prime.ValidationError);
    });
  });

  describe("assertSquareMatrix", () => {
    it("should not throw for valid square matrices", () => {
      expect(() =>
        TypeValidation.assertSquareMatrix([], "empty"),
      ).not.toThrow();
      expect(() =>
        TypeValidation.assertSquareMatrix([[1]], "oneByOne"),
      ).not.toThrow();
      expect(() =>
        TypeValidation.assertSquareMatrix(
          [
            [1, 2],
            [3, 4],
          ],
          "twoByTwo",
        ),
      ).not.toThrow();
    });

    it("should throw ValidationError for non-square matrices", () => {
      expect(() =>
        TypeValidation.assertSquareMatrix(
          [
            [1, 2, 3],
            [4, 5, 6],
          ],
          "twoByThree",
        ),
      ).toThrow(Prime.ValidationError);
      expect(() =>
        TypeValidation.assertSquareMatrix([[1], [2], [3]], "threeByOne"),
      ).toThrow(Prime.ValidationError);
    });
  });

  describe("assertSameDimension", () => {
    it("should not throw for vectors with same dimension", () => {
      expect(() =>
        TypeValidation.assertSameDimension([], [], "empty1", "empty2"),
      ).not.toThrow();
      expect(() =>
        TypeValidation.assertSameDimension([1, 2], [3, 4], "v1", "v2"),
      ).not.toThrow();
      expect(() =>
        TypeValidation.assertSameDimension([1, 2, 3], [4, 5, 6], "v1", "v2"),
      ).not.toThrow();
    });

    it("should throw DimensionMismatchError for vectors with different dimensions", () => {
      expect(() =>
        TypeValidation.assertSameDimension([1, 2], [3, 4, 5], "v1", "v2"),
      ).toThrow(Prime.DimensionMismatchError);
      expect(() =>
        TypeValidation.assertSameDimension([1], [2, 3], "v1", "v2"),
      ).toThrow(Prime.DimensionMismatchError);
    });
  });

  describe("assertMultiplicableMatrices", () => {
    it("should not throw for multiplicable matrices", () => {
      expect(() =>
        TypeValidation.assertMultiplicableMatrices(
          [
            [1, 2, 3],
            [4, 5, 6],
          ],
          [
            [1, 2],
            [3, 4],
            [5, 6],
          ],
          "m1",
          "m2",
        ),
      ).not.toThrow();
      expect(() =>
        TypeValidation.assertMultiplicableMatrices(
          [[1, 2]],
          [[3], [4]],
          "m1",
          "m2",
        ),
      ).not.toThrow();
    });

    it("should throw DimensionMismatchError for incompatible matrices", () => {
      expect(() =>
        TypeValidation.assertMultiplicableMatrices(
          [
            [1, 2],
            [3, 4],
          ],
          [
            [1, 2, 3],
            [4, 5, 6],
            [7, 8, 9],
          ],
          "m1",
          "m2",
        ),
      ).toThrow(Prime.DimensionMismatchError);
      expect(() =>
        TypeValidation.assertMultiplicableMatrices(
          [[1, 2, 3]],
          [[4, 5]],
          "m1",
          "m2",
        ),
      ).toThrow(Prime.DimensionMismatchError);
    });
  });

  describe("validateMagnitude", () => {
    it("should not throw for values within allowed magnitude", () => {
      expect(() =>
        TypeValidation.validateMagnitude(42, "normal"),
      ).not.toThrow();
      expect(() =>
        TypeValidation.validateMagnitude(1e-50, "small"),
      ).not.toThrow();
      expect(() =>
        TypeValidation.validateMagnitude(1e50, "large"),
      ).not.toThrow();
      expect(() => TypeValidation.validateMagnitude(0, "zero")).not.toThrow();
      expect(() =>
        TypeValidation.validateMagnitude(0, "zero", { allowZero: true }),
      ).not.toThrow();
    });

    it("should throw NumericOverflowError for values outside allowed magnitude", () => {
      expect(() =>
        TypeValidation.validateMagnitude(1e-150, "tooSmall"),
      ).toThrow(Prime.NumericOverflowError);
      expect(() => TypeValidation.validateMagnitude(1e150, "tooLarge")).toThrow(
        Prime.NumericOverflowError,
      );
      expect(() =>
        TypeValidation.validateMagnitude(0, "zero", { allowZero: false }),
      ).toThrow(Prime.NumericOverflowError);
    });

    it("should respect custom magnitude limits", () => {
      expect(() =>
        TypeValidation.validateMagnitude(0.001, "custom", {
          minMagnitude: 0.01,
        }),
      ).toThrow(Prime.NumericOverflowError);
      expect(() =>
        TypeValidation.validateMagnitude(1000, "custom", { maxMagnitude: 100 }),
      ).toThrow(Prime.NumericOverflowError);
      expect(() =>
        TypeValidation.validateMagnitude(0.1, "custom", { minMagnitude: 0.01 }),
      ).not.toThrow();
    });
  });

  describe("createValidationContext", () => {
    it("should create a context object with operation and inputs", () => {
      const context = TypeValidation.createValidationContext("matrixMultiply", {
        m1: [
          [1, 2],
          [3, 4],
        ],
        m2: [
          [5, 6],
          [7, 8],
        ],
        transpose: true,
      });

      expect(context.operation).toBe("matrixMultiply");
      expect(context.inputs.m1).toBe("matrix(2x2)");
      expect(context.inputs.m2).toBe("matrix(2x2)");
      expect(context.inputs.transpose).toBe("boolean(true)");
    });

    it("should handle various input types correctly", () => {
      const context = TypeValidation.createValidationContext(
        "complexOperation",
        {
          number: 42,
          vector: [1, 2, 3],
          string: "hello",
          func: () => {},
          obj: { a: 1 },
        },
      );

      expect(context.inputs.number).toBe("number(42)");
      expect(context.inputs.vector).toBe("vector(3)");
      expect(context.inputs.string).toBe('string("hello")');
      expect(context.inputs.func).toBe("function");
      expect(context.inputs.obj).toBe("object");
    });

    it("should include additional details", () => {
      const context = TypeValidation.createValidationContext(
        "operation",
        { a: 1, b: 2 },
        { extraInfo: "additional", timestamp: Date.now() },
      );

      expect(context.operation).toBe("operation");
      expect(context.extraInfo).toBe("additional");
      expect(context.timestamp).toBeDefined();
    });
  });
});
