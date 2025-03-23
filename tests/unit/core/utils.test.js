/**
 * PrimeOS Unit Tests - Core Utilities
 *
 * Tests for the utility functions in the core module.
 */

const Prime = require("../../../src/core.js");
const { Assertions, Mocking } = require("../../utils");

describe("Core Utilities", () => {
  describe("Type Checking", () => {
    test("isObject returns true for plain objects", () => {
      expect(Prime.Utils.isObject({})).toBe(true);
      expect(Prime.Utils.isObject({ a: 1 })).toBe(true);
    });

    test("isObject returns false for non-objects", () => {
      expect(Prime.Utils.isObject(null)).toBe(false);
      expect(Prime.Utils.isObject([])).toBe(false);
      expect(Prime.Utils.isObject("string")).toBe(false);
      expect(Prime.Utils.isObject(123)).toBe(false);
      expect(Prime.Utils.isObject(true)).toBe(false);
      expect(Prime.Utils.isObject(undefined)).toBe(false);
      expect(Prime.Utils.isObject(function () {})).toBe(false);
    });

    test("isFunction returns true for functions", () => {
      expect(Prime.Utils.isFunction(function () {})).toBe(true);
      expect(Prime.Utils.isFunction(() => {})).toBe(true);
    });

    test("isFunction returns false for non-functions", () => {
      expect(Prime.Utils.isFunction({})).toBe(false);
      expect(Prime.Utils.isFunction([])).toBe(false);
      expect(Prime.Utils.isFunction("string")).toBe(false);
      expect(Prime.Utils.isFunction(123)).toBe(false);
    });

    test("isArray returns true for arrays", () => {
      expect(Prime.Utils.isArray([])).toBe(true);
      expect(Prime.Utils.isArray([1, 2, 3])).toBe(true);
    });

    test("isArray returns false for non-arrays", () => {
      expect(Prime.Utils.isArray({})).toBe(false);
      expect(Prime.Utils.isArray("string")).toBe(false);
      expect(Prime.Utils.isArray(123)).toBe(false);
    });

    test("isNumber returns true for numbers", () => {
      expect(Prime.Utils.isNumber(0)).toBe(true);
      expect(Prime.Utils.isNumber(123)).toBe(true);
      expect(Prime.Utils.isNumber(3.14)).toBe(true);
    });

    test("isNumber returns false for non-numbers", () => {
      expect(Prime.Utils.isNumber(NaN)).toBe(false);
      expect(Prime.Utils.isNumber("123")).toBe(false);
      expect(Prime.Utils.isNumber({})).toBe(false);
    });

    test("isString returns true for strings", () => {
      expect(Prime.Utils.isString("")).toBe(true);
      expect(Prime.Utils.isString("hello")).toBe(true);
    });

    test("isString returns false for non-strings", () => {
      expect(Prime.Utils.isString(123)).toBe(false);
      expect(Prime.Utils.isString({})).toBe(false);
      expect(Prime.Utils.isString([])).toBe(false);
    });

    test("isBoolean returns true for booleans", () => {
      expect(Prime.Utils.isBoolean(true)).toBe(true);
      expect(Prime.Utils.isBoolean(false)).toBe(true);
    });

    test("isBoolean returns false for non-booleans", () => {
      expect(Prime.Utils.isBoolean(0)).toBe(false);
      expect(Prime.Utils.isBoolean(1)).toBe(false);
      expect(Prime.Utils.isBoolean("true")).toBe(false);
      expect(Prime.Utils.isBoolean({})).toBe(false);
    });
  });

  describe("Object Operations", () => {
    test("deepClone creates a deep copy of objects", () => {
      const original = {
        a: 1,
        b: { c: 2, d: [3, 4, { e: 5 }] },
        f: new Date(2023, 0, 1),
        g: /test/g,
      };

      const clone = Prime.Utils.deepClone(original);

      expect(clone).not.toBe(original);
      expect(clone.b).not.toBe(original.b);
      expect(clone.b.d).not.toBe(original.b.d);
      expect(clone.b.d[2]).not.toBe(original.b.d[2]);
      expect(clone).toEqual(original);
    });

    test("deepClone handles circular references", () => {
      const circular = { a: 1 };
      circular.self = circular;

      const circularClone = Prime.Utils.deepClone(circular);
      expect(circularClone).not.toBe(circular);
      expect(circularClone.self).toBe(circularClone);
    });

    test("memoize caches function results", () => {
      let callCount = 0;
      const expensiveFunction = (a, b) => {
        callCount++;
        return a + b;
      };

      const memoized = Prime.Utils.memoize(expensiveFunction);

      const result1 = memoized(1, 2);
      const result2 = memoized(1, 2);
      const result3 = memoized(2, 3);

      expect(result1).toBe(3);
      expect(result2).toBe(3);
      expect(result3).toBe(5);
      expect(callCount).toBe(2);
    });

    test("get retrieves nested properties", () => {
      const obj = { a: { b: { c: 42 } } };
      expect(Prime.Utils.get(obj, "a.b.c")).toBe(42);
      expect(Prime.Utils.get(obj, ["a", "b", "c"])).toBe(42);
      expect(Prime.Utils.get(obj, "a.x.y", "default")).toBe("default");
      expect(Prime.Utils.get(null, "a.b", "default")).toBe("default");
    });

    test("set creates nested properties", () => {
      const obj = {};
      Prime.Utils.set(obj, "a.b.c", 42);
      expect(obj.a.b.c).toBe(42);

      Prime.Utils.set(obj, ["x", "y", "z"], "value");
      expect(obj.x.y.z).toBe("value");
    });
  });

  describe("Utility Functions", () => {
    test("uuid generates unique identifiers", () => {
      const uuid1 = Prime.Utils.uuid();
      const uuid2 = Prime.Utils.uuid();

      expect(typeof uuid1).toBe("string");
      expect(uuid1.length).toBe(36);
      expect(uuid1).not.toBe(uuid2);
      expect(uuid1).toMatch(
        /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/,
      );
    });

    // Add more tests for other utility functions
  });

  describe("Using Custom Assertions", () => {
    test("custom assertions work correctly", () => {
      const value1 = 0.1 + 0.2;
      const value2 = 0.3;

      // This would fail with exact equality due to floating point precision
      // expect(value1).toBe(value2);

      // Using our custom assertion instead
      const error = Assertions.assertAdaptivePrecision(value1, value2, 1e-10);
      expect(error).toBeLessThan(1e-10);
    });
  });

  describe("Using Mocking Utilities", () => {
    test("createMock correctly mocks object methods", () => {
      const original = {
        add: (a, b) => a + b,
        multiply: (a, b) => a * b,
      };

      const mock = Mocking.createMock(original);

      // Set up a mock return value
      mock.results.add = 42;

      // Call the mocked method
      const result = mock.add(1, 2);

      // Verify the result
      expect(result).toBe(42);

      // Verify the call was tracked
      expect(mock.calls.add.length).toBe(1);
      expect(mock.calls.add[0][0]).toBe(1);
      expect(mock.calls.add[0][1]).toBe(2);
    });

    test("createSpy correctly tracks function calls", () => {
      const original = (a, b) => a * b;
      const spy = Mocking.createSpy(original);

      // Call the spy
      const result = spy(3, 4);

      // Verify it returned the correct result
      expect(result).toBe(12);

      // Verify the call was tracked
      expect(spy.getCallCount()).toBe(1);
      expect(spy.calls[0][0]).toBe(3);
      expect(spy.calls[0][1]).toBe(4);

      // Reset the spy
      spy.reset();
      expect(spy.getCallCount()).toBe(0);
    });
  });
});
