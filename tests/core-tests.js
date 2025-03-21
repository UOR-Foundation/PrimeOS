/**
 * PrimeOS JavaScript Library - Core Tests
 * Test suite for the core.js module
 */

// Use CommonJS require instead of ES module import to avoid circular dependency issues
const Prime = require("../src/core.js");

// Enhanced test framework with better error handling and reporting
const Test = {
  passed: 0,
  failed: 0,
  skipped: 0,
  failureDetails: [],

  assert: function (condition, message) {
    try {
      if (condition) {
        this.passed++;
        console.log(`✓ PASS: ${message}`);
      } else {
        this.failed++;
        const error = new Error(`Assertion failed: ${message}`);
        this.failureDetails.push({
          message: message,
          error: error,
          stack: error.stack,
        });
        console.error(`✗ FAIL: ${message}`);
      }
    } catch (e) {
      this.failed++;
      this.failureDetails.push({
        message: `Exception during assertion: ${message}`,
        error: e,
        stack: e.stack,
      });
      console.error(`✗ ERROR: Exception during assertion: ${message}`, e);
    }
  },

  assertThrows: function (fn, errorType, message) {
    try {
      fn();
      this.failed++;
      const error = new Error(`Expected to throw ${errorType.name}`);
      this.failureDetails.push({
        message: message,
        error: error,
        stack: error.stack,
        expected: errorType.name,
        actual: "No error thrown",
      });
      console.error(`✗ FAIL: ${message} - Expected to throw ${errorType.name}`);
    } catch (error) {
      if (error instanceof errorType) {
        this.passed++;
        console.log(`✓ PASS: ${message}`);
      } else {
        this.failed++;
        this.failureDetails.push({
          message: message,
          error: error,
          stack: error.stack,
          expected: errorType.name,
          actual: error.constructor.name,
        });
        console.error(
          `✗ FAIL: ${message} - Expected error of type ${errorType.name}, got ${error.constructor.name}`,
        );
        console.error(error);
      }
    }
  },

  assertDeepEquals: function (actual, expected, message) {
    try {
      // Simple deep equality check - for more complex objects, consider using a dedicated library
      const actualStr = JSON.stringify(actual);
      const expectedStr = JSON.stringify(expected);

      if (actualStr === expectedStr) {
        this.passed++;
        console.log(`✓ PASS: ${message}`);
      } else {
        this.failed++;
        this.failureDetails.push({
          message: message,
          expected: expected,
          actual: actual,
          diff: {
            expected: expectedStr,
            actual: actualStr,
          },
        });
        console.error(
          `✗ FAIL: ${message} - Expected: ${expectedStr}, Actual: ${actualStr}`,
        );
      }
    } catch (e) {
      this.failed++;
      this.failureDetails.push({
        message: `Exception during deep equality assertion: ${message}`,
        error: e,
        stack: e.stack,
      });
      console.error(
        `✗ ERROR: Exception during deep equality assertion: ${message}`,
        e,
      );
    }
  },

  skip: function (message) {
    this.skipped++;
    console.warn(`○ SKIP: ${message}`);
  },

  run: function (name, tests) {
    console.log(`\n=== Running Test Suite: ${name} ===`);
    this.failureDetails = [];

    try {
      tests();
    } catch (error) {
      this.failed++;
      this.failureDetails.push({
        message: `Uncaught exception in test suite: ${name}`,
        error: error,
        stack: error.stack,
      });
      console.error(
        `✗ FATAL ERROR: Uncaught exception in test suite: ${name}`,
        error,
      );
    }

    console.log(`\n=== Test Summary: ${name} ===`);
    console.log(
      `Passed: ${this.passed}, Failed: ${this.failed}, Skipped: ${this.skipped}`,
    );

    if (this.failed > 0) {
      console.error(`\n=== Failure Details for ${name} ===`);
      this.failureDetails.forEach((detail, index) => {
        console.error(`Failure #${index + 1}: ${detail.message}`);
        if (detail.stack) {
          console.error(`Stack: ${detail.stack.split("\n")[1]}`);
        }
      });
    }

    // Reset counters for next suite
    const total = this.passed + this.failed;
    const oldPassed = this.passed;
    const oldFailed = this.failed;
    const oldSkipped = this.skipped;
    const oldFailureDetails = [...this.failureDetails];
    this.passed = 0;
    this.failed = 0;
    this.skipped = 0;
    this.failureDetails = [];

    return {
      suite: name,
      passed: oldPassed,
      failed: oldFailed,
      skipped: oldSkipped,
      total: total,
      success: oldFailed === 0,
      failureDetails: oldFailureDetails,
    };
  },
};

// Test suites
const testResults = [];

// Test Utilities
testResults.push(
  Test.run("Utilities", function () {
    // isObject tests
    Test.assert(
      Prime.Utils.isObject({}),
      "isObject returns true for empty object",
    );
    Test.assert(
      Prime.Utils.isObject({ a: 1 }),
      "isObject returns true for object literal",
    );
    Test.assert(!Prime.Utils.isObject(null), "isObject returns false for null");
    Test.assert(!Prime.Utils.isObject([]), "isObject returns false for array");
    Test.assert(
      !Prime.Utils.isObject("string"),
      "isObject returns false for string",
    );
    Test.assert(
      !Prime.Utils.isObject(123),
      "isObject returns false for number",
    );
    Test.assert(
      !Prime.Utils.isObject(true),
      "isObject returns false for boolean",
    );
    Test.assert(
      !Prime.Utils.isObject(undefined),
      "isObject returns false for undefined",
    );
    Test.assert(
      !Prime.Utils.isObject(function () {}),
      "isObject returns false for function",
    );

    // isFunction tests
    Test.assert(
      Prime.Utils.isFunction(function () {}),
      "isFunction returns true for function declaration",
    );
    Test.assert(
      Prime.Utils.isFunction(() => {}),
      "isFunction returns true for arrow function",
    );
    Test.assert(
      !Prime.Utils.isFunction({}),
      "isFunction returns false for object",
    );
    Test.assert(
      !Prime.Utils.isFunction([]),
      "isFunction returns false for array",
    );

    // isArray tests
    Test.assert(
      Prime.Utils.isArray([]),
      "isArray returns true for empty array",
    );
    Test.assert(
      Prime.Utils.isArray([1, 2, 3]),
      "isArray returns true for array with elements",
    );
    Test.assert(!Prime.Utils.isArray({}), "isArray returns false for object");
    Test.assert(
      !Prime.Utils.isArray("string"),
      "isArray returns false for string",
    );

    // isNumber tests
    Test.assert(Prime.Utils.isNumber(0), "isNumber returns true for 0");
    Test.assert(Prime.Utils.isNumber(123), "isNumber returns true for integer");
    Test.assert(Prime.Utils.isNumber(3.14), "isNumber returns true for float");
    Test.assert(!Prime.Utils.isNumber(NaN), "isNumber returns false for NaN");
    Test.assert(
      !Prime.Utils.isNumber("123"),
      "isNumber returns false for numeric string",
    );

    // isString tests
    Test.assert(
      Prime.Utils.isString(""),
      "isString returns true for empty string",
    );
    Test.assert(
      Prime.Utils.isString("hello"),
      "isString returns true for non-empty string",
    );
    Test.assert(
      !Prime.Utils.isString(123),
      "isString returns false for number",
    );

    // isBoolean tests
    Test.assert(Prime.Utils.isBoolean(true), "isBoolean returns true for true");
    Test.assert(
      Prime.Utils.isBoolean(false),
      "isBoolean returns true for false",
    );
    Test.assert(!Prime.Utils.isBoolean(0), "isBoolean returns false for 0");
    Test.assert(!Prime.Utils.isBoolean(1), "isBoolean returns false for 1");
    Test.assert(
      !Prime.Utils.isBoolean("true"),
      "isBoolean returns false for string 'true'",
    );

    // deepClone tests
    const original = {
      a: 1,
      b: { c: 2, d: [3, 4, { e: 5 }] },
      f: new Date(2023, 0, 1),
      g: /test/g,
      h: new Map([["key", "value"]]),
      i: new Set([1, 2, 3]),
    };

    const clone = Prime.Utils.deepClone(original);

    Test.assert(
      clone !== original,
      "deepClone creates a different object reference",
    );
    Test.assert(clone.b !== original.b, "deepClone creates deep object copies");
    Test.assert(
      clone.b.d !== original.b.d,
      "deepClone creates deep array copies",
    );
    Test.assert(
      clone.b.d[2] !== original.b.d[2],
      "deepClone creates deep nested object copies",
    );
    Test.assert(
      clone.f.getTime() === original.f.getTime(),
      "deepClone preserves Date values",
    );
    Test.assert(
      clone.g.source === original.g.source &&
        clone.g.flags === original.g.flags,
      "deepClone preserves RegExp properties",
    );
    Test.assert(
      clone.h.get("key") === original.h.get("key"),
      "deepClone preserves Map entries",
    );
    Test.assert(
      clone.i.has(1) && clone.i.has(2) && clone.i.has(3),
      "deepClone preserves Set values",
    );

    // Test circular references
    const circular = { a: 1 };
    circular.self = circular;

    const circularClone = Prime.Utils.deepClone(circular);
    Test.assert(
      circularClone !== circular,
      "deepClone handles circular references (different reference)",
    );
    Test.assert(
      circularClone.self === circularClone,
      "deepClone preserves circular structure",
    );

    // memoize tests
    let callCount = 0;
    const expensiveFunction = (a, b) => {
      callCount++;
      return a + b;
    };

    const memoized = Prime.Utils.memoize(expensiveFunction);

    const result1 = memoized(1, 2);
    const result2 = memoized(1, 2); // Should be cached
    const result3 = memoized(2, 3); // Different args, not cached

    Test.assert(result1 === 3, "memoize returns correct result first time");
    Test.assert(result2 === 3, "memoize returns correct result from cache");
    Test.assert(
      result3 === 5,
      "memoize returns correct result for different args",
    );
    Test.assert(
      callCount === 2,
      "memoize calls original function only when needed",
    );

    // get tests
    const obj = { a: { b: { c: 42 } } };
    Test.assert(
      Prime.Utils.get(obj, "a.b.c") === 42,
      "get retrieves nested property with string path",
    );
    Test.assert(
      Prime.Utils.get(obj, ["a", "b", "c"]) === 42,
      "get retrieves nested property with array path",
    );
    Test.assert(
      Prime.Utils.get(obj, "a.x.y", "default") === "default",
      "get returns default for missing property",
    );
    Test.assert(
      Prime.Utils.get(null, "a.b", "default") === "default",
      "get handles null object",
    );

    // set tests
    const setObj = {};
    Prime.Utils.set(setObj, "a.b.c", 42);
    Test.assert(setObj.a.b.c === 42, "set creates nested properties");

    Prime.Utils.set(setObj, ["x", "y", "z"], "value");
    Test.assert(setObj.x.y.z === "value", "set works with array path");

    // uuid tests
    const uuid1 = Prime.Utils.uuid();
    const uuid2 = Prime.Utils.uuid();

    Test.assert(typeof uuid1 === "string", "uuid returns a string");
    Test.assert(uuid1.length === 36, "uuid has correct length (36 characters)");
    Test.assert(uuid1 !== uuid2, "uuid generates unique values");
    Test.assert(
      /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/.test(
        uuid1,
      ),
      "uuid has correct format (RFC4122 version 4)",
    );
  }),
);

// Test Error Classes
testResults.push(
  Test.run("Error Classes", function () {
    // PrimeError tests
    const error1 = new Prime.PrimeError("Test error");
    Test.assert(error1 instanceof Error, "PrimeError is an instance of Error");
    Test.assert(
      error1 instanceof Prime.PrimeError,
      "PrimeError is an instance of PrimeError",
    );
    Test.assert(error1.name === "PrimeError", "PrimeError has correct name");
    Test.assert(
      error1.message === "Test error",
      "PrimeError has correct message",
    );
    Test.assert(error1.code === "GENERIC_ERROR", "PrimeError has default code");
    Test.assert(error1.timestamp instanceof Date, "PrimeError has timestamp");

    const error2 = new Prime.PrimeError("Custom error", {
      code: "CUSTOM_CODE",
      context: { key: "value" },
    });
    Test.assert(
      error2.code === "CUSTOM_CODE",
      "PrimeError accepts custom code",
    );
    Test.assert(
      error2.context.key === "value",
      "PrimeError stores context data",
    );

    // CoherenceViolationError tests
    const constraint = { name: "TestConstraint", check: () => false };
    const coherenceError = new Prime.CoherenceViolationError(
      "Coherence violation",
      constraint,
      0.75,
    );
    Test.assert(
      coherenceError instanceof Prime.PrimeError,
      "CoherenceViolationError is a PrimeError",
    );
    Test.assert(
      coherenceError.constraint === constraint,
      "CoherenceViolationError stores constraint",
    );
    Test.assert(
      coherenceError.magnitude === 0.75,
      "CoherenceViolationError stores magnitude",
    );

    // MathematicalError tests
    const mathError = new Prime.MathematicalError("Math error");
    Test.assert(
      mathError instanceof Prime.PrimeError,
      "MathematicalError is a PrimeError",
    );
    Test.assert(
      mathError.name === "MathematicalError",
      "MathematicalError has correct name",
    );

    // InvalidOperationError tests
    const opError = new Prime.InvalidOperationError("Invalid operation");
    Test.assert(
      opError instanceof Prime.PrimeError,
      "InvalidOperationError is a PrimeError",
    );
    Test.assert(
      opError.name === "InvalidOperationError",
      "InvalidOperationError has correct name",
    );

    // ConfigurationError tests
    const configError = new Prime.ConfigurationError("Config error");
    Test.assert(
      configError instanceof Prime.PrimeError,
      "ConfigurationError is a PrimeError",
    );
    Test.assert(
      configError.name === "ConfigurationError",
      "ConfigurationError has correct name",
    );

    // ValidationError tests
    const validationError = new Prime.ValidationError("Validation error");
    Test.assert(
      validationError instanceof Prime.PrimeError,
      "ValidationError is a PrimeError",
    );
    Test.assert(
      validationError.name === "ValidationError",
      "ValidationError has correct name",
    );
  }),
);

// Test EventBus
testResults.push(
  Test.run("EventBus", function () {
    // Reset event bus for testing
    Prime.EventBus.clear();

    // subscribe and publish tests
    let callCount = 0;
    let lastData = null;

    const handler = (data) => {
      callCount++;
      lastData = data;
    };

    // Test subscription
    const unsubscribe = Prime.EventBus.subscribe("test-event", handler);
    Test.assert(
      typeof unsubscribe === "function",
      "subscribe returns unsubscribe function",
    );

    // Test publishing
    Prime.EventBus.publish("test-event", { value: 42 });
    Test.assert(callCount === 1, "Event handler was called once");
    Test.assert(
      lastData && lastData.value === 42,
      "Event handler received correct data",
    );

    // Test multiple handlers
    let secondCallCount = 0;
    Prime.EventBus.subscribe("test-event", () => secondCallCount++);

    Prime.EventBus.publish("test-event", { value: "test" });
    Test.assert(callCount === 2, "First handler called again");
    Test.assert(secondCallCount === 1, "Second handler was called");

    // Test unsubscribe
    unsubscribe();
    Prime.EventBus.publish("test-event", {});
    Test.assert(callCount === 2, "Unsubscribed handler not called");
    Test.assert(secondCallCount === 2, "Other handler still called");

    // Test non-existent event
    Prime.EventBus.publish("non-existent-event", {});
    // Should not error

    // Test clear
    Prime.EventBus.clear("test-event");
    Prime.EventBus.publish("test-event", {});
    Test.assert(secondCallCount === 2, "Handler not called after clear");

    // Test clear entire bus
    let thirdCallCount = 0;
    Prime.EventBus.subscribe("another-event", () => thirdCallCount++);
    Prime.EventBus.publish("another-event", {});
    Test.assert(thirdCallCount === 1, "Handler for another event was called");

    Prime.EventBus.clear(); // Clear all events
    Prime.EventBus.publish("another-event", {});
    Test.assert(
      thirdCallCount === 1,
      "Handler not called after clearing all events",
    );

    // Test error handling in event handlers
    Prime.EventBus.clear();

    let safeHandlerCalled = false;
    const errorHandler = () => {
      throw new Error("Error in handler");
    };
    const safeHandler = () => {
      safeHandlerCalled = true;
    };

    Prime.EventBus.subscribe("error-event", errorHandler);
    Prime.EventBus.subscribe("error-event", safeHandler);

    // This should not throw, and the second handler should still be called
    Prime.EventBus.publish("error-event", {});
    Test.assert(
      safeHandlerCalled,
      "Safe handler called despite error in another handler",
    );

    // Test error handling for invalid event name
    Test.assertThrows(
      () => Prime.EventBus.subscribe(123, () => {}),
      Prime.ValidationError,
      "subscribe throws for non-string event name",
    );

    // Test error handling for invalid callback
    Test.assertThrows(
      () => Prime.EventBus.subscribe("test-event", "not a function"),
      Prime.ValidationError,
      "subscribe throws for non-function callback",
    );

    // Test unsubscribe edge cases
    const emptyUnsubscribe = Prime.EventBus.unsubscribe(
      "non-existent-event",
      () => {},
    );
    Test.assert(
      emptyUnsubscribe === false,
      "unsubscribe returns false for non-existent event",
    );

    const validEvent = "valid-event";
    const validHandler = () => {};
    Prime.EventBus.subscribe(validEvent, validHandler);
    const validUnsubscribe = Prime.EventBus.unsubscribe(
      validEvent,
      validHandler,
    );
    Test.assert(
      validUnsubscribe === true,
      "unsubscribe returns true for successful unsubscribe",
    );
  }),
);

// Test Logger
testResults.push(
  Test.run("Logger", function () {
    // Backup original console methods
    const originalConsole = {
      debug: console.debug,
      info: console.info,
      warn: console.warn,
      error: console.error,
    };

    // Mock console methods for testing
    let debugCalls = 0;
    let infoCalls = 0;
    let warnCalls = 0;
    let errorCalls = 0;

    console.debug = () => debugCalls++;
    console.info = () => infoCalls++;
    console.warn = () => warnCalls++;
    console.error = () => errorCalls++;

    // Test defaulting to INFO level
    Prime.Logger.debug("test");
    Prime.Logger.info("test");
    Prime.Logger.warn("test");
    Prime.Logger.error("test");

    Test.assert(debugCalls === 0, "DEBUG not logged at default INFO level");
    Test.assert(infoCalls === 1, "INFO logged at default INFO level");
    Test.assert(warnCalls === 1, "WARN logged at default INFO level");
    Test.assert(errorCalls === 1, "ERROR logged at default INFO level");

    // Test level change to DEBUG
    Prime.Logger.setLevel("DEBUG");

    debugCalls = 0;
    infoCalls = 0;
    warnCalls = 0;
    errorCalls = 0;

    Prime.Logger.debug("test");
    Prime.Logger.info("test");
    Prime.Logger.warn("test");
    Prime.Logger.error("test");

    Test.assert(debugCalls === 1, "DEBUG logged at DEBUG level");
    Test.assert(infoCalls === 1, "INFO logged at DEBUG level");
    Test.assert(warnCalls === 1, "WARN logged at DEBUG level");
    Test.assert(errorCalls === 1, "ERROR logged at DEBUG level");

    // Test level change to ERROR
    Prime.Logger.setLevel("ERROR");

    debugCalls = 0;
    infoCalls = 0;
    warnCalls = 0;
    errorCalls = 0;

    Prime.Logger.debug("test");
    Prime.Logger.info("test");
    Prime.Logger.warn("test");
    Prime.Logger.error("test");

    Test.assert(debugCalls === 0, "DEBUG not logged at ERROR level");
    Test.assert(infoCalls === 0, "INFO not logged at ERROR level");
    Test.assert(warnCalls === 0, "WARN not logged at ERROR level");
    Test.assert(errorCalls === 1, "ERROR logged at ERROR level");

    // Test invalid level
    Test.assertThrows(
      () => Prime.Logger.setLevel("INVALID_LEVEL"),
      Prime.ValidationError,
      "setLevel throws for invalid level string",
    );

    // Restore original console methods
    console.debug = originalConsole.debug;
    console.info = originalConsole.info;
    console.warn = originalConsole.warn;
    console.error = originalConsole.error;
  }),
);

// Test Version Management
testResults.push(
  Test.run("Version Management", function () {
    // Test version property exists
    Test.assert(typeof Prime.version === "string", "version is a string");
    Test.assert(
      /^\d+\.\d+\.\d+$/.test(Prime.version),
      "version follows semantic versioning format",
    );

    // Test validateVersion
    Test.assert(Prime.validateVersion("0.0.1"), "Validates higher version");
    Test.assert(
      Prime.validateVersion("0.9.0"),
      "Validates higher minor version",
    );
    Test.assert(
      Prime.validateVersion("0.9.9"),
      "Validates higher minor and patch versions",
    );
    Test.assert(Prime.validateVersion(Prime.version), "Validates same version");
    Test.assert(
      !Prime.validateVersion("99.0.0"),
      "Rejects higher major version",
    );

    // Test isCompatible
    Test.assert(
      Prime.isCompatible({
        minVersion: "0.0.1",
        features: [],
      }),
      "isCompatible works with valid version and no features",
    );

    Test.assert(
      !Prime.isCompatible({
        minVersion: "99.0.0",
        features: [],
      }),
      "isCompatible rejects with higher required version",
    );

    // Test with features
    const result = Prime.isCompatible({
      minVersion: "0.0.1",
      features: [],
    });

    Test.assert(
      result,
      "isCompatible works with valid version and no features",
    );
  }),
);

// Test Testing Utilities
testResults.push(
  Test.run("Testing Utilities", function () {
    // Test assert
    let assertCalled = false;
    try {
      Prime.Testing.assert(true, "Assert passes");
      assertCalled = true;
    } catch (e) {
      // Should not reach here
    }
    Test.assert(assertCalled, "assert doesn't throw for true condition");

    Test.assertThrows(
      () => Prime.Testing.assert(false, "Assert fails"),
      Prime.ValidationError,
      "assert throws ValidationError for false condition",
    );

    // Test createMock
    const original = {
      method1: (a, b) => a + b,
      method2: () => "original",
    };

    const mock = Prime.Testing.createMock(original);

    Test.assert(
      typeof mock.calls === "object",
      "Mock has calls tracking object",
    );
    Test.assert(typeof mock.results === "object", "Mock has results object");

    // Test call tracking
    mock.method1(1, 2);
    Test.assert(
      Array.isArray(mock.calls.method1),
      "Calls are tracked in an array",
    );
    Test.assert(mock.calls.method1.length === 1, "Call count is correct");
    Test.assert(mock.calls.method1[0][0] === 1, "First argument is tracked");
    Test.assert(mock.calls.method1[0][1] === 2, "Second argument is tracked");

    // Test result overriding
    mock.results.method2 = "mocked";
    Test.assert(mock.method2() === "mocked", "Result can be overridden");

    // Test createSpy
    const original2 = (a, b) => a * b;
    const spy = Prime.Testing.createSpy(original2);

    const result1 = spy(3, 4);
    Test.assert(result1 === 12, "Spy calls original function");
    Test.assert(spy.getCallCount() === 1, "Spy tracks call count");
    Test.assert(spy.calls.length === 1, "Spy has calls array");
    Test.assert(spy.calls[0][0] === 3, "Spy tracks first argument");
    Test.assert(spy.calls[0][1] === 4, "Spy tracks second argument");

    spy.reset();
    Test.assert(spy.getCallCount() === 0, "Spy can be reset");
  }),
);

// Test ModuleLoader
testResults.push(
  Test.run("ModuleLoader", function () {
    // Test detectEnvironment
    const env = Prime.ModuleLoader.detectEnvironment();
    Test.assert(typeof env === "string", "detectEnvironment returns a string");

    // Test registration
    const mockModule = { test: true };
    const result = Prime.ModuleLoader.register("testModule", mockModule);
    Test.assert(result === true, "register returns true on success");
    Test.assert(
      Prime.testModule === mockModule,
      "Module is registered on Prime object",
    );

    // Test validation
    Test.assertThrows(
      () => Prime.ModuleLoader.register(123, {}),
      Prime.ValidationError,
      "register throws for invalid module name",
    );

    Test.assertThrows(
      () => Prime.ModuleLoader.register("test", "not an object"),
      Prime.ValidationError,
      "register throws for invalid module object",
    );

    // Clean up test module
    delete Prime.testModule;
  }),
);

// Output final test summary with enhanced reporting
let overallPassed = 0;
let overallFailed = 0;
let overallSkipped = 0;
let allFailureDetails = [];

console.log("\n=== OVERALL TEST SUMMARY ===");
testResults.forEach((result) => {
  console.log(
    `${result.suite}: ${result.passed}/${result.total} passed, ${result.failed} failed, ${result.skipped} skipped`,
  );
  overallPassed += result.passed;
  overallFailed += result.failed;
  overallSkipped += result.skipped;

  // Collect failure details
  if (result.failureDetails && result.failureDetails.length > 0) {
    allFailureDetails.push({
      suite: result.suite,
      details: result.failureDetails,
    });
  }
});

console.log(
  `\nTOTAL: ${overallPassed}/${overallPassed + overallFailed} passed, ${overallFailed} failed, ${overallSkipped} skipped`,
);
console.log(`OVERALL STATUS: ${overallFailed === 0 ? "SUCCESS" : "FAILURE"}`);

// If any tests failed, output a consolidated failure report
if (overallFailed > 0) {
  console.error("\n=== CONSOLIDATED FAILURE REPORT ===");
  allFailureDetails.forEach((suiteFails) => {
    console.error(`\nSuite: ${suiteFails.suite}`);
    suiteFails.details.forEach((detail, index) => {
      console.error(`  ${index + 1}. ${detail.message}`);
      if (detail.expected && detail.actual) {
        console.error(`     Expected: ${detail.expected}`);
        console.error(`     Actual: ${detail.actual}`);
      }
      if (detail.stack) {
        const stackLine =
          detail.stack.split("\n")[1] || detail.stack.split("\n")[0];
        console.error(`     Location: ${stackLine.trim()}`);
      }
    });
  });
}

// Export test results using CommonJS
const testSummary = {
  suites: testResults,
  total: {
    passed: overallPassed,
    failed: overallFailed,
    skipped: overallSkipped,
    success: overallFailed === 0,
  },
  failureDetails: allFailureDetails,
};

module.exports = { testSummary };

// Add Jest-compatible tests
test("Core module tests - overall success", () => {
  // Our custom test framework already ran the tests and output results
  // This test is just to make Jest happy
  expect(testSummary.total.passed).toBeGreaterThan(0);

  // Also make Jest fail if our tests failed
  if (testSummary.total.failed > 0) {
    // Create a detailed error message from the failure details
    const errorMessages = allFailureDetails
      .map(
        (suite) =>
          `Suite "${suite.suite}" had ${suite.details.length} failure(s): ${suite.details
            .map((d) => d.message)
            .join("; ")}`,
      )
      .join("\n");

    throw new Error(
      `${testSummary.total.failed} test(s) failed:\n${errorMessages}`,
    );
  }
});

// Test that all expected test suites were run
test("Core module test suites", () => {
  const expectedSuites = [
    "Utilities",
    "Error Classes",
    "EventBus",
    "Logger",
    "Version Management",
    "Testing Utilities",
    "ModuleLoader",
  ];

  const actualSuites = testResults.map((r) => r.suite);

  expectedSuites.forEach((suiteName) => {
    expect(actualSuites).toContain(suiteName);
  });
});
