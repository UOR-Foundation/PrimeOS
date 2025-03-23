/**
 * PrimeOS Browser Tests - Error Classes
 *
 * Tests for the error handling classes in the core module.
 */

// Register tests with TestRunner
TestRunner.suite("Core Errors", function () {
  TestRunner.test(
    "PrimeError creates base error with correct properties",
    function () {
      const error = new Prime.PrimeError("Test error");

      TestRunner.assert(error instanceof Error, "Should be an Error instance");
      TestRunner.assert(
        error instanceof Prime.PrimeError,
        "Should be a PrimeError instance",
      );
      TestRunner.assertEqual(
        error.name,
        "PrimeError",
        "Should have correct name",
      );
      TestRunner.assertEqual(
        error.message,
        "Test error",
        "Should have correct message",
      );
      TestRunner.assert(
        typeof error.timestamp === "string",
        "Should have timestamp",
      );
    },
  );

  TestRunner.test("PrimeError accepts custom code and context", function () {
    const error = new Prime.PrimeError("Custom error", {
      code: "CUSTOM_CODE",
      context: { key: "value" },
    });

    TestRunner.assertEqual(
      error.code,
      "CUSTOM_CODE",
      "Should have custom code",
    );
    TestRunner.assertEqual(error.context.key, "value", "Should have context");
  });

  TestRunner.test("PrimeError provides stack trace information", function () {
    const error = new Prime.PrimeError("Test error");
    TestRunner.assert(error.stack !== undefined, "Should have stack trace");
    TestRunner.assert(
      typeof error.stack === "string",
      "Stack should be string",
    );
    TestRunner.assert(
      error.stack.includes("Test error"),
      "Stack should include error message",
    );
  });

  TestRunner.test(
    "CoherenceViolationError extends PrimeError with specific properties",
    function () {
      const constraint = {
        name: "TestConstraint",
        check: function () {
          return false;
        },
      };
      const magnitude = 0.75;

      const error = new Prime.CoherenceViolationError(
        "Coherence violation",
        constraint,
        magnitude,
      );

      TestRunner.assert(
        error instanceof Prime.PrimeError,
        "Should be a PrimeError instance",
      );
      TestRunner.assert(
        error instanceof Prime.CoherenceViolationError,
        "Should be a CoherenceViolationError instance",
      );
      TestRunner.assertEqual(
        error.name,
        "CoherenceViolationError",
        "Should have correct name",
      );
      TestRunner.assertEqual(
        error.message,
        "Coherence violation",
        "Should have correct message",
      );
      TestRunner.assertEqual(
        error.constraint,
        constraint,
        "Should store constraint reference",
      );
      TestRunner.assertEqual(
        error.magnitude,
        magnitude,
        "Should store magnitude",
      );
    },
  );

  TestRunner.test(
    "CoherenceViolationError handles context data properly",
    function () {
      const constraint = {
        name: "TestConstraint",
        check: function () {
          return false;
        },
      };
      const magnitude = 0.5;
      const context = { component: "TestComponent" };

      const error = new Prime.CoherenceViolationError(
        "Coherence violation",
        constraint,
        magnitude,
        context,
      );

      // Test that context is defined
      TestRunner.assert(
        error.context !== undefined,
        "Should have context object",
      );

      // Test that constraint properties are preserved
      TestRunner.assert(
        error.constraint !== undefined,
        "Should have constraint",
      );
      TestRunner.assertEqual(
        error.constraint.name,
        "TestConstraint",
        "Constraint should have correct name",
      );
      TestRunner.assertEqual(
        error.magnitude,
        0.5,
        "Should have correct magnitude",
      );

      // Original context object should not be modified
      TestRunner.assertEqual(
        context.component,
        "TestComponent",
        "Original context should be unchanged",
      );
    },
  );

  TestRunner.test("Error hierarchy is properly constructed", function () {
    // Test a few representative error types
    const validation = new Prime.ValidationError("Validation error");
    const config = new Prime.ConfigurationError("Config error");
    const operation = new Prime.InvalidOperationError("Invalid operation");

    // All should be instances of PrimeError
    TestRunner.assert(
      validation instanceof Prime.PrimeError,
      "ValidationError should be a PrimeError",
    );
    TestRunner.assert(
      config instanceof Prime.PrimeError,
      "ConfigurationError should be a PrimeError",
    );
    TestRunner.assert(
      operation instanceof Prime.PrimeError,
      "InvalidOperationError should be a PrimeError",
    );

    // Each should have correct name
    TestRunner.assertEqual(
      validation.name,
      "ValidationError",
      "Should have correct name",
    );
    TestRunner.assertEqual(
      config.name,
      "ConfigurationError",
      "Should have correct name",
    );
    TestRunner.assertEqual(
      operation.name,
      "InvalidOperationError",
      "Should have correct name",
    );
  });

  TestRunner.test(
    "ValidationError provides details about invalid values",
    function () {
      const error = new Prime.ValidationError("Invalid type", {
        code: "INVALID_TYPE",
        context: {
          expected: "string",
          actual: "number",
          value: 42,
        },
      });

      TestRunner.assertEqual(
        error.code,
        "INVALID_TYPE",
        "Should have correct code",
      );
      TestRunner.assertEqual(
        error.context.expected,
        "string",
        "Should store expected type",
      );
      TestRunner.assertEqual(
        error.context.actual,
        "number",
        "Should store actual type",
      );
      TestRunner.assertEqual(
        error.context.value,
        42,
        "Should store invalid value",
      );
    },
  );
});
