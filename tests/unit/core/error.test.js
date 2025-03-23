/**
 * PrimeOS Unit Tests - Error Classes
 * 
 * Tests for the error handling classes in the core module.
 */

const Prime = require('../../../src/core.js');
const { Assertions, Mocking } = require('../../utils');

describe('Error Classes', () => {
  describe('PrimeError', () => {
    test('creates base error with correct properties', () => {
      const error = new Prime.PrimeError("Test error");
      
      expect(error instanceof Error).toBe(true);
      expect(error instanceof Prime.PrimeError).toBe(true);
      expect(error.name).toBe("PrimeError");
      expect(error.message).toBe("Test error");
      expect(error.code).toBe("GENERIC_ERROR");
      expect(error.timestamp instanceof Date).toBe(true);
    });
    
    test('accepts custom code and context', () => {
      const error = new Prime.PrimeError("Custom error", {
        code: "CUSTOM_CODE",
        context: { key: "value" }
      });
      
      expect(error.code).toBe("CUSTOM_CODE");
      expect(error.context.key).toBe("value");
    });
    
    test('provides stack trace information', () => {
      const error = new Prime.PrimeError("Test error");
      expect(error.stack).toBeDefined();
      expect(typeof error.stack).toBe('string');
      expect(error.stack.includes('PrimeError: Test error')).toBe(true);
    });
  });

  describe('CoherenceViolationError', () => {
    test('extends PrimeError with coherence specific properties', () => {
      const constraint = { name: "TestConstraint", check: () => false };
      const magnitude = 0.75;
      
      const error = new Prime.CoherenceViolationError(
        "Coherence violation",
        constraint,
        magnitude
      );
      
      expect(error instanceof Prime.PrimeError).toBe(true);
      expect(error instanceof Prime.CoherenceViolationError).toBe(true);
      expect(error.name).toBe("CoherenceViolationError");
      expect(error.message).toBe("Coherence violation");
      expect(error.constraint).toBe(constraint);
      expect(error.magnitude).toBe(magnitude);
    });
    
    test('handles context data', () => {
      const constraint = { name: "TestConstraint", check: () => false };
      const magnitude = 0.5;
      const context = { component: "TestComponent" };
      
      const error = new Prime.CoherenceViolationError(
        "Coherence violation",
        constraint,
        magnitude,
        context
      );
      
      expect(error.context).toBeDefined();
      expect(error.context.component).toBe("TestComponent");
    });
  });

  describe('MathematicalError', () => {
    test('extends PrimeError for mathematical errors', () => {
      const error = new Prime.MathematicalError("Math error");
      
      expect(error instanceof Prime.PrimeError).toBe(true);
      expect(error.name).toBe("MathematicalError");
      expect(error.message).toBe("Math error");
    });
    
    test('accepts custom code and context', () => {
      const error = new Prime.MathematicalError("Division by zero", {
        code: "DIVISION_BY_ZERO",
        context: { operation: "division", value: 0 }
      });
      
      expect(error.code).toBe("DIVISION_BY_ZERO");
      expect(error.context.operation).toBe("division");
      expect(error.context.value).toBe(0);
    });
  });

  describe('InvalidOperationError', () => {
    test('extends PrimeError for operation errors', () => {
      const error = new Prime.InvalidOperationError("Invalid operation");
      
      expect(error instanceof Prime.PrimeError).toBe(true);
      expect(error.name).toBe("InvalidOperationError");
      expect(error.message).toBe("Invalid operation");
    });
  });

  describe('ConfigurationError', () => {
    test('extends PrimeError for configuration errors', () => {
      const error = new Prime.ConfigurationError("Config error");
      
      expect(error instanceof Prime.PrimeError).toBe(true);
      expect(error.name).toBe("ConfigurationError");
      expect(error.message).toBe("Config error");
    });
  });

  describe('ValidationError', () => {
    test('extends PrimeError for validation errors', () => {
      const error = new Prime.ValidationError("Validation error");
      
      expect(error instanceof Prime.PrimeError).toBe(true);
      expect(error.name).toBe("ValidationError");
      expect(error.message).toBe("Validation error");
    });
    
    test('provides details about invalid values', () => {
      const error = new Prime.ValidationError("Invalid type", {
        code: "INVALID_TYPE",
        context: { 
          expected: "string", 
          actual: "number",
          value: 42
        }
      });
      
      expect(error.code).toBe("INVALID_TYPE");
      expect(error.context.expected).toBe("string");
      expect(error.context.actual).toBe("number");
      expect(error.context.value).toBe(42);
    });
  });

  describe('Error throwing helpers', () => {
    test('can use Assertions.assertThrows to test error conditions', () => {
      const throwingFunction = () => {
        throw new Prime.ValidationError("Test validation error");
      };
      
      const error = Assertions.assertThrows(
        throwingFunction,
        Prime.ValidationError,
        "Function should throw ValidationError"
      );
      
      expect(error.message).toBe("Test validation error");
    });
    
    test('Assertions.assertThrows fails if wrong error type is thrown', () => {
      const wrongErrorFunction = () => {
        throw new Error("Regular error, not ValidationError");
      };
      
      expect(() => {
        Assertions.assertThrows(
          wrongErrorFunction,
          Prime.ValidationError,
          "Should throw ValidationError"
        );
      }).toThrow();
    });
    
    test('Assertions.assertThrows fails if no error is thrown', () => {
      const nonThrowingFunction = () => {
        // This function doesn't throw
        return true;
      };
      
      expect(() => {
        Assertions.assertThrows(
          nonThrowingFunction,
          Prime.ValidationError,
          "Should throw ValidationError"
        );
      }).toThrow();
    });
  });
});