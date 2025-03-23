/**
 * PrimeOS JavaScript Library - System Coherence Unit Tests
 * Tests for the system coherence functionality that manages global coherence across components
 */

const Prime = require('../../../src/core.js');
require('../../../src/mathematics.js');
require('../../../src/coherence.js');

// Import test utilities
const { assertAdaptivePrecision, assertThrows } = require('../../utils/assertions');

// Helper function to create a Clifford algebra with multivectors for testing
function createTestAlgebra() {
  const algebra = Prime.Clifford.create({ dimension: 3 });
  const scalar = algebra.scalar(5);
  const vector = algebra.vector([1, 2, 3]);
  const bivector = algebra.bivector([
    [0, 1, 0],
    [0, 0, 1],
    [0, 0, 0],
  ]);

  return { algebra, scalar, vector, bivector };
}

describe('System Coherence', () => {
  beforeEach(() => {
    // Clear existing components before each test
    Prime.coherence.systemCoherence.components = [];
  });

  describe('Component Registration', () => {
    test('should register components with default weight', () => {
      const { vector } = createTestAlgebra();
      
      // Register component
      const unregister = Prime.coherence.systemCoherence.register(vector);
      
      // Test registration
      expect(Prime.coherence.systemCoherence.components.length).toBe(1);
      expect(Prime.coherence.systemCoherence.components[0].component).toBe(vector);
      expect(Prime.coherence.systemCoherence.components[0].weight).toBe(1); // Default weight
      
      // Test unregister function
      unregister();
      expect(Prime.coherence.systemCoherence.components.length).toBe(0);
    });

    test('should register components with custom weight', () => {
      const { vector } = createTestAlgebra();
      
      // Register component with weight
      const unregister = Prime.coherence.systemCoherence.register(vector, 2.5);
      
      // Test registration
      expect(Prime.coherence.systemCoherence.components.length).toBe(1);
      expect(Prime.coherence.systemCoherence.components[0].component).toBe(vector);
      expect(Prime.coherence.systemCoherence.components[0].weight).toBe(2.5);
    });

    test('should register multiple components', () => {
      const { scalar, vector } = createTestAlgebra();
      
      // Register components
      Prime.coherence.systemCoherence.register(scalar, 1);
      Prime.coherence.systemCoherence.register(vector, 2);
      
      // Test registration
      expect(Prime.coherence.systemCoherence.components.length).toBe(2);
    });

    test('should unregister components directly', () => {
      const { scalar, vector } = createTestAlgebra();
      const customObj = { value: 5, norm: () => 5 };
      
      // Register components
      Prime.coherence.systemCoherence.register(scalar, 1);
      Prime.coherence.systemCoherence.register(vector, 2);
      Prime.coherence.systemCoherence.register(customObj, 3);
      
      // Test registration
      expect(Prime.coherence.systemCoherence.components.length).toBe(3);
      
      // Unregister one component
      Prime.coherence.systemCoherence.unregister(vector);
      expect(Prime.coherence.systemCoherence.components.length).toBe(2);
      
      // Unregister by reference
      Prime.coherence.systemCoherence.unregister(customObj);
      expect(Prime.coherence.systemCoherence.components.length).toBe(1);
    });
  });

  describe('Global Coherence Calculation', () => {
    test('should calculate global coherence using default method', () => {
      // Register components with known norms
      Prime.coherence.systemCoherence.register(
        { value: 1, norm: () => 0.1 },
        1
      );
      Prime.coherence.systemCoherence.register(
        { value: 2, norm: () => 0.2 },
        2
      );
      Prime.coherence.systemCoherence.register(
        { value: 3, norm: () => 0.3 },
        3
      );
      
      // Calculate expected value using weighted RMS
      const sumWeightedNormSquared =
        1 * 1 * 0.1 * 0.1 + 2 * 2 * 0.2 * 0.2 + 3 * 3 * 0.3 * 0.3;
      const sumWeights = 1 + 2 + 3;
      const expected = Math.sqrt(sumWeightedNormSquared) / sumWeights;
      
      // Test global coherence
      const globalCoherence = Prime.coherence.systemCoherence.calculateGlobalCoherence();
      expect(globalCoherence).toBeCloseTo(expected, 10);
    });

    test('should calculate global coherence using geometric mean', () => {
      // Register components with known norms
      Prime.coherence.systemCoherence.register(
        { value: 1, norm: () => 0.1 },
        1
      );
      Prime.coherence.systemCoherence.register(
        { value: 2, norm: () => 0.2 },
        2
      );
      Prime.coherence.systemCoherence.register(
        { value: 3, norm: () => 0.3 },
        3
      );
      
      // Calculate expected value using geometric mean
      const sumWeights = 1 + 2 + 3;
      const expectedGeometric = Math.pow(
        Math.pow(0.1, 1) * Math.pow(0.2, 2) * Math.pow(0.3, 3),
        1 / sumWeights
      );
      
      // Test geometric mean coherence
      const geometricMean =
        Prime.coherence.systemCoherence.calculateGlobalCoherence({
          method: "geometric_mean",
        });
      expect(geometricMean).toBeCloseTo(expectedGeometric, 10);
    });

    test('should handle empty component list', () => {
      // No components registered
      const globalCoherence = Prime.coherence.systemCoherence.calculateGlobalCoherence();
      expect(globalCoherence).toBe(0);
    });
  });

  describe('Global Optimization', () => {
    test('should optimize registered components', () => {
      // Create a test object with optimization capability
      const testObj = {
        value: 10,
        norm: function() {
          return Math.abs(this.value);
        },
        optimize: function() {
          this.value = this.value * 0.5;
          return this;
        }
      };
      
      // Register component
      Prime.coherence.systemCoherence.register(testObj);
      
      // Patch the Prime.coherence.optimize method for testing
      const originalOptimize = Prime.coherence.optimize;
      Prime.coherence.optimize = function(obj, options) {
        if (obj === testObj) {
          obj.optimize();
        }
        return obj;
      };
      
      // Test initial coherence
      const initialCoherence = Prime.coherence.systemCoherence.calculateGlobalCoherence();
      expect(initialCoherence).toBeCloseTo(10, 5); // Initial norm
      
      // Optimize and test
      Prime.coherence.systemCoherence.optimizeGlobal();
      
      // Test that the object was optimized
      // The value might differ due to multiple optimization iterations
      expect(testObj.value).toBeLessThan(10); // Value should decrease from initial 10
      
      // Restore original optimize method
      Prime.coherence.optimize = originalOptimize;
    });

    test('should optimize all registered components', () => {
      // Create multiple test objects
      const testObj1 = {
        value: 10,
        norm: function() {
          return Math.abs(this.value);
        },
        optimize: function() {
          this.value = this.value * 0.5;
          return this;
        }
      };
      
      const testObj2 = {
        value: 20,
        norm: function() {
          return Math.abs(this.value);
        },
        optimize: function() {
          this.value = this.value * 0.75;
          return this;
        }
      };
      
      // Register components
      Prime.coherence.systemCoherence.register(testObj1, 1);
      Prime.coherence.systemCoherence.register(testObj2, 2);
      
      // Patch the Prime.coherence.optimize method for testing
      const originalOptimize = Prime.coherence.optimize;
      let optimizeCalls = [];
      Prime.coherence.optimize = function(obj, options) {
        optimizeCalls.push(obj);
        if (obj === testObj1) {
          obj.optimize();
        } else if (obj === testObj2) {
          obj.optimize();
        }
        return obj;
      };
      
      // Optimize and test
      Prime.coherence.systemCoherence.optimizeGlobal();
      
      // Should have optimized both components
      expect(optimizeCalls.length).toBe(20); // Default is 10 iterations for systemCoherence.optimizeGlobal
      
      // Values should decrease from initial values but exact values may vary
      expect(testObj1.value).toBeLessThan(10); // Original value was 10
      expect(testObj2.value).toBeLessThan(20); // Original value was 20
      
      // Restore original optimize method
      Prime.coherence.optimize = originalOptimize;
    });
  });
});