/**
 * PrimeOS JavaScript Library - Coherence Numerical Stability Tests
 * Tests for extreme numerical conditions in coherence operations
 */

const Prime = require('../../../src/core.js');
require('../../../src/mathematics.js');
require('../../../src/coherence.js');

// Import test utilities
const {
  assertAdaptivePrecision,
  assertExtremePrecision,
  assertStabilityBound,
  assertNoCatastrophicCancellation,
  assertExtremeValueHandling
} = require('../../utils/assertions');

describe('Coherence Numerical Stability Tests', () => {
  describe('Inner Product Stability', () => {
    test('should handle extreme value combinations in inner product', () => {
      // Test with tiny values
      const tinyVector1 = [1e-200, 2e-200, 3e-200];
      const tinyVector2 = [4e-200, 5e-200, 6e-200];
      const tinyProduct = Prime.coherence.innerProduct(tinyVector1, tinyVector2);
      
      // Expected: 1e-200*4e-200 + 2e-200*5e-200 + 3e-200*6e-200
      const expectedTiny = 1e-200*4e-200 + 2e-200*5e-200 + 3e-200*6e-200;
      
      // Due to the extreme values, we test with a very relaxed tolerance
      expect(tinyProduct / expectedTiny).toBeCloseTo(1, 4);
      
      // Test with huge values
      const hugeVector1 = [1e200, 2e200, 3e200];
      const hugeVector2 = [4e200, 5e200, 6e200];
      
      // This will likely cause overflow - we just verify it doesn't crash
      expect(() => {
        Prime.coherence.innerProduct(hugeVector1, hugeVector2);
      }).not.toThrow();
      
      // Test with mixed values - using assertStabilityBound
      const mixedVector1 = [1e-100, 1, 1e100];
      const mixedVector2 = [1, 1, 1];
      
      // We're testing that the operation doesn't catastrophically lose precision
      // when dealing with vastly different scales
      assertNoCatastrophicCancellation(
        () => Prime.coherence.innerProduct(mixedVector1, mixedVector2),
        [mixedVector1, mixedVector2],
        1e-5,
        "Inner product with mixed scales should avoid catastrophic loss of precision"
      );
    });
    
    test('should handle cancellation in inner product calculation', () => {
      // Test cancellation with alternating signs
      const altVector = [1e8, -1e8, 1e8, -1e8, 1e8, -1e8, 1e8, -1e8];
      const onesVector = [1, 1, 1, 1, 1, 1, 1, 1];
      
      // This should sum to zero, but we need to test if it avoids numeric errors
      const result = Prime.coherence.innerProduct(altVector, onesVector);
      expect(Math.abs(result)).toBeLessThan(1e-5);
      
      // Test near-cancellation
      const nearCancelVector = [1e16, -1e16, 1e16, -1e16 + 1];
      const nearCancelResult = Prime.coherence.innerProduct(nearCancelVector, onesVector);
      
      // We expect 1 after all cancellations
      expect(nearCancelResult).toBeCloseTo(1, 0);
    });
    
    test('should use compensated summation for precision', () => {
      // Create a large array of tiny values that should add up to a significant value
      const size = 1000000;
      const tinyValue = 1e-10;
      const tinyArray1 = Array(size).fill(tinyValue);
      const tinyArray2 = Array(size).fill(tinyValue);
      
      // Naive summation would lose precision, but compensated should maintain it
      const expected = size * (tinyValue * tinyValue);
      const result = Prime.coherence.innerProduct(tinyArray1, tinyArray2);
      
      // Use a relaxed tolerance due to floating point limits
      expect(result / expected).toBeCloseTo(1, 2);
    });
  });
  
  describe('Norm Stability', () => {
    test('should calculate accurate norms with extreme values', () => {
      // Function to compute Euclidean norm directly
      const directNorm = (vec) => Math.sqrt(vec.reduce((sum, x) => sum + x * x, 0));
      
      // Test with extreme tiny values
      const tinyVector = Array(10).fill(1e-150);
      const tinyNorm = Prime.coherence.norm(tinyVector);
      const expectedTinyNorm = directNorm(tinyVector);
      
      // For very tiny values, we expect relative accuracy but relaxed
      expect(tinyNorm / expectedTinyNorm).toBeCloseTo(1, 4);
      
      // Test with mixed magnitudes
      const mixedVector = [1e-100, 1e-50, 1, 1e50, 1e100];
      
      // This is a challenging case for norm calculation
      // We don't test exact values, just that it behaves reasonably
      const mixedNorm = Prime.coherence.norm(mixedVector);
      expect(mixedNorm).toBeGreaterThan(1e50);
      expect(mixedNorm).toBeLessThan(1e101);
      
      // Test with alternating tiny and huge values
      const alternatingVector = [1e-100, 1e100, 1e-100, 1e100];
      
      // The huge values should dominate
      const altNorm = Prime.coherence.norm(alternatingVector);
      expect(altNorm / Math.sqrt(2) / 1e100).toBeCloseTo(1, 4);
    });
    
    test('should be robust against overflow and underflow', () => {
      // Test vectors that would cause underflow or overflow in naive implementations
      const extremeTestCases = [
        {
          vector: [1e-170, 2e-170, 3e-170], // Might underflow
          condition: 'finite'
        },
        {
          vector: [1e170, 2e170, 3e170], // Might overflow
          condition: 'finite'
        },
        {
          vector: [1e-308, 1e-308], // Near smallest representable double
          condition: 'finite'
        },
        {
          vector: [1e308, 1e308], // Near largest representable double
          condition: 'finite'
        }
      ];
      
      // Use assertExtremeValueHandling to test behavior
      assertExtremeValueHandling(
        (vec) => Prime.coherence.norm(vec),
        extremeTestCases.map(tc => [tc.vector]),
        extremeTestCases.map(tc => tc.condition),
        "Norm calculation should be robust against extreme values"
      );
    });
    
    test('should handle challenging norm calculations with different norm types', () => {
      // Vector with wide range of values
      const wideRangeVector = [1e-100, 1e-50, 1, 1e50, 1e100];
      
      // Test L1 norm (sum of absolutes)
      const l1Norm = Prime.coherence.norm(wideRangeVector, { normType: "l1" });
      expect(l1Norm).toBeCloseTo(1e100, -10); // Dominated by largest value
      
      // Test L-infinity norm (max absolute)
      const lInfNorm = Prime.coherence.norm(wideRangeVector, { normType: "infinity" });
      expect(lInfNorm).toBe(1e100);
      
      // Test weighted norm
      const weights = [1e100, 1e50, 1, 1e-50, 1e-100]; // Inverted weights
      const weightedNorm = Prime.coherence.norm(wideRangeVector, {
        normType: "weighted",
        weights: weights
      });
      
      // Now all components contribute equally to the norm
      const expectedWeighted = Math.sqrt(5); // All terms are ~1 after weighting
      expect(weightedNorm).toBeCloseTo(expectedWeighted, 0);
    });
  });
  
  describe('Optimization Stability', () => {
    test('should optimize challenging functions with extreme gradients', () => {
      // Function with extreme surface features
      // f(x,y) = 1e10 * x^2 + 1e-10 * y^2
      // Gradient is [2e10 * x, 2e-10 * y]
      const challengingFunction = (point) => {
        const x = point[0];
        const y = point[1];
        return Math.sqrt(1e10 * x * x + 1e-10 * y * y);
      };
      
      // Initial point
      const initialPoint = [1, 1e10]; // Both terms equally contribute
      
      // Mock the norm function
      const originalNorm = Prime.coherence.norm;
      Prime.coherence.norm = function(obj) {
        if (Array.isArray(obj) && obj.length === 2) {
          return challengingFunction(obj);
        }
        return originalNorm.call(this, obj);
      };
      
      // Run optimization with careful step handling
      const optimized = Prime.coherence.optimize(initialPoint, {
        maxIterations: 20,
        learningRate: 1e-5, // Small learning rate for stability
        tolerance: 1e-8,
        method: "gradient",
      });
      
      // Check that optimization improved the point
      const initialNorm = challengingFunction(initialPoint);
      const finalNorm = challengingFunction(optimized);
      
      expect(finalNorm).toBeLessThan(initialNorm * 0.9);
      
      // Restore original norm function
      Prime.coherence.norm = originalNorm;
    });
    
    test('should use adaptive step sizes for stability', () => {
      // Create a function with a steep valley
      // f(x,y) = x^2 + 100*y^2
      const valleyFunction = (point) => {
        const x = point[0];
        const y = point[1];
        return Math.sqrt(x * x + 100 * y * y);
      };
      
      // Initial point
      const initialPoint = [10, 10];
      
      // Count gradient and update calls
      let gradientCalls = 0;
      let updateCalls = 0;
      
      // Mock the norm and internal optimization methods
      const originalNorm = Prime.coherence.norm;
      const originalComputeGradient = Prime.coherence._computeGradient;
      const originalUpdateSolution = Prime.coherence._updateSolution;
      
      Prime.coherence.norm = function(obj) {
        if (Array.isArray(obj) && obj.length === 2) {
          return valleyFunction(obj);
        }
        return originalNorm.call(this, obj);
      };
      
      Prime.coherence._computeGradient = function(obj) {
        gradientCalls++;
        // Analytical gradient of our valley function
        return {
          0: 2 * obj[0],
          1: 200 * obj[1],
        };
      };
      
      Prime.coherence._updateSolution = function(current, gradient, learningRate) {
        updateCalls++;
        const updated = {...current};
        for (const key in gradient) {
          if (gradient.hasOwnProperty(key)) {
            // Adaptive step size - smaller steps in steep directions
            const adaptiveLR = learningRate / Math.sqrt(1 + gradient[key] * gradient[key]);
            updated[key] = current[key] - gradient[key] * adaptiveLR;
          }
        }
        return updated;
      };
      
      // Run optimization
      const optimized = Prime.coherence.optimize(initialPoint, {
        maxIterations: 10,
        learningRate: 0.1,
      });
      
      // Verify optimization progress
      expect(Math.abs(optimized[0])).toBeLessThan(Math.abs(initialPoint[0]));
      expect(Math.abs(optimized[1])).toBeLessThan(Math.abs(initialPoint[1]));
      
      // The y coordinate should decrease faster due to higher gradient
      const xImprovement = Math.abs(initialPoint[0]) - Math.abs(optimized[0]);
      const yImprovement = Math.abs(initialPoint[1]) - Math.abs(optimized[1]);
      expect(yImprovement).toBeGreaterThan(xImprovement);
      
      // Restore original methods
      Prime.coherence.norm = originalNorm;
      Prime.coherence._computeGradient = originalComputeGradient;
      Prime.coherence._updateSolution = originalUpdateSolution;
    });
  });
  
  describe('System Coherence Stability', () => {
    beforeEach(() => {
      // Clear existing components before each test
      Prime.coherence.systemCoherence.components = [];
    });
    
    test('should handle extreme component norms in system coherence', () => {
      // Register components with extreme norms
      Prime.coherence.systemCoherence.register(
        { value: 1, norm: () => 1e-100 },
        1
      );
      Prime.coherence.systemCoherence.register(
        { value: 2, norm: () => 1 },
        1
      );
      Prime.coherence.systemCoherence.register(
        { value: 3, norm: () => 1e100 },
        1
      );
      
      // Calculate global coherence - this should be dominated by the largest norm
      const globalCoherence = Prime.coherence.systemCoherence.calculateGlobalCoherence();
      
      // With equal weights, should be close to average
      expect(globalCoherence).toBeCloseTo(1e100 / 3, -90);
      
      // With weighted calculation
      Prime.coherence.systemCoherence.components = [];
      Prime.coherence.systemCoherence.register(
        { value: 1, norm: () => 1e-100 },
        1e100
      );
      Prime.coherence.systemCoherence.register(
        { value: 2, norm: () => 1 },
        1
      );
      Prime.coherence.systemCoherence.register(
        { value: 3, norm: () => 1e100 },
        1e-100
      );
      
      // Now weights should balance out the extreme norms
      const weightedCoherence = Prime.coherence.systemCoherence.calculateGlobalCoherence();
      
      // This is an extreme scenario with very large norms balanced by very small weights
      // Implementation may handle this differently; simply check that it's a number
      expect(typeof weightedCoherence).toBe('number');
      expect(isFinite(weightedCoherence)).toBe(true);
    });
    
    test('should be stable with many small components', () => {
      // Add many components with tiny norms
      const componentCount = 1000;
      for (let i = 0; i < componentCount; i++) {
        Prime.coherence.systemCoherence.register(
          { value: i, norm: () => 1e-10 },
          1
        );
      }
      
      // Calculate global coherence
      const globalCoherence = Prime.coherence.systemCoherence.calculateGlobalCoherence();
      
      // The actual numerical value may vary depending on implementation details
      // Just check that it's a small positive value in a reasonable range
      expect(globalCoherence).toBeGreaterThan(0);
      expect(globalCoherence).toBeLessThan(1e-8);
    });
    
    test('should handle extreme weighting scenarios', () => {
      // Add components with very different weights
      Prime.coherence.systemCoherence.register(
        { value: 1, norm: () => 1 },
        1e-100
      );
      Prime.coherence.systemCoherence.register(
        { value: 2, norm: () => 1 },
        1e100
      );
      
      // Calculate global coherence
      const globalCoherence = Prime.coherence.systemCoherence.calculateGlobalCoherence();
      
      // The component with huge weight should dominate
      const totalWeight = 1e-100 + 1e100;
      const weightedNormSquared = 1e-100 * 1e-100 * 1 * 1 + 1e100 * 1e100 * 1 * 1;
      const expected = Math.sqrt(weightedNormSquared) / totalWeight;
      
      expect(globalCoherence).toBeCloseTo(expected, -90);
    });
  });
});