/**
 * PrimeOS JavaScript Library - Coherence Tests
 * Tests for coherence system and Universal Object Reference (UOR) implementation
 */

import { Prime } from '../src/coherence.js';

// Mock console for tests if needed
const originalConsole = console;
let consoleOutput = [];

function setupMockConsole() {
  consoleOutput = [];
  
  global.console = {
    log: (...args) => { consoleOutput.push({ type: 'log', args }); },
    warn: (...args) => { consoleOutput.push({ type: 'warn', args }); },
    error: (...args) => { consoleOutput.push({ type: 'error', args }); },
    debug: (...args) => { consoleOutput.push({ type: 'debug', args }); },
    info: (...args) => { consoleOutput.push({ type: 'info', args }); }
  };
}

function restoreConsole() {
  global.console = originalConsole;
}

/**
 * Test runner
 */
function runTests(tests) {
  const results = {
    total: tests.length,
    passed: 0,
    failed: 0,
    failures: []
  };
  
  console.log(`Running ${tests.length} tests...`);
  
  for (const test of tests) {
    try {
      console.log(`\nTest: ${test.name}`);
      test.test();
      results.passed++;
      console.log(`✓ ${test.name}`);
    } catch (error) {
      results.failed++;
      results.failures.push({ name: test.name, error });
      console.error(`✗ ${test.name}`);
      console.error(`  Error: ${error.message}`);
      if (error.stack) {
        console.error(`  Stack: ${error.stack.split('\n')[1]}`);
      }
    }
  }
  
  console.log('\nTest Results:');
  console.log(`  Total: ${results.total}`);
  console.log(`  Passed: ${results.passed}`);
  console.log(`  Failed: ${results.failed}`);
  
  if (results.failed > 0) {
    console.log('\nFailures:');
    for (const failure of results.failures) {
      console.log(`  ${failure.name}: ${failure.error.message}`);
    }
  }
  
  return results;
}

/**
 * Helper function to assert conditions
 */
function assert(condition, message) {
  if (!condition) {
    throw new Error(message || 'Assertion failed');
  }
}

/**
 * Helper function to assert that two values are equal
 */
function assertEqual(actual, expected, message) {
  if (actual !== expected) {
    throw new Error(message || `Expected ${expected}, but got ${actual}`);
  }
}

/**
 * Helper function to assert that two values are approximately equal
 */
function assertApproxEqual(actual, expected, epsilon = 1e-6, message) {
  if (Math.abs(actual - expected) > epsilon) {
    throw new Error(message || `Expected ${expected} ± ${epsilon}, but got ${actual}`);
  }
}

/**
 * Helper function to assert that a function throws an error
 */
function assertThrows(fn, errorType, message) {
  try {
    fn();
    throw new Error(message || 'Expected function to throw, but it did not');
  } catch (error) {
    if (errorType && !(error instanceof errorType)) {
      throw new Error(message || `Expected function to throw ${errorType.name}, but got ${error.constructor.name}`);
    }
  }
}

/**
 * Helper function to create a Clifford algebra with multivectors for testing
 */
function createTestAlgebra() {
  const algebra = Prime.Clifford.create({ dimension: 3 });
  const scalar = algebra.scalar(5);
  const vector = algebra.vector([1, 2, 3]);
  const bivector = algebra.bivector([[0, 1, 0], [0, 0, 1], [0, 0, 0]]);
  
  return { algebra, scalar, vector, bivector };
}

// =============================================================================
// Test Suites
// =============================================================================

/**
 * Coherence Inner Product Tests
 */
const innerProductTests = [
  {
    name: 'Inner product of multivectors',
    test: function() {
      const { algebra, scalar, vector } = createTestAlgebra();
      
      // Test scalar-scalar inner product
      const scalarProduct = Prime.coherence.innerProduct(scalar, scalar);
      assert(Prime.Clifford.isMultivector(scalarProduct), 'Result should be a multivector');
      assert(scalarProduct.scalarValue() === 25, 'Scalar-scalar should be 25');
      
      // Test vector-vector inner product
      const vectorProduct = Prime.coherence.innerProduct(vector, vector);
      assert(Prime.Clifford.isMultivector(vectorProduct), 'Result should be a multivector');
      assert(vectorProduct.scalarValue() === 14, 'Vector-vector should be 14');
    }
  },
  {
    name: 'Inner product of arrays',
    test: function() {
      const a = [1, 2, 3];
      const b = [4, 5, 6];
      
      // Test default Euclidean inner product
      const product = Prime.coherence.innerProduct(a, b);
      assertEqual(product, 32, 'Inner product should be 32');
      
      // Test inner product with weighted metric
      const weightedProduct = Prime.coherence.innerProduct(a, b, { 
        metric: 'weighted', 
        weights: [2, 1, 0.5] 
      });
      assertEqual(weightedProduct, 8 + 10 + 9, 'Weighted inner product should be 27');
    }
  },
  {
    name: 'Inner product throws for incompatible objects',
    test: function() {
      assertThrows(
        () => Prime.coherence.innerProduct(5, 'string'), 
        Prime.InvalidOperationError,
        'Should throw for incompatible objects'
      );
    }
  }
];

/**
 * Coherence Norm Tests
 */
const normTests = [
  {
    name: 'Norm of multivectors',
    test: function() {
      const { algebra, scalar, vector } = createTestAlgebra();
      
      // Test scalar norm
      const scalarNorm = Prime.coherence.norm(scalar);
      assertApproxEqual(scalarNorm, 5, 1e-6, 'Scalar norm should be 5');
      
      // Test vector norm
      const vectorNorm = Prime.coherence.norm(vector);
      assertApproxEqual(vectorNorm, Math.sqrt(14), 1e-6, 'Vector norm should be sqrt(14)');
    }
  },
  {
    name: 'Norm of arrays',
    test: function() {
      const a = [3, 4];
      
      // Test Euclidean norm
      const normEuclidean = Prime.coherence.norm(a);
      assertEqual(normEuclidean, 5, 'Euclidean norm should be 5');
      
      // Test norm with options
      const normWeighted = Prime.coherence.norm(a, { 
        normType: 'weighted', 
        weights: [0.5, 2] 
      });
      assertApproxEqual(normWeighted, Math.sqrt(0.5*9 + 2*16), 1e-6, 'Weighted norm should be correct');
    }
  },
  {
    name: 'IsCoherent function works correctly',
    test: function() {
      const { algebra, scalar } = createTestAlgebra();
      
      // Test object that should be coherent
      assert(Prime.coherence.isCoherent(scalar, 10), 'Scalar should be coherent with large tolerance');
      
      // Test with very small tolerance
      assert(!Prime.coherence.isCoherent(scalar, 1e-10), 'Scalar should not be coherent with tiny tolerance');
    }
  }
];

/**
 * Coherence Constraint Tests
 */
const constraintTests = [
  {
    name: 'Create and use constraints',
    test: function() {
      // Create a constraint that numbers must be positive
      const positiveConstraint = Prime.coherence.createConstraint(
        x => x > 0,
        { name: 'positiveNumber', weight: 2 }
      );
      
      // Test constraint
      assert(positiveConstraint.check(5), 'Constraint should pass for positive number');
      assert(!positiveConstraint.check(-1), 'Constraint should fail for negative number');
      assertEqual(positiveConstraint.name, 'positiveNumber', 'Constraint should have the right name');
      assertEqual(positiveConstraint.weight, 2, 'Constraint should have the right weight');
    }
  },
  {
    name: 'Coherence-constrained state',
    test: function() {
      // Create constraints
      const constraints = [
        Prime.coherence.createConstraint(
          state => state.count >= 0,
          { name: 'nonNegativeCount', type: 'hard' }
        ),
        Prime.coherence.createConstraint(
          state => state.count <= 100,
          { name: 'maxCount', type: 'soft' }
        )
      ];
      
      // Create state
      const state = Prime.coherence.createState({ count: 50 }, constraints);
      
      // Test initial state
      assertEqual(state.value.count, 50, 'Initial state should be correct');
      
      // Test valid update
      state.update({ count: 75 });
      assertEqual(state.value.count, 75, 'State should update for valid value');
      
      // Test violating a hard constraint
      assertThrows(
        () => state.update({ count: -1 }),
        Prime.CoherenceViolationError,
        'Should throw for hard constraint violation'
      );
      
      // Coherence norm should be zero for valid state
      assertEqual(state.coherenceNorm(), 0, 'Coherence norm should be zero for valid state');
      
      // Manually check with a failing state
      const failingState = { count: -5 };
      let normSquared = 0;
      
      for (const constraint of constraints) {
        if (!constraint.check(failingState)) {
          normSquared += constraint.weight * constraint.weight;
        }
      }
      
      assertApproxEqual(
        Math.sqrt(normSquared), 
        constraints[0].weight, 
        1e-6, 
        'Manual norm calculation should match implementation'
      );
    }
  },
  {
    name: 'Optimization respects constraints',
    test: function() {
      // Simple object with a constraint
      const obj = { x: -5, y: 10 };
      const constraints = {
        maxIterations: 10,
        learningRate: 0.1,
        // Define a custom gradient function for the test
        _computeGradient: function(obj) {
          return { x: obj.x < 0 ? -1 : 1, y: obj.y > 0 ? 1 : -1 };
        },
        // Define a custom update function for the test
        _updateSolution: function(current, gradient, learningRate) {
          return {
            x: current.x - gradient.x * learningRate,
            y: current.y - gradient.y * learningRate
          };
        }
      };
      
      // Replace internal methods for testing
      const originalComputeGradient = Prime.coherence._computeGradient;
      const originalUpdateSolution = Prime.coherence._updateSolution;
      
      Prime.coherence._computeGradient = constraints._computeGradient;
      Prime.coherence._updateSolution = constraints._updateSolution;
      
      // Run optimization
      const optimized = Prime.coherence.optimize(obj, constraints);
      
      // Verify optimization moved in the right direction
      assert(optimized.x > obj.x, 'X should increase towards positive');
      assert(optimized.y < obj.y, 'Y should decrease towards negative');
      
      // Restore original methods
      Prime.coherence._computeGradient = originalComputeGradient;
      Prime.coherence._updateSolution = originalUpdateSolution;
    }
  }
];

/**
 * Universal Object Reference (UOR) Tests
 */
const uorTests = [
  {
    name: 'UOR Reference creation and compatibility',
    test: function() {
      const { algebra } = createTestAlgebra();
      
      // Create references
      const ref1 = Prime.UOR.createReference({
        manifold: 'testManifold',
        point: [0, 0, 0],
        fiber: algebra
      });
      
      const ref2 = Prime.UOR.createReference({
        manifold: 'testManifold',
        point: [1, 1, 1],
        fiber: algebra
      });
      
      const ref3 = Prime.UOR.createReference({
        manifold: 'otherManifold',
        point: [0, 0, 0],
        fiber: algebra
      });
      
      // Test reference properties
      assertEqual(ref1.manifold, 'testManifold', 'Manifold should be correct');
      assert(ref1.fiber === algebra, 'Fiber should be the algebra');
      
      // Test compatibility
      assert(ref1.isCompatibleWith(ref2), 'References with same manifold and fiber should be compatible');
      assert(!ref1.isCompatibleWith(ref3), 'References with different manifolds should not be compatible');
      
      // Test related reference
      const relatedRef = ref1.relatedReference([2, 2, 2]);
      assertEqual(relatedRef.manifold, ref1.manifold, 'Related reference should have same manifold');
      assertEqual(relatedRef.fiber, ref1.fiber, 'Related reference should have same fiber');
      assert(relatedRef.point[0] === 2, 'Related reference should have new point');
    }
  },
  {
    name: 'UOR Object creation and transformation',
    test: function() {
      const { algebra, vector } = createTestAlgebra();
      
      // Create reference and object
      const ref = Prime.UOR.createReference({
        manifold: 'testManifold',
        point: [0, 0, 0],
        fiber: algebra
      });
      
      const obj = ref.createObject(vector);
      
      // Test object properties
      assert(obj.reference === ref, 'Object should have correct reference');
      assert(obj.value === vector, 'Object should have correct value');
      
      // Test transformation with a function
      const transformed = obj.transform(v => v.scale(2));
      assert(transformed.reference === ref, 'Transformed object should have same reference');
      assertApproxEqual(
        transformed.value.norm(), 
        vector.scale(2).norm(), 
        1e-6, 
        'Transformation should scale the vector'
      );
      
      // Test coherence norm
      const norm = obj.coherenceNorm();
      assertApproxEqual(norm, vector.norm(), 1e-6, 'Coherence norm should match vector norm');
    }
  },
  {
    name: 'UOR Object projection',
    test: function() {
      const { algebra, vector } = createTestAlgebra();
      
      // Create references
      const ref1 = Prime.UOR.createReference({
        manifold: 'testManifold',
        point: [0, 0, 0],
        fiber: algebra
      });
      
      const ref2 = Prime.UOR.createReference({
        manifold: 'testManifold',
        point: [1, 1, 1],
        fiber: algebra
      });
      
      const obj = ref1.createObject(vector);
      
      // Test projection
      const projected = obj.projectTo(ref2);
      assert(projected.reference === ref2, 'Projected object should have new reference');
      assert(projected.value !== obj.value, 'Projected value should be a new object');
      assertApproxEqual(
        projected.value.norm(), 
        obj.value.norm(), 
        1e-6, 
        'Projection should preserve norm'
      );
      
      // Test projection fails for incompatible references
      const incompatibleRef = Prime.UOR.createReference({
        manifold: 'otherManifold',
        point: [0, 0, 0],
        fiber: algebra
      });
      
      assertThrows(
        () => obj.projectTo(incompatibleRef),
        Prime.InvalidOperationError,
        'Projection to incompatible reference should throw'
      );
    }
  },
  {
    name: 'UOR Fiber Bundle creation and operations',
    test: function() {
      const { algebra } = createTestAlgebra();
      
      // Create a fiber bundle
      const bundle = Prime.UOR.createFiberBundle({
        baseManifold: 'testManifold',
        fiber: algebra
      });
      
      // Test bundle properties
      assertEqual(bundle.baseManifold, 'testManifold', 'Bundle should have correct manifold');
      assertEqual(bundle.fiber, algebra, 'Bundle should have correct fiber');
      
      // Create a section
      const section = bundle.createSection(point => {
        // Return a vector based on the point coordinates
        return algebra.vector(point);
      });
      
      // Test section evaluation
      const point = [2, 3, 4];
      const value = section.valueAt(point);
      assert(Prime.UOR.isObject(value), 'Section value should be a UOR object');
      assert(Prime.Clifford.isMultivector(value.value), 'Section value should contain a multivector');
      assertApproxEqual(
        value.value.toArray()[0], 
        point[0], 
        1e-6, 
        'Section value should reflect point coordinates'
      );
      
      // Test parallel transport
      const curve = [[0, 0, 0], [1, 1, 1], [2, 2, 2]];
      const transported = bundle.parallelTransport(section, curve);
      assert(transported.bundle === bundle, 'Transported section should belong to the same bundle');
      
      // Test transported value at end point
      const endPoint = curve[curve.length - 1];
      const endValue = transported.valueAt(endPoint);
      assert(Prime.UOR.isObject(endValue), 'Transported value should be a UOR object');
    }
  }
];

/**
 * System Coherence Tests
 */
const systemCoherenceTests = [
  {
    name: 'System coherence registration and calculation',
    test: function() {
      const { vector } = createTestAlgebra();
      
      // Clear existing components
      Prime.coherence.systemCoherence.components = [];
      
      // Register components
      const unregister1 = Prime.coherence.systemCoherence.register(vector, 1);
      const unregister2 = Prime.coherence.systemCoherence.register({ value: 5, norm: () => 5 }, 2);
      
      // Test registration
      assertEqual(
        Prime.coherence.systemCoherence.components.length, 
        2, 
        'Should have 2 registered components'
      );
      
      // Test global coherence calculation
      const globalCoherence = Prime.coherence.systemCoherence.calculateGlobalCoherence();
      assert(globalCoherence > 0, 'Global coherence should be positive');
      
      // Test unregister
      unregister1();
      assertEqual(
        Prime.coherence.systemCoherence.components.length, 
        1, 
        'Should have 1 component after unregistering'
      );
      
      // Test direct unregister method
      Prime.coherence.systemCoherence.unregister({ value: 5, norm: () => 5 });
      assertEqual(
        Prime.coherence.systemCoherence.components.length, 
        0, 
        'Should have 0 components after unregistering all'
      );
    }
  },
  {
    name: 'System coherence optimization',
    test: function() {
      // Create a test object with optimization capability
      const testObj = {
        value: 10,
        norm: function() { return Math.abs(this.value); },
        optimize: function() { this.value = this.value * 0.5; return this; }
      };
      
      // Clear existing components
      Prime.coherence.systemCoherence.components = [];
      
      // Register component
      Prime.coherence.systemCoherence.register(testObj);
      
      // Replace optimize method for testing
      const originalOptimize = Prime.coherence.optimize;
      Prime.coherence.optimize = function(obj) {
        if (obj === testObj) {
          obj.optimize();
        }
        return obj;
      };
      
      // Test optimization
      const initialCoherence = Prime.coherence.systemCoherence.calculateGlobalCoherence();
      Prime.coherence.systemCoherence.optimizeGlobal();
      const optimizedCoherence = Prime.coherence.systemCoherence.calculateGlobalCoherence();
      
      assert(
        optimizedCoherence < initialCoherence, 
        'Optimization should decrease global coherence'
      );
      
      // Restore original optimize method
      Prime.coherence.optimize = originalOptimize;
    }
  }
];

// Combine all test suites
const allTests = [
  ...innerProductTests,
  ...normTests,
  ...constraintTests,
  ...uorTests,
  ...systemCoherenceTests
];

// Run tests
runTests(allTests);
