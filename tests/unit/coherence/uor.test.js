/**
 * PrimeOS JavaScript Library - Universal Object Reference (UOR) Unit Tests
 * Tests for UOR reference creation, object creation, and transformation
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

describe('Universal Object Reference (UOR)', () => {
  describe('Reference Creation', () => {
    test('should create a reference with manifold and fiber', () => {
      const { algebra } = createTestAlgebra();
      
      // Create reference
      const ref = Prime.UOR.createReference({
        manifold: "testManifold",
        point: [0, 0, 0],
        fiber: algebra,
      });
      
      // Test reference properties
      expect(ref.manifold).toBe("testManifold");
      expect(ref.fiber).toBe(algebra);
      expect(ref.point).toEqual([0, 0, 0]);
    });

    test('should check reference compatibility', () => {
      const { algebra } = createTestAlgebra();
      
      // Create references
      const ref1 = Prime.UOR.createReference({
        manifold: "testManifold",
        point: [0, 0, 0],
        fiber: algebra,
      });
      
      const ref2 = Prime.UOR.createReference({
        manifold: "testManifold",
        point: [1, 1, 1],
        fiber: algebra,
      });
      
      const ref3 = Prime.UOR.createReference({
        manifold: "otherManifold",
        point: [0, 0, 0],
        fiber: algebra,
      });
      
      // Test compatibility
      expect(ref1.isCompatibleWith(ref2)).toBe(true);
      expect(ref1.isCompatibleWith(ref3)).toBe(false);
    });

    test('should create related reference', () => {
      const { algebra } = createTestAlgebra();
      
      // Create a reference
      const ref1 = Prime.UOR.createReference({
        manifold: "testManifold",
        point: [0, 0, 0],
        fiber: algebra,
      });
      
      // Create a related reference
      const relatedRef = ref1.relatedReference([2, 2, 2]);
      
      // Test properties
      expect(relatedRef.manifold).toBe(ref1.manifold);
      expect(relatedRef.fiber).toBe(ref1.fiber);
      expect(relatedRef.point).toEqual([2, 2, 2]);
    });
  });

  describe('UOR Object Creation', () => {
    test('should create an object at a reference', () => {
      const { algebra, vector } = createTestAlgebra();
      
      // Create reference
      const ref = Prime.UOR.createReference({
        manifold: "testManifold",
        point: [0, 0, 0],
        fiber: algebra,
      });
      
      // Create object
      const obj = ref.createObject(vector);
      
      // Test object properties
      expect(obj.reference).toBe(ref);
      expect(obj.value).toBe(vector);
    });

    test('should create objects with different values', () => {
      const { algebra, scalar, vector } = createTestAlgebra();
      
      // Create reference
      const ref = Prime.UOR.createReference({
        manifold: "testManifold",
        point: [0, 0, 0],
        fiber: algebra,
      });
      
      // Create objects
      const obj1 = ref.createObject(scalar);
      const obj2 = ref.createObject(vector);
      
      // Test object values
      expect(obj1.value).toBe(scalar);
      expect(obj2.value).toBe(vector);
    });
  });

  describe('UOR Object Transformation', () => {
    test('should transform objects with a function', () => {
      const { algebra, vector } = createTestAlgebra();
      
      // Create reference
      const ref = Prime.UOR.createReference({
        manifold: "testManifold",
        point: [0, 0, 0],
        fiber: algebra,
      });
      
      // Create object
      const obj = ref.createObject(vector);
      
      // Transform with a function
      const transformed = obj.transform((v) => v.scale(2));
      
      // Test transformation
      expect(transformed.reference).toBe(ref);
      expect(transformed.value.norm()).toBeCloseTo(vector.scale(2).norm(), 10);
    });

    test('should calculate coherence norm', () => {
      const { algebra, vector } = createTestAlgebra();
      
      // Create reference
      const ref = Prime.UOR.createReference({
        manifold: "testManifold",
        point: [0, 0, 0],
        fiber: algebra,
      });
      
      // Create object
      const obj = ref.createObject(vector);
      
      // Test coherence norm
      const norm = obj.coherenceNorm();
      expect(norm).toBeCloseTo(vector.norm(), 10);
    });
  });

  describe('UOR Object Projection', () => {
    test('should project objects between compatible references', () => {
      const { algebra, vector } = createTestAlgebra();
      
      // Create references
      const ref1 = Prime.UOR.createReference({
        manifold: "testManifold",
        point: [0, 0, 0],
        fiber: algebra,
      });
      
      const ref2 = Prime.UOR.createReference({
        manifold: "testManifold",
        point: [1, 1, 1],
        fiber: algebra,
      });
      
      // Create object
      const obj = ref1.createObject(vector);
      
      // Project to second reference
      const projected = obj.projectTo(ref2);
      
      // Test projection
      expect(projected.reference).toBe(ref2);
      expect(projected.value).not.toBe(obj.value);
      expect(projected.value.norm()).toBeCloseTo(obj.value.norm(), 10);
    });

    test('should throw for projection to incompatible references', () => {
      const { algebra, vector } = createTestAlgebra();
      
      // Create references
      const ref1 = Prime.UOR.createReference({
        manifold: "testManifold",
        point: [0, 0, 0],
        fiber: algebra,
      });
      
      const incompatibleRef = Prime.UOR.createReference({
        manifold: "otherManifold",
        point: [0, 0, 0],
        fiber: algebra,
      });
      
      // Create object
      const obj = ref1.createObject(vector);
      
      // Test projection fails
      expect(() => {
        obj.projectTo(incompatibleRef);
      }).toThrow(Prime.InvalidOperationError);
    });
  });

  describe('UOR Fiber Bundle', () => {
    test('should create a fiber bundle', () => {
      const { algebra } = createTestAlgebra();
      
      // Create a fiber bundle
      const bundle = Prime.UOR.createFiberBundle({
        baseManifold: "testManifold",
        fiber: algebra,
      });
      
      // Test bundle properties
      expect(bundle.baseManifold).toBe("testManifold");
      expect(bundle.fiber).toBe(algebra);
    });

    test('should create a section of a fiber bundle', () => {
      const { algebra } = createTestAlgebra();
      
      // Create a fiber bundle
      const bundle = Prime.UOR.createFiberBundle({
        baseManifold: "testManifold",
        fiber: algebra,
      });
      
      // Create a section
      const section = bundle.createSection((point) => {
        // Return a vector based on the point coordinates
        return algebra.vector(point);
      });
      
      // Test section evaluation
      const point = [2, 3, 4];
      const value = section.valueAt(point);
      
      expect(Prime.UOR.isObject(value)).toBe(true);
      expect(Prime.Clifford.isMultivector(value.value)).toBe(true);
      
      // Check that section value reflects point coordinates
      const components = value.value.toArray();
      expect(components[0]).toBe(point[0]);
      expect(components[1]).toBe(point[1]);
      expect(components[2]).toBe(point[2]);
    });

    test('should perform parallel transport along a curve', () => {
      const { algebra } = createTestAlgebra();
      
      // Create a fiber bundle
      const bundle = Prime.UOR.createFiberBundle({
        baseManifold: "testManifold",
        fiber: algebra,
      });
      
      // Create a section
      const section = bundle.createSection((point) => {
        return algebra.vector(point);
      });
      
      // Define a curve
      const curve = [
        [0, 0, 0],
        [1, 1, 1],
        [2, 2, 2],
      ];
      
      // Perform parallel transport
      const transported = bundle.parallelTransport(section, curve);
      
      // Test transported section
      expect(transported.bundle).toBe(bundle);
      
      // Test transported value at end point
      const endPoint = curve[curve.length - 1];
      const endValue = transported.valueAt(endPoint);
      
      expect(Prime.UOR.isObject(endValue)).toBe(true);
      expect(Prime.Clifford.isMultivector(endValue.value)).toBe(true);
    });
  });
});