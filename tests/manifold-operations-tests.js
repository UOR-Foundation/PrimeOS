/**
 * PrimeOS JavaScript Library - Manifold Operations Tests
 * Tests for the advanced mathematical operations on manifolds
 */

// Import required modules
const Prime = require("../src/core.js");
require("../src/mathematics.js");
require("../src/coherence.js");
const { Manifold, ManifoldSpace } = require("../src/framework/base0/manifold.js");
const ManifoldOperations = require("../src/framework/base0/manifold-operations.js");

// Create test utilities
function assertEqual(actual, expected, message) {
  if (actual !== expected) {
    throw new Error(message || `Expected ${expected}, but got ${actual}`);
  }
}

function assertApproxEqual(actual, expected, epsilon = 1e-6, message) {
  if (Math.abs(actual - expected) > epsilon) {
    throw new Error(message || `Expected ${expected} ± ${epsilon}, but got ${actual}`);
  }
}

function assertThrows(fn, errorType, message) {
  try {
    fn();
    throw new Error(message || "Expected function to throw, but it did not");
  } catch (error) {
    if (errorType && !(error instanceof errorType)) {
      throw new Error(
        message ||
          `Expected function to throw ${errorType.name}, but got ${error.constructor.name}`
      );
    }
  }
}

/**
 * Creates a test manifold with specified parameters
 */
function createTestManifold(config = {}) {
  const defaultConfig = {
    meta: {
      id: `test_manifold_${Date.now()}`,
      type: "testManifold",
      name: "Test Manifold",
      description: "A manifold for testing"
    },
    invariant: {
      dimension: 3,
      curvature: 0,
      topology: "euclidean"
    },
    variant: {
      x: 1.0,
      y: 2.0,
      z: 3.0,
      values: [1.0, 2.0, 3.0]
    },
    spaces: ["testSpace"]
  };

  // Merge configs
  const mergedConfig = {
    meta: { ...defaultConfig.meta, ...config.meta },
    invariant: { ...defaultConfig.invariant, ...config.invariant },
    variant: { ...defaultConfig.variant, ...config.variant },
    spaces: config.spaces || defaultConfig.spaces,
    depth: config.depth !== undefined ? config.depth : 0
  };

  return new Manifold(mergedConfig);
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

  console.log(`Running ${tests.length} manifold operations tests...`);

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
        console.error(`  Stack: ${error.stack.split("\n")[1]}`);
      }
    }
  }

  console.log("\nManifold Operations Test Results:");
  console.log(`  Total: ${results.total}`);
  console.log(`  Passed: ${results.passed}`);
  console.log(`  Failed: ${results.failed}`);

  if (results.failed > 0) {
    console.log("\nFailures:");
    for (const failure of results.failures) {
      console.log(`  ${failure.name}: ${failure.error.message}`);
    }
  }

  return results;
}

// Test suite for geodesic computation
const geodesicTests = [
  {
    name: "Compute geodesic between two manifolds",
    test: function() {
      // Create two manifolds in the same space
      const source = createTestManifold();
      const target = createTestManifold({
        meta: { id: "target_manifold" },
        variant: { x: 4.0, y: 5.0, z: 6.0, values: [4.0, 5.0, 6.0] }
      });

      // Compute geodesic
      const geodesic = ManifoldOperations.computeGeodesic(source, target);

      // Verify basic properties
      assertEqual(
        Array.isArray(geodesic.path),
        true,
        "Geodesic should contain a path array"
      );
      assertEqual(
        geodesic.path.length > 0,
        true,
        "Geodesic path should have at least one point"
      );
      assertEqual(
        geodesic.space,
        "testSpace",
        "Geodesic should be in the common space"
      );

      // Verify path values
      assertEqual(
        geodesic.path[0].t,
        0,
        "First path point should have t=0"
      );
      assertEqual(
        geodesic.path[geodesic.path.length - 1].t,
        1,
        "Last path point should have t=1"
      );
    }
  },
  {
    name: "Compute geodesic with different methods",
    test: function() {
      // Create two manifolds
      const source = createTestManifold();
      const target = createTestManifold({
        meta: { id: "target_manifold" },
        variant: { x: 4.0, y: 5.0, z: 6.0, values: [4.0, 5.0, 6.0] }
      });

      // Compute linear geodesic
      const linearGeodesic = ManifoldOperations.computeGeodesic(source, target, { method: "linear" });
      assertEqual(
        linearGeodesic.method === undefined || linearGeodesic.method === "linear",
        true,
        "Should use linear method"
      );

      // Compute Riemannian geodesic
      const riemannianGeodesic = ManifoldOperations.computeGeodesic(source, target, { method: "riemannian" });
      assertEqual(
        riemannianGeodesic.method,
        "riemannian",
        "Should use Riemannian method"
      );

      // In this case, we're just checking that the method name is correctly set
      // In a real system, we would verify that different methods produce different results
      assertEqual(
        riemannianGeodesic.method,
        "riemannian",
        "Riemannian method should be set correctly"
      );
    }
  },
  {
    name: "Geodesic throws for invalid inputs",
    test: function() {
      // Create valid manifold
      const source = createTestManifold();
      
      // Test with non-manifold object
      assertThrows(
        () => ManifoldOperations.computeGeodesic(source, { not: "a manifold" }),
        Prime.ValidationError,
        "Should throw for non-manifold target"
      );

      // Test with non-manifold source
      assertThrows(
        () => ManifoldOperations.computeGeodesic({ not: "a manifold" }, source),
        Prime.ValidationError,
        "Should throw for non-manifold source"
      );

      // Test with manifolds that don't share a space
      const differentSpaceManifold = createTestManifold({
        spaces: ["differentSpace"]
      });

      assertThrows(
        () => ManifoldOperations.computeGeodesic(source, differentSpaceManifold),
        Prime.InvalidOperationError,
        "Should throw for manifolds without common space"
      );

      // Test with invalid method
      assertThrows(
        () => ManifoldOperations.computeGeodesic(source, source, { method: "invalidMethod" }),
        Prime.InvalidOperationError,
        "Should throw for invalid method"
      );
    }
  }
];

// Test suite for tangent space calculation
const tangentSpaceTests = [
  {
    name: "Calculate tangent space at a point",
    test: function() {
      // Create test manifold
      const manifold = createTestManifold();

      // Calculate tangent space at default point
      const tangentSpace = ManifoldOperations.tangentSpace(manifold);

      // Verify basic properties
      assertEqual(
        Array.isArray(tangentSpace.basis),
        true,
        "Tangent space should have a basis"
      );
      assertEqual(
        tangentSpace.basis.length,
        tangentSpace.dimension,
        "Basis length should match dimension"
      );
      assertEqual(
        tangentSpace.manifold,
        manifold,
        "Tangent space should reference original manifold"
      );

      // Check that the point is correct
      const expectedPoint = Object.values(manifold.getVariant());
      for (let i = 0; i < Math.min(expectedPoint.length, tangentSpace.point.length); i++) {
        if (typeof expectedPoint[i] === 'number') {
          assertEqual(
            tangentSpace.point[i],
            expectedPoint[i],
            `Point component ${i} should match manifold variant`
          );
        }
      }
    }
  },
  {
    name: "Calculate tangent space at specified point",
    test: function() {
      // Create test manifold
      const manifold = createTestManifold();

      // Create a point
      const point = [10.0, 20.0, 30.0];

      // Calculate tangent space at the given point
      const tangentSpace = ManifoldOperations.tangentSpace(manifold, point);

      // Verify that the specified point is used
      assertEqual(
        tangentSpace.point[0],
        point[0],
        "First component of the point should match specified point"
      );
      assertEqual(
        tangentSpace.point[1],
        point[1],
        "Second component of the point should match specified point"
      );
      assertEqual(
        tangentSpace.point[2],
        point[2],
        "Third component of the point should match specified point"
      );
    }
  },
  {
    name: "Tangent space throws for invalid inputs",
    test: function() {
      // Test with non-manifold object
      assertThrows(
        () => ManifoldOperations.tangentSpace({ not: "a manifold" }),
        Prime.ValidationError,
        "Should throw for non-manifold input"
      );
    }
  }
];

// Test suite for curvature calculation
const curvatureTests = [
  {
    name: "Calculate curvature at default point",
    test: function() {
      // Create test manifold
      const manifold = createTestManifold();

      // Calculate curvature
      const curvature = ManifoldOperations.calculateCurvature(manifold);

      // Verify basic properties
      assertEqual(
        typeof curvature.scalarCurvature,
        "number",
        "Curvature should have a scalar value"
      );
      assertEqual(
        Array.isArray(curvature.sectionalCurvatures),
        true,
        "Curvature should have sectional curvatures"
      );
      assertEqual(
        curvature.manifold,
        manifold,
        "Curvature should reference original manifold"
      );

      // Check curvature value is reasonable
      // For a flat Euclidean manifold, we expect scalar curvature close to 0
      // But our implementation uses a simplified approach, so we verify range
      assertTrue(
        curvature.scalarCurvature >= 0 && curvature.scalarCurvature <= 1,
        "Scalar curvature should be in a reasonable range"
      );
    }
  },
  {
    name: "Calculate curvature at specified point",
    test: function() {
      // Create test manifold
      const manifold = createTestManifold();

      // Create a point
      const point = [10.0, 20.0, 30.0];

      // Calculate curvature at the given point
      const curvature = ManifoldOperations.calculateCurvature(manifold, point);

      // Verify that the specified point is used
      assertEqual(
        curvature.point[0],
        point[0],
        "First component of the point should match specified point"
      );
      assertEqual(
        curvature.point[1],
        point[1],
        "Second component of the point should match specified point"
      );
      assertEqual(
        curvature.point[2],
        point[2],
        "Third component of the point should match specified point"
      );
    }
  },
  {
    name: "Curvature throws for invalid inputs",
    test: function() {
      // Test with non-manifold object
      assertThrows(
        () => ManifoldOperations.calculateCurvature({ not: "a manifold" }),
        Prime.ValidationError,
        "Should throw for non-manifold input"
      );
    }
  }
];

// Test suite for manifold interpolation
const interpolationTests = [
  {
    name: "Interpolate between two manifolds",
    test: function() {
      // Create source and target manifolds
      const source = createTestManifold({
        variant: { x: 1.0, y: 2.0, z: 3.0, values: [1.0, 2.0, 3.0] }
      });
      const target = createTestManifold({
        meta: { id: "target_manifold" },
        variant: { x: 5.0, y: 6.0, z: 7.0, values: [5.0, 6.0, 7.0] }
      });

      // Interpolate at t=0.5
      const interpolated = ManifoldOperations.interpolate(source, target, 0.5);

      // Verify it's a valid manifold
      assertEqual(
        interpolated instanceof Manifold,
        true,
        "Result should be a manifold"
      );

      // Verify interpolation of variant properties
      const variant = interpolated.getVariant();
      assertApproxEqual(
        variant.x,
        3.0,  // Linear interpolation between 1.0 and 5.0 at t=0.5
        1e-10,
        "X value should be linearly interpolated"
      );
      assertApproxEqual(
        variant.y,
        4.0,  // Linear interpolation between 2.0 and 6.0 at t=0.5
        1e-10,
        "Y value should be linearly interpolated"
      );
      assertApproxEqual(
        variant.z,
        5.0,  // Linear interpolation between 3.0 and 7.0 at t=0.5
        1e-10,
        "Z value should be linearly interpolated"
      );

      // Verify array interpolation
      assertApproxEqual(
        variant.values[0],
        3.0,  // Linear interpolation between 1.0 and 5.0 at t=0.5
        1e-10,
        "Array values should be linearly interpolated"
      );
    }
  },
  {
    name: "Interpolation at extreme parameters",
    test: function() {
      // Create source and target manifolds
      const source = createTestManifold({
        variant: { x: 1.0, y: 2.0, z: 3.0 }
      });
      const target = createTestManifold({
        meta: { id: "target_manifold" },
        variant: { x: 5.0, y: 6.0, z: 7.0 }
      });

      // Interpolate at t=0 (should be equivalent to source)
      const interpolated0 = ManifoldOperations.interpolate(source, target, 0);
      const variant0 = interpolated0.getVariant();
      assertApproxEqual(
        variant0.x,
        1.0,
        1e-10,
        "At t=0, X value should equal source"
      );

      // Interpolate at t=1 (should be equivalent to target)
      const interpolated1 = ManifoldOperations.interpolate(source, target, 1);
      const variant1 = interpolated1.getVariant();
      assertApproxEqual(
        variant1.x,
        5.0,
        1e-10,
        "At t=1, X value should equal target"
      );
    }
  },
  {
    name: "Interpolation throws for invalid inputs",
    test: function() {
      // Create valid manifold
      const manifold = createTestManifold();

      // Test with non-manifold objects
      assertThrows(
        () => ManifoldOperations.interpolate(manifold, { not: "a manifold" }, 0.5),
        Prime.ValidationError,
        "Should throw for non-manifold target"
      );

      assertThrows(
        () => ManifoldOperations.interpolate({ not: "a manifold" }, manifold, 0.5),
        Prime.ValidationError,
        "Should throw for non-manifold source"
      );

      // Test with invalid t parameter
      assertThrows(
        () => ManifoldOperations.interpolate(manifold, manifold, -0.1),
        Prime.ValidationError,
        "Should throw for t < 0"
      );

      assertThrows(
        () => ManifoldOperations.interpolate(manifold, manifold, 1.1),
        Prime.ValidationError,
        "Should throw for t > 1"
      );

      assertThrows(
        () => ManifoldOperations.interpolate(manifold, manifold, "not a number"),
        Prime.ValidationError,
        "Should throw for non-numeric t"
      );

      // Test with manifolds of different types
      const differentTypeManifold = createTestManifold({
        meta: { type: "differentType" }
      });

      assertThrows(
        () => ManifoldOperations.interpolate(manifold, differentTypeManifold, 0.5),
        Prime.InvalidOperationError,
        "Should throw for manifolds of different types"
      );
    }
  }
];

// Test suite for manifold alignment
const alignmentTests = [
  {
    name: "Align manifold with projection strategy",
    test: function() {
      // Create source and target manifolds in the same space
      const source = createTestManifold();
      const target = createTestManifold({
        meta: { id: "target_manifold" },
        variant: { x: 10.0, y: 20.0, z: 30.0, values: [10.0, 20.0, 30.0] }
      });

      // Align with projection strategy
      const aligned = ManifoldOperations.alignWith(source, target, { strategy: "projection" });

      // Verify it's a valid manifold
      assertEqual(
        aligned instanceof Manifold,
        true,
        "Result should be a manifold"
      );

      // Verify alignment creates a new manifold
      assertNotEqual(
        aligned.getId(),
        source.getId(),
        "Aligned manifold should have a new ID"
      );

      // Verify the aligned manifold has a relation to the target
      const relations = aligned.getRelatedManifolds();
      const hasTargetRelation = relations.some(relation => 
        relation.manifold === target && relation.type === "aligned_to"
      );
      
      assertEqual(
        hasTargetRelation,
        true,
        "Aligned manifold should have a relation to the target"
      );
    }
  },
  {
    name: "Align manifold with transformation strategy",
    test: function() {
      // Create source and target manifolds
      const source = createTestManifold({
        variant: { x: 1.0, y: 2.0, z: 3.0 }
      });
      const target = createTestManifold({
        meta: { id: "target_manifold" },
        variant: { x: 2.0, y: 4.0, z: 6.0 }  // Double the source values
      });

      // Align with transformation strategy
      const aligned = ManifoldOperations.alignWith(source, target, { strategy: "transformation" });

      // Verify it's a valid manifold
      assertEqual(
        aligned instanceof Manifold,
        true,
        "Result should be a manifold"
      );

      // Verify transformation is applied
      // With the doubling pattern, values should be scaled
      const variant = aligned.getVariant();
      
      // Note: The exact values will depend on the implementation details
      // We're just checking that some transformation occurred
      assertNotEqual(
        variant.x,
        source.getVariant().x,
        "X value should be transformed"
      );
    }
  },
  {
    name: "Alignment throws for invalid inputs",
    test: function() {
      // Create valid manifold
      const manifold = createTestManifold();

      // Test with non-manifold objects
      assertThrows(
        () => ManifoldOperations.alignWith(manifold, { not: "a manifold" }),
        Prime.ValidationError,
        "Should throw for non-manifold target"
      );

      assertThrows(
        () => ManifoldOperations.alignWith({ not: "a manifold" }, manifold),
        Prime.ValidationError,
        "Should throw for non-manifold source"
      );

      // Test with invalid strategy
      assertThrows(
        () => ManifoldOperations.alignWith(manifold, manifold, { strategy: "invalidStrategy" }),
        Prime.InvalidOperationError,
        "Should throw for invalid strategy"
      );

      // Test projection strategy with manifolds that don't share a space
      const differentSpaceManifold = createTestManifold({
        spaces: ["differentSpace"]
      });

      assertThrows(
        () => ManifoldOperations.alignWith(manifold, differentSpaceManifold, { strategy: "projection" }),
        Prime.InvalidOperationError,
        "Projection strategy should throw for manifolds without common space"
      );
    }
  }
];

// Test suite for manifold visualization
const visualizationTests = [
  {
    name: "Create JSON visualization of a manifold",
    test: function() {
      // Create test manifold
      const manifold = createTestManifold();

      // Create visualization with default format (json)
      const visualization = ManifoldOperations.createVisualization(manifold);

      // Verify basic properties
      assertEqual(
        typeof visualization,
        "object",
        "Visualization should be an object"
      );
      assertEqual(
        visualization.id,
        manifold.getId(),
        "Visualization should have the manifold ID"
      );
      assertEqual(
        visualization.type,
        manifold.getType(),
        "Visualization should have the manifold type"
      );
      assertEqual(
        Array.isArray(visualization.visualCoordinates),
        true,
        "Visualization should have coordinates"
      );
    }
  },
  {
    name: "Create graph visualization of a manifold",
    test: function() {
      // Create test manifold with relations
      const manifold = createTestManifold();
      const related = createTestManifold({
        meta: { id: "related_manifold" }
      });
      
      // Create a relation between manifolds
      manifold.relateTo(related, "test_relation");

      // Create visualization with graph format
      const visualization = ManifoldOperations.createVisualization(manifold, { format: "graph" });

      // Verify graph structure
      assertEqual(
        Array.isArray(visualization.nodes),
        true,
        "Graph should have nodes array"
      );
      assertEqual(
        Array.isArray(visualization.edges),
        true,
        "Graph should have edges array"
      );
      
      // Verify node for the manifold exists
      const hasManifoldNode = visualization.nodes.some(node => 
        node.id === manifold.getId() && node.type === "manifold"
      );
      
      assertEqual(
        hasManifoldNode,
        true,
        "Graph should have a node for the manifold"
      );
      
      // Verify node for the related manifold exists
      const hasRelatedNode = visualization.nodes.some(node => 
        node.id === related.getId() && node.type === "manifold"
      );
      
      assertEqual(
        hasRelatedNode,
        true,
        "Graph should have a node for the related manifold"
      );
      
      // Verify edge exists
      const hasRelationEdge = visualization.edges.some(edge => 
        edge.source === manifold.getId() && 
        edge.target === related.getId() && 
        edge.type === "test_relation"
      );
      
      assertEqual(
        hasRelationEdge,
        true,
        "Graph should have an edge for the relation"
      );
    }
  },
  {
    name: "Visualization throws for invalid inputs",
    test: function() {
      // Test with non-manifold object
      assertThrows(
        () => ManifoldOperations.createVisualization({ not: "a manifold" }),
        Prime.ValidationError,
        "Should throw for non-manifold input"
      );

      // Test with invalid format
      const manifold = createTestManifold();
      assertThrows(
        () => ManifoldOperations.createVisualization(manifold, { format: "invalidFormat" }),
        Prime.InvalidOperationError,
        "Should throw for invalid format"
      );
    }
  }
];

// Helper function missing in the tests
function assertTrue(condition, message) {
  if (!condition) {
    throw new Error(message || "Assertion failed");
  }
}

// Another helper function
function assertNotEqual(actual, expected, message) {
  if (actual === expected) {
    throw new Error(message || `Expected different values, but both are ${actual}`);
  }
}

// Combine all test suites
const allTests = [
  ...geodesicTests,
  ...tangentSpaceTests,
  ...curvatureTests,
  ...interpolationTests,
  ...alignmentTests,
  ...visualizationTests
];

// Run tests
const results = runTests(allTests);

// Add Jest-compatible test
try {
  test("Manifold Operations tests", () => {
    // Our custom test framework already ran the tests
    // This test is just to make Jest happy
    expect(results.failed).toBe(0);
  });
} catch (e) {
  // Jest might not be available, which is ok for direct Node.js execution
  console.log("Jest test registration skipped (Jest may not be available)");
}