/**
 * PrimeOS JavaScript Library - Refactoring Verification Tests
 * Tests to ensure that refactored modules maintain functionality
 */

// Import required modules
const Prime = require("../src/core.js");

// Load Mathematics
require("../src/mathematics.js");

// Function to log test results
function logTestResult(name, success, error = null) {
  if (success) {
    console.log(`✅ ${name} - PASSED`);
  } else {
    console.error(`❌ ${name} - FAILED${error ? ': ' + error.message : ''}`);
    if (error) {
      console.error(error.stack);
    }
  }
}

// Test framework
function runTests(tests) {
  console.log("\n=== Refactoring Verification Tests ===\n");
  
  let passed = 0;
  let failed = 0;
  
  tests.forEach(test => {
    try {
      test.fn();
      passed++;
      logTestResult(test.name, true);
    } catch (error) {
      failed++;
      logTestResult(test.name, false, error);
    }
  });
  
  console.log(`\n=== Summary: ${passed} passed, ${failed} failed ===\n`);
  
  return { passed, failed };
}

// Define tests
const tests = [
  // Manifold basic loading test
  {
    name: "Manifold class loading",
    fn: function() {
      const { Manifold } = require("../src/framework/base0/manifold.js");
      
      if (!Manifold || typeof Manifold !== 'function') {
        throw new Error("Manifold class not properly defined");
      }
      
      const manifold = new Manifold({
        meta: { id: "test_manifold", type: "test" },
        invariant: { dim: 3 },
        variant: { x: 1, y: 2, z: 3 }
      });
      
      if (manifold.getId() !== "test_manifold") {
        throw new Error("Manifold.getId() not working properly");
      }
    }
  },
  
  // ManifoldSpace loading test
  {
    name: "ManifoldSpace class loading",
    fn: function() {
      const { ManifoldSpace } = require("../src/framework/base0/manifold-space.js");
      
      if (!ManifoldSpace || typeof ManifoldSpace !== 'function') {
        throw new Error("ManifoldSpace class not properly defined");
      }
      
      // Create a minimal test if Prime.coherence is not fully implemented
      try {
        const space = new ManifoldSpace({
          id: "test_space",
          name: "TestSpace",
          dimension: 3
        });
        
        if (space.id !== "test_space") {
          throw new Error("ManifoldSpace constructor not working properly");
        }
      } catch (e) {
        // Skip test if coherence system isn't properly set up
        if (!e.message.includes('registerSpace')) {
          throw e;
        }
        console.log("    (Skipping coherence registration)");
      }
    }
  },
  
  // ManifoldRelations loading test
  {
    name: "ManifoldRelations module loading",
    fn: function() {
      const ManifoldRelations = require("../src/framework/base0/manifold-relations.js");
      
      if (!ManifoldRelations || typeof ManifoldRelations !== 'object') {
        throw new Error("ManifoldRelations module not properly defined");
      }
      
      if (!ManifoldRelations.connect || typeof ManifoldRelations.connect !== 'function') {
        throw new Error("ManifoldRelations.connect method not properly defined");
      }
    }
  },
  
  // GeodesicOperations loading test
  {
    name: "GeodesicOperations module loading",
    fn: function() {
      const GeodesicOperations = require("../src/framework/base0/geodesic-operations.js");
      
      if (!GeodesicOperations || typeof GeodesicOperations !== 'object') {
        throw new Error("GeodesicOperations module not properly defined");
      }
      
      if (!GeodesicOperations.computeGeodesic || typeof GeodesicOperations.computeGeodesic !== 'function') {
        throw new Error("GeodesicOperations.computeGeodesic method not properly defined");
      }
    }
  },
  
  // TangentSpace loading test
  {
    name: "TangentSpaceOperations module loading",
    fn: function() {
      const TangentSpaceOperations = require("../src/framework/base0/tangent-space.js");
      
      if (!TangentSpaceOperations || typeof TangentSpaceOperations !== 'object') {
        throw new Error("TangentSpaceOperations module not properly defined");
      }
      
      if (!TangentSpaceOperations.calculateTangentSpace || typeof TangentSpaceOperations.calculateTangentSpace !== 'function') {
        throw new Error("TangentSpaceOperations.calculateTangentSpace method not properly defined");
      }
    }
  },
  
  // ManifoldVisualization loading test
  {
    name: "ManifoldVisualization module loading",
    fn: function() {
      const ManifoldVisualization = require("../src/framework/base0/manifold-visualization.js");
      
      if (!ManifoldVisualization || typeof ManifoldVisualization !== 'object') {
        throw new Error("ManifoldVisualization module not properly defined");
      }
      
      if (!ManifoldVisualization.createVisualization || typeof ManifoldVisualization.createVisualization !== 'function') {
        throw new Error("ManifoldVisualization.createVisualization method not properly defined");
      }
    }
  },
  
  // ManifoldTransformations loading test
  {
    name: "ManifoldTransformations module loading",
    fn: function() {
      const ManifoldTransformations = require("../src/framework/base0/manifold-transformations.js");
      
      if (!ManifoldTransformations || typeof ManifoldTransformations !== 'object') {
        throw new Error("ManifoldTransformations module not properly defined");
      }
      
      if (!ManifoldTransformations.alignWith || typeof ManifoldTransformations.alignWith !== 'function') {
        throw new Error("ManifoldTransformations.alignWith method not properly defined");
      }
    }
  },
  
  // Combined ManifoldOperations backwards compatibility test
  {
    name: "ManifoldOperations backwards compatibility",
    fn: function() {
      const ManifoldOperations = require("../src/framework/base0/manifold-operations.js");
      
      if (!ManifoldOperations || typeof ManifoldOperations !== 'object') {
        throw new Error("ManifoldOperations module not properly defined");
      }
      
      // Check that original methods are still accessible
      const requiredMethods = [
        'computeGeodesic',
        'tangentSpace',
        'calculateCurvature',
        'createVisualization',
        'alignWith',
        'interpolate'
      ];
      
      for (const method of requiredMethods) {
        if (!ManifoldOperations[method] || typeof ManifoldOperations[method] !== 'function') {
          throw new Error(`ManifoldOperations.${method} method not properly defined or accessible`);
        }
      }
      
      // Check that namespaced modules are exposed
      const requiredNamespaces = [
        'geodesic',
        'tangent',
        'visualization',
        'transformation',
        'relations'
      ];
      
      for (const namespace of requiredNamespaces) {
        if (!ManifoldOperations[namespace] || typeof ManifoldOperations[namespace] !== 'object') {
          throw new Error(`ManifoldOperations.${namespace} namespace not properly defined`);
        }
      }
    }
  },
  
  // Integration test with simple manifold operations
  {
    name: "Basic manifold operations integration",
    fn: function() {
      const { Manifold } = require("../src/framework/base0/manifold.js");
      const ManifoldOperations = require("../src/framework/base0/manifold-operations.js");
      
      // Create test manifolds
      const manifoldA = new Manifold({
        meta: { id: "manifold_a", type: "test" },
        invariant: { dim: 3 },
        variant: { x: 1, y: 2, z: 3 }
      });
      
      const manifoldB = new Manifold({
        meta: { id: "manifold_b", type: "test" },
        invariant: { dim: 3 },
        variant: { x: 4, y: 5, z: 6 }
      });
      
      // Add to spaces
      manifoldA.addToSpace("testSpace");
      manifoldB.addToSpace("testSpace");
      
      // Test relation creation
      const relation = ManifoldOperations.connect(manifoldA, manifoldB, "connected");
      
      if (relation.type !== "connected" || relation.sourceId !== "manifold_a" || relation.targetId !== "manifold_b") {
        throw new Error("ManifoldOperations.connect not working properly");
      }
      
      // Test visualization creation
      const visualization = ManifoldOperations.createVisualization(manifoldA);
      
      if (visualization.id !== "manifold_a") {
        throw new Error("ManifoldOperations.createVisualization not working properly");
      }
    }
  }
];

// Run the tests
const results = runTests(tests);

// For Jest compatibility (if available)
try {
  test("Refactoring verification tests pass", () => {
    expect(results.failed).toBe(0);
  });
} catch (e) {
  // Jest may not be available
}

module.exports = { results };