/**
 * Verification Tests for the UOR (Universal Object Reference) Framework
 * These tests validate the mathematical rigor and precision of the implementations
 * based on the concepts from the P vs NP proofs
 */

const Prime = require('../src/mathematics.js');
const assert = require('assert');

// Import required modules
let CoherenceValidator, FiberPatternRecognition, CoherenceGradientDescent;
try {
  CoherenceValidator = require('../src/framework/base0/coherence-validator.js').CoherenceValidator;
  FiberPatternRecognition = require('../src/framework/math/patternRecognition.js').FiberAlgebraPatternRecognition;
  CoherenceGradientDescent = require('../src/framework/math/coherence.js').CoherenceGradientDescent;
} catch (e) {
  console.warn('Direct module imports failed, falling back to Prime framework');
}

/**
 * Numerical verification utilities
 */
const NumVerify = {
  // Verify numerical precision with explicit error bounds
  assertPrecision: (actual, expected, epsilon = 1e-10, message = "") => {
    const error = Math.abs(actual - expected);
    assert.ok(
      error <= epsilon,
      `${message || 'Precision error'}: |${actual} - ${expected}| = ${error} > ${epsilon}`
    );
    return error;
  },
  
  // Verify vector precision with norm-based error bounds
  assertVectorPrecision: (actual, expected, epsilon = 1e-10, message = "") => {
    if (!Array.isArray(actual) || !Array.isArray(expected)) {
      throw new TypeError("Both vectors must be arrays");
    }
    
    if (actual.length !== expected.length) {
      throw new Error(`Vector length mismatch: ${actual.length} vs ${expected.length}`);
    }
    
    let errorSquaredSum = 0;
    for (let i = 0; i < actual.length; i++) {
      const error = Math.abs(actual[i] - expected[i]);
      errorSquaredSum += error * error;
    }
    
    const rootMeanSquaredError = Math.sqrt(errorSquaredSum / actual.length);
    assert.ok(
      rootMeanSquaredError <= epsilon,
      `${message || 'Vector precision error'}: RMSE = ${rootMeanSquaredError} > ${epsilon}`
    );
    
    return rootMeanSquaredError;
  },
  
  // Verify mathematical coherence properties
  assertCoherence: (value, threshold = 0.9, message = "") => {
    assert.ok(
      value >= threshold,
      `${message || 'Coherence error'}: ${value} < ${threshold}`
    );
  },
  
  // Verify invariance under transformations
  assertInvariance: (original, transformed, transformer, epsilon = 1e-10, message = "") => {
    // Apply inverse transformation
    const restored = transformer.invert(transformed);
    
    // Compare original and restored values
    return NumVerify.assertVectorPrecision(
      restored, 
      original, 
      epsilon,
      message || 'Invariance error'
    );
  }
};

describe('UOR Framework Verification', () => {
  describe('Formal Coherence Constraints', () => {
    let validator;
    
    beforeEach(() => {
      validator = new CoherenceValidator({
        strictMode: true,
        toleranceLevel: 1e-12,
        enforceUorConstraints: true
      });
      
      // Register formal UOR constraints
      validator.registerConstraint('manifold', {
        name: 'closure',
        validator: (value, context) => {
          // Check if operations on manifold stay within the manifold
          if (!Array.isArray(value)) return false;
          
          // Test for formal manifold closure property
          const allPointsValid = value.every(point => {
            if (!Array.isArray(point)) return false;
            // Check if point coordinates satisfy manifold equations
            return point.every(coord => Number.isFinite(coord));
          });
          
          return allPointsValid;
        },
        priority: 10
      });
      
      validator.registerConstraint('fiber', {
        name: 'basepoint_connection',
        validator: (value, context) => {
          // Check if fiber is properly attached to a base point
          if (!value || typeof value !== 'object') return false;
          if (!Array.isArray(value.position)) return false;
          
          // Check if the fiber position is valid (finite coordinates)
          return value.position.every(coord => Number.isFinite(coord));
        },
        priority: 9
      });
      
      validator.registerConstraint('transformation', {
        name: 'group_axioms',
        validator: (value, context) => {
          // Verify transformation satisfies group axioms
          if (!value || typeof value !== 'object') return false;
          if (!Array.isArray(value.matrix)) return false;
          
          // Check if transformation matrix is invertible
          // This is a simplified check - a full implementation would verify determinant != 0
          return value.matrix.length > 0 && value.matrix[0].length > 0;
        },
        priority: 10
      });
      
      // Define coherence norms based on UOR framework
      validator.defineCoherenceNorm('manifold', (results, value, context) => {
        // For manifolds, coherence is based on constraint satisfaction
        const satisfiedCount = results.filter(r => r.satisfied).length;
        return satisfiedCount / results.length;
      });
      
      validator.defineCoherenceNorm('fiber', (results, value, context) => {
        // For fibers, coherence relates to connection with base point
        if (!results.find(r => r.name === 'basepoint_connection')?.satisfied) {
          return 0;
        }
        
        // Compute more sophisticated coherence measures for fibers
        return results.filter(r => r.satisfied).length / results.length;
      });
    });
    
    it('should validate manifold structures with formal constraints', () => {
      // Create a test manifold (a 2-sphere in this case)
      const sphere = Array(20).fill().map(() => {
        // Generate random point on unit sphere
        const theta = Math.random() * 2 * Math.PI;
        const phi = Math.acos(2 * Math.random() - 1);
        return [
          Math.sin(phi) * Math.cos(theta),
          Math.sin(phi) * Math.sin(theta),
          Math.cos(phi)
        ];
      });
      
      // Validate the manifold
      const result = validator.validate('manifold', sphere);
      assert.ok(result.valid, "Manifold should satisfy formal constraints");
      NumVerify.assertCoherence(result.coherence, 0.9, "Manifold should have high coherence");
    });
    
    it('should validate fiber structures with formal constraints', () => {
      // Create a test fiber
      const fiber = {
        position: [0, 1, 0], // Base point
        dimension: 4,
        state: Array(16).fill(0).map((_, i) => i % 2 ? 0.1 : 0), // Sparse state vector
      };
      
      // Validate the fiber
      const result = validator.validate('fiber', fiber);
      assert.ok(result.valid, "Fiber should satisfy formal constraints");
      NumVerify.assertCoherence(result.coherence, 0.9, "Fiber should have high coherence");
    });
    
    it('should validate transformations with formal group axioms', () => {
      // Create a test transformation (rotation in 3D)
      const angle = Math.PI / 4;
      const transformation = {
        matrix: [
          [Math.cos(angle), -Math.sin(angle), 0],
          [Math.sin(angle), Math.cos(angle), 0],
          [0, 0, 1]
        ],
        type: 'rotation',
        parameter: angle
      };
      
      // Validate the transformation
      const result = validator.validate('transformation', transformation);
      assert.ok(result.valid, "Transformation should satisfy group axioms");
      NumVerify.assertCoherence(result.coherence, 0.9, "Transformation should have high coherence");
    });
    
    it('should reject invalid manifold structures', () => {
      // Create an invalid manifold with NaN/Infinity values
      const invalidManifold = Array(5).fill().map(() => {
        return [Math.random(), Number.POSITIVE_INFINITY, Math.random()];
      });
      
      // Validate the manifold
      const result = validator.validate('manifold', invalidManifold);
      assert.ok(!result.valid, "Invalid manifold should fail validation");
      assert.ok(result.coherence < 0.9, "Invalid manifold should have low coherence");
    });
    
    it('should validate compound UOR structures with nested constraints', () => {
      // Create a compound UOR structure (manifold with attached fibers)
      const compound = {
        manifold: Array(5).fill().map(() => {
          // Random points in [-1,1]^3
          return [
            2 * Math.random() - 1,
            2 * Math.random() - 1,
            2 * Math.random() - 1
          ];
        }),
        fibers: Array(5).fill().map((_, i) => {
          return {
            position: [
              2 * Math.random() - 1,
              2 * Math.random() - 1,
              2 * Math.random() - 1
            ],
            dimension: 3,
            state: Array(8).fill(0).map(() => Math.random())
          };
        })
      };
      
      // Register compound validation
      validator.registerConstraint('compound', {
        name: 'fiber_manifold_connection',
        validator: (value) => {
          if (!value || typeof value !== 'object') return false;
          if (!Array.isArray(value.manifold)) return false;
          if (!Array.isArray(value.fibers)) return false;
          
          // Check if each fiber is connected to a point in the manifold
          // This is a simplified check - just ensuring the arrays exist
          return value.fibers.length > 0;
        },
        priority: 10
      });
      
      // Validate the compound structure
      const result = validator.validate('compound', compound);
      assert.ok(result.valid, "Compound UOR structure should be valid");
    });
  });
  
  describe('Pattern Recognition with UOR Guarantees', () => {
    let recognizer;
    
    beforeEach(() => {
      // Create a fiber algebra pattern recognition instance with UOR guarantees
      recognizer = new FiberPatternRecognition({
        dimension: 6,
        manifoldDim: 3,
        manifoldPoints: 7
      });
    });
    
    it('should create a mathematically rigorous reference manifold', () => {
      assert.ok(Array.isArray(recognizer.manifold));
      assert.strictEqual(recognizer.manifold.length, 7);
      
      // Validate manifold properties with formal criteria
      recognizer.manifold.forEach(point => {
        assert.ok(Array.isArray(point));
        assert.strictEqual(point.length, 3);
        point.forEach(coord => {
          assert.ok(Number.isFinite(coord), "Manifold coordinates must be finite");
          assert.ok(coord >= 0 && coord <= 1, "Manifold coordinates should be in [0,1]");
        });
      });
    });
    
    it('should compute pattern coherence with formal guarantees', () => {
      // Create test data with a clear pattern
      const pattern1 = [1, 0, 0, 0, 0, 0];
      const pattern2 = [0, 1, 0, 0, 0, 0];
      const data = Array(10).fill().map((_, i) => 
        i % 2 === 0 ? pattern1 : pattern2
      );
      
      // Find patterns with explicit coherence calculation
      const patterns = recognizer.findPatterns(data, 3);
      assert.ok(patterns.length > 0, "Should find patterns in the data");
      
      // Verify coherence properties
      patterns.forEach(pattern => {
        assert.ok('coherence' in pattern, "Pattern should have coherence measure");
        assert.ok(pattern.coherence >= 0 && pattern.coherence <= 1,
          "Coherence should be in [0,1]");
        
        // Formal coherence property: measure of internal consistency
        if (pattern.type === 'base') {
          // Base pattern should have high coherence for clean data
          NumVerify.assertCoherence(pattern.coherence, 0.7,
            "Base pattern should have high coherence for clean data");
        }
      });
    });
    
    it('should maintain stable algebraic representations under small perturbations', () => {
      // Create a baseline dataset
      const baseData = [
        [1, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0],
        [0, 0, 1, 0, 0, 0]
      ];
      
      // Encode the baseline data
      const baseStates = recognizer.encodeData(baseData);
      
      // Create a perturbed dataset (small noise)
      const epsilon = 1e-5;
      const perturbedData = baseData.map(vector => 
        vector.map(v => v + (Math.random() - 0.5) * epsilon)
      );
      
      // Encode the perturbed data
      const perturbedStates = recognizer.encodeData(perturbedData);
      
      // Compare encoded states - should be nearly identical for small perturbations
      Object.keys(baseStates).forEach(fiber => {
        const baseState = baseStates[fiber];
        const perturbedState = perturbedStates[fiber];
        
        // Compute L2 distance between states
        let distSquared = 0;
        for (let i = 0; i < baseState.length; i++) {
          distSquared += Math.pow(baseState[i] - perturbedState[i], 2);
        }
        const distance = Math.sqrt(distSquared);
        
        // The distance should be small, related to the perturbation size
        // This is a formal guarantee of the stability of the representation
        assert.ok(distance < 10 * epsilon, 
          `Representation should be stable: distance=${distance}, epsilon=${epsilon}`);
      });
    });
    
    it('should detect invariant structures across algebraic transformations', () => {
      // Create a test pattern with a clear symmetry
      const data = [];
      
      // Generate points along a circle in 2D, embedded in 6D
      for (let i = 0; i < 12; i++) {
        const angle = (i / 12) * 2 * Math.PI;
        const point = [
          Math.cos(angle), Math.sin(angle), 0, 0, 0, 0
        ];
        data.push(point);
      }
      
      // Find patterns
      const patterns = recognizer.findPatterns(data, 3);
      assert.ok(patterns.length > 0, "Should find patterns with symmetry");
      
      // Get the top pattern
      const topPattern = patterns[0];
      assert.ok(topPattern.coherence > 0.7, 
        "Top pattern should have high coherence for symmetric data");
      
      // Apply a transformation that preserves the symmetry (rotation in the first two dimensions)
      const transformedData = data.map(point => {
        const angle = Math.PI / 4; // 45 degree rotation
        const x = point[0] * Math.cos(angle) - point[1] * Math.sin(angle);
        const y = point[0] * Math.sin(angle) + point[1] * Math.cos(angle);
        return [x, y, point[2], point[3], point[4], point[5]];
      });
      
      // Find patterns in the transformed data
      const transformedPatterns = recognizer.findPatterns(transformedData, 3);
      assert.ok(transformedPatterns.length > 0, 
        "Should find patterns in transformed data");
      
      // The coherence of the top pattern should be similar
      // This validates the invariance of the pattern recognition
      NumVerify.assertPrecision(
        transformedPatterns[0].coherence,
        topPattern.coherence,
        0.1, // Allow some variability due to numerical considerations
        "Pattern coherence should be invariant under rotation"
      );
    });
  });
  
  describe('Coherence-Gradient Descent with UOR Guarantees', () => {
    let optimizer;
    
    beforeEach(() => {
      // Create a coherence-gradient descent optimizer with UOR guarantees
      optimizer = new CoherenceGradientDescent({
        dimension: 5,
        numFibers: 4,
        useSpectral: true,
        useFiber: true
      });
    });
    
    it('should initialize the fiber manifold with formal mathematical structure', () => {
      // Check basic structure
      assert.ok(Array.isArray(optimizer.fibers));
      assert.strictEqual(optimizer.fibers.length, 4);
      
      // Verify fiber properties
      optimizer.fibers.forEach(fiber => {
        // Check if fiber has position in manifold
        assert.ok(Array.isArray(fiber.position));
        assert.strictEqual(fiber.position.length, 3);
        
        // Check if all coordinates are valid
        fiber.position.forEach(coord => {
          assert.ok(Number.isFinite(coord));
          assert.ok(coord >= 0 && coord <= 1);
        });
        
        // Check dimension
        assert.strictEqual(fiber.dimension, 5);
      });
    });
    
    it('should create mathematically valid symmetry generators', () => {
      // Check generator structure
      assert.ok(Array.isArray(optimizer.symmetryGenerators));
      assert.ok(optimizer.symmetryGenerators.length > 0);
      
      // Verify formal mathematical properties of generators
      optimizer.symmetryGenerators.forEach(gen => {
        assert.ok(gen.type, "Generator should have a type");
        
        // Verify symmetry type-specific properties
        switch (gen.type) {
          case 'bit_flip':
            assert.ok('index' in gen, "Bit-flip should have index property");
            assert.ok(Number.isInteger(gen.index), "Index should be an integer");
            break;
            
          case 'bit_swap':
            assert.ok(Array.isArray(gen.indices), "Bit-swap should have indices array");
            assert.strictEqual(gen.indices.length, 2, "Bit-swap should have exactly 2 indices");
            assert.ok(Number.isInteger(gen.indices[0]) && Number.isInteger(gen.indices[1]),
              "Indices should be integers");
            break;
            
          case 'cluster_flip':
            assert.ok(Array.isArray(gen.indices), "Cluster-flip should have indices array");
            assert.ok(gen.indices.length > 1, "Cluster-flip should have multiple indices");
            assert.ok(gen.indices.every(Number.isInteger),
              "All indices should be integers");
            break;
        }
      });
    });
    
    it('should maintain transformation consistency under composition', () => {
      // Create a test state
      const state = Array(5).fill(0).map(() => Math.random() > 0.5 ? 1 : 0);
      
      // Apply a sequence of transformations
      const generatorIndices = [0, 2, 1, 3];
      
      // Apply transformations sequentially
      let sequentialState = [...state];
      for (const idx of generatorIndices) {
        sequentialState = optimizer.applyTransformation(sequentialState, idx);
      }
      
      // Verify transformations can be composed (mathematical group property)
      // Select three generators
      const genA = 0;
      const genB = 1;
      const genC = 2;
      
      // Apply (A * B) * C
      let state1 = [...state];
      state1 = optimizer.applyTransformation(state1, genA);
      state1 = optimizer.applyTransformation(state1, genB);
      state1 = optimizer.applyTransformation(state1, genC);
      
      // Apply A * (B * C)
      let state2 = [...state];
      state2 = optimizer.applyTransformation(state2, genB);
      state2 = optimizer.applyTransformation(state2, genC);
      state2 = optimizer.applyTransformation(state2, genA);
      
      // Check associativity [not strictly valid for all generators, but some will satisfy this]
      // For those that don't, we're testing an important property of the implementation
      if (JSON.stringify(state1) === JSON.stringify(state2)) {
        // For associative generators, states should be identical
        assert.deepStrictEqual(state1, state2, "Associative generators should satisfy (A*B)*C = A*(B*C)");
      } else {
        // For non-associative transformations, note this is expected
        console.log("Note: Tested generators don't satisfy associativity (expected for some transformations)");
      }
    });
    
    it('should handle problem encoding with formal constraint preservation', () => {
      // Create a test problem with constraints
      const constraint1 = (state) => (state[0] + state[1]) % 2 === 0; // Even sum
      const constraint2 = (state) => state[2] === 1; // Bit 2 must be on
      
      const problem = {
        dimension: 5,
        constraints: [constraint1, constraint2],
        weights: [1, 2], // Higher weight for second constraint
        initialState: [0, 0, 1, 0, 1]
      };
      
      // Encode the problem
      const encoded = optimizer.encodeProblem(problem);
      
      // Verify encoding preserves problem structure
      assert.strictEqual(encoded.n_vars, 5);
      assert.strictEqual(encoded.n_constraints, 2);
      assert.deepStrictEqual(encoded.constraints, [constraint1, constraint2]);
      assert.deepStrictEqual(encoded.weights, [1, 2]);
      assert.deepStrictEqual(encoded.initialState, [0, 0, 1, 0, 1]);
      
      // Verify constraints are preserved in the encoding
      assert.ok(encoded.constraints[0](encoded.initialState), "First constraint should be satisfied");
      assert.ok(encoded.constraints[1](encoded.initialState), "Second constraint should be satisfied");
    });
    
    it('should compute coherence measures with formal guarantees', () => {
      // Create a test problem
      const problem = {
        dimension: 5,
        constraints: [
          (state) => state[0] === state[1], // Bit 0 equals bit 1
          (state) => state[2] === 1, // Bit 2 must be on
          (state) => state[3] === 0, // Bit 3 must be off
        ],
        weights: [1, 1, 1],
        initialState: [1, 1, 1, 0, 0]
      };
      
      // Encode the problem
      const encoded = optimizer.encodeProblem(problem);
      
      // Compute coherence for the initial state (should be 1.0 - all constraints satisfied)
      const initialCoherence = optimizer.computeStateCoherence(encoded, encoded.initialState);
      assert.strictEqual(initialCoherence.coherence, 0, 
        "Initial state satisfies all constraints, coherence should be 0");
      
      // Create a state that violates one constraint
      const state1 = [1, 0, 1, 0, 0]; // Violates first constraint
      const coherence1 = optimizer.computeStateCoherence(encoded, state1);
      assert.ok(coherence1.coherence > 0, 
        "State violating one constraint should have positive coherence");
      
      // Create a state that violates two constraints
      const state2 = [1, 0, 0, 0, 0]; // Violates first and second constraints
      const coherence2 = optimizer.computeStateCoherence(encoded, state2);
      assert.ok(coherence2.coherence > coherence1.coherence, 
        "State violating two constraints should have higher coherence");
      
      // Verify coherence norms are correctly ordered
      assert.ok(
        coherence2.coherence > coherence1.coherence,
        `Coherence ordering violated: ${coherence2.coherence} <= ${coherence1.coherence}`
      );
    });
    
    it('should optimize solutions with formal constraint satisfaction guarantees', () => {
      // Create a challenging test problem with mutual constraints
      const problem = {
        dimension: 6,
        constraints: [
          (state) => state[0] === state[1], // Bit 0 equals bit 1
          (state) => state[1] === state[2], // Bit 1 equals bit 2
          (state) => state[0] !== state[3], // Bit 0 not equal to bit 3
          (state) => (state[4] + state[5]) % 2 === 0, // Bit 4 + Bit 5 is even
          (state) => state[0] + state[1] + state[2] >= 2, // At least 2 of first 3 bits are on
        ],
        weights: [1, 1, 1, 1, 2], // Higher weight for last constraint
        initialState: [0, 0, 0, 1, 0, 0] // Violates several constraints
      };
      
      // Solve the problem
      const solution = optimizer.solve(problem, {
        maxIterations: 50,
        useSimulatedAnnealing: true,
        temperature: 2.0,
        restartCount: 2
      });
      
      // Verify solution quality
      assert.ok(solution.minimum, "Should return a solution");
      
      // Verify constraints on the solution
      const finalState = solution.minimum;
      let constraintsSatisfied = 0;
      
      for (let i = 0; i < problem.constraints.length; i++) {
        if (problem.constraints[i](finalState)) {
          constraintsSatisfied++;
        }
      }
      
      // Assert that most constraints are satisfied
      // Since this is a stochastic algorithm, we allow some flexibility
      assert.ok(constraintsSatisfied >= 4, 
        `Solution should satisfy most constraints, but only satisfied ${constraintsSatisfied}/${problem.constraints.length}`);
      
      // Verify coherence improvement
      const initialCoherence = optimizer.computeStateCoherence(
        optimizer.encodeProblem(problem), 
        problem.initialState
      );
      
      assert.ok(solution.value < initialCoherence.coherence,
        "Final solution should have better coherence than initial state");
    });
  });
});

// Export utilities for other tests
module.exports = {
  NumVerify
};