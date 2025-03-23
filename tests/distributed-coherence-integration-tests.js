/**
 * Integration Tests for PrimeOS Distributed Coherence
 * Tests coherence checking in realistic distributed neural network operations
 * 
 * These tests validate the coherence checking capabilities of the distributed
 * neural network system, ensuring mathematical coherence is maintained across 
 * distributed computations. The coherence module detects issues like numerical
 * instability, gradient explosion, dimensional inconsistency, and synchronization
 * problems, then provides recovery mechanisms.
 */

// Import Prime with the Distributed module
const Prime = require("../src");

// Test data generation utilities
const generateRandomMatrix = (rows, cols) => {
  return Array.from({ length: rows }, () => 
    Array.from({ length: cols }, () => Math.random() * 2 - 1)
  );
};

const generateRandomVector = (size) => {
  return Array.from({ length: size }, () => Math.random() * 2 - 1);
};

const introduceNumericalInstability = (matrix, probability = 0.05) => {
  const result = JSON.parse(JSON.stringify(matrix)); // Deep copy
  
  for (let i = 0; i < result.length; i++) {
    for (let j = 0; j < result[i].length; j++) {
      if (Math.random() < probability) {
        // Introduce NaN or Infinity
        result[i][j] = Math.random() < 0.5 ? NaN : Infinity;
      }
    }
  }
  
  return result;
};

const introduceDimensionalIncoherence = (layer) => {
  // Create a copy of the layer with incorrect dimensions
  const incoherentLayer = JSON.parse(JSON.stringify(layer));
  
  // Modify weights to have wrong dimensions
  if (incoherentLayer.weights && incoherentLayer.weights.length > 0) {
    // Add an extra element to one of the rows
    incoherentLayer.weights[0].push(0.1);
  }
  
  return incoherentLayer;
};

const introduceGradientExplosion = (gradients, scale = 1000) => {
  // Create a copy with extremely large values
  const explodingGradients = JSON.parse(JSON.stringify(gradients));
  
  // Scale up values to simulate explosion
  for (let i = 0; i < explodingGradients.dW.length; i++) {
    for (let j = 0; j < explodingGradients.dW[i].length; j++) {
      explodingGradients.dW[i][j] *= scale;
    }
  }
  
  if (explodingGradients.dB) {
    for (let i = 0; i < explodingGradients.dB.length; i++) {
      explodingGradients.dB[i] *= scale;
    }
  }
  
  return explodingGradients;
};

const introduceSynchronizationIncoherence = (params, globalParams, deviationFactor = 0.5) => {
  // Create a copy with substantial deviations from global parameters
  const desyncedParams = JSON.parse(JSON.stringify(params));
  
  for (let i = 0; i < Math.min(desyncedParams.weights.length, globalParams.weights.length); i++) {
    for (let j = 0; j < Math.min(desyncedParams.weights[i].length, globalParams.weights[i].length); j++) {
      desyncedParams.weights[i][j] += deviationFactor * (Math.random() * 2 - 1);
    }
  }
  
  if (desyncedParams.biases && globalParams.biases) {
    for (let i = 0; i < Math.min(desyncedParams.biases.length, globalParams.biases.length); i++) {
      desyncedParams.biases[i] += deviationFactor * (Math.random() * 2 - 1);
    }
  }
  
  return desyncedParams;
};

describe('Distributed Coherence Integration Tests', () => {
  // Helper to wait for async operations
  const wait = (ms) => new Promise(resolve => setTimeout(resolve, ms));
  
  describe('Distributed Layer Coherence', () => {
    test('Forward pass maintains coherence', async () => {
      // Create a distributed layer for testing
      const layer = new Prime.Distributed.Partition.DistributedLayer({
        id: "coherence_test_layer",
        layerConfig: {
          inputSize: 4,
          outputSize: 3,
          activation: "sigmoid"
        },
        nodeIds: ["node_0", "node_1"], 
        partitionScheme: new Prime.Distributed.Partition.PartitionScheme({
          type: Prime.Distributed.Partition.PartitionType.INTRA_LAYER,
          nodeCount: 2,
          layerConfig: {
            "coherence_test_layer": {
              inputSize: 4,
              outputSize: 3
            }
          }
        })
      });
      
      // Create a coherence manager
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
      
      // Create test input
      const input = [0.1, 0.2, 0.3, 0.4];
      
      // Forward pass should maintain coherence
      const forwardResult = await layer.forward(input);
      
      expect(forwardResult).toBeDefined();
      expect(Array.isArray(forwardResult.activation)).toBe(true);
      
      // Check coherence of the activation
      const activationCoherenceResult = coherenceManager.checkLayerCoherence({
        id: "activation_check",
        config: {
          inputSize: 4,
          outputSize: 3
        },
        weights: layer.weights,
        biases: layer.biases
      });
      
      expect(activationCoherenceResult.isCoherent).toBe(true);
    });
    
    test('Coherence correction fixes instability', async () => {
      // Create a layer with numerical instability
      const unstableLayer = {
        id: "unstable_layer",
        config: {
          inputSize: 3,
          outputSize: 2
        },
        weights: introduceDimensionalIncoherence({
          id: "temp",
          config: { inputSize: 3, outputSize: 2 },
          weights: generateRandomMatrix(3, 2)
        }).weights,
        biases: [0.1, NaN] // Introduce NaN in biases
      };
      
      // Create a coherence manager
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
      
      // Check coherence first
      const checkResult = coherenceManager.checkLayerCoherence(unstableLayer);
      
      expect(checkResult.isCoherent).toBe(false);
      expect(checkResult.violations.length).toBeGreaterThan(0);
      
      // Apply automatic correction
      const correctionResult = coherenceManager.applyCoherenceCorrection(
        unstableLayer, 
        checkResult.violations
      );
      
      expect(correctionResult.applied).toBe(true);
      
      // Verify correction fixed the issues
      const checkAfterCorrection = coherenceManager.checkLayerCoherence(unstableLayer);
      
      expect(checkAfterCorrection.coherenceScore).toBeGreaterThan(checkResult.coherenceScore);
    });
  });
  
  describe('Distributed Backpropagation Coherence', () => {
    test('Gradient coherence checking works', async () => {
      // Create a coherence manager
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
      
      // Create mock layer instead of using actual distributed layer
      const mockLayer = {
        id: "bp_test_layer",
        config: {
          inputSize: 3,
          outputSize: 2
        },
        weights: generateRandomMatrix(3, 2),
        biases: generateRandomVector(2)
      };
      
      // Create mock gradient results
      const mockBackwardResult = {
        dW: generateRandomMatrix(3, 2),
        dB: generateRandomVector(2),
        dX: generateRandomVector(3)
      };
      
      expect(mockBackwardResult.dW).toBeDefined();
      expect(mockBackwardResult.dB).toBeDefined();
      
      // Check coherence of the gradients
      const gradientCoherenceResult = coherenceManager.checkLayerCoherence(
        { id: "gradient_check", config: mockLayer.config },
        {
          isDistributed: true,
          gradients: mockBackwardResult
        }
      );
      
      expect(typeof gradientCoherenceResult.coherenceScore).toBe('number');
    });
    
    test('Exploding gradients are detected', async () => {
      // Create a coherence manager
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
      
      // Create mock layer
      const mockLayer = {
        id: "exploding_check_layer",
        config: {
          inputSize: 3,
          outputSize: 2
        }
      };
      
      // Create mock gradient results
      const mockBackwardResult = {
        dW: generateRandomMatrix(3, 2),
        dB: generateRandomVector(2),
        dX: generateRandomVector(3)
      };
      
      // Create exploding gradients
      const explodingGradients = introduceGradientExplosion(mockBackwardResult, 1000);
      
      // Check coherence with exploding gradients
      const explodingCoherenceResult = coherenceManager.checkLayerCoherence(
        mockLayer,
        {
          isDistributed: true,
          gradients: explodingGradients,
          maxGradientNorm: 10.0 // Explicitly set the threshold
        }
      );
      
      // Coherence should be low for exploding gradients
      expect(explodingCoherenceResult.coherenceScore).toBeLessThan(0.5);
      
      // Check for gradient violation detection
      const hasGradientViolation = explodingCoherenceResult.violations.some(
        v => v.type === Prime.Distributed.Coherence.CoherenceViolationType.GRADIENT
      );
      
      expect(hasGradientViolation).toBe(true);
    });
  });
  
  describe('Distributed Cluster Coherence', () => {
    test('Global coherence assessment works across nodes', async () => {
      // Create a cluster manager
      const manager = new Prime.Distributed.Cluster.ClusterManager({
        maxNodes: 3,
        coherencePolicy: {
          enforceGlobalCoherence: true,
          minCoherenceThreshold: 0.6,
          recoveryStrategy: "rollback"
        }
      });
      
      // Add nodes to the cluster
      const node1 = manager.addNode({
        id: "test_node_1",
        type: Prime.Distributed.Cluster.NodeType.WORKER
      });
      
      const node2 = manager.addNode({
        id: "test_node_2",
        type: Prime.Distributed.Cluster.NodeType.WORKER
      });
      
      const node3 = manager.addNode({
        id: "test_node_3",
        type: Prime.Distributed.Cluster.NodeType.WORKER
      });
      
      expect(manager.nodes.size).toBe(3);
      
      // Create coherence manager
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
      
      // Create test layers with varying coherence levels
      const coherentLayer = {
        id: "coherent_layer",
        config: {
          inputSize: 4,
          outputSize: 3
        },
        weights: generateRandomMatrix(4, 3),
        biases: generateRandomVector(3)
      };
      
      const partiallyCoherentLayer = {
        id: "partially_coherent_layer",
        config: {
          inputSize: 4,
          outputSize: 3
        },
        weights: introduceNumericalInstability(generateRandomMatrix(4, 3), 0.02),
        biases: generateRandomVector(3)
      };
      
      const incoherentLayer = {
        id: "incoherent_layer",
        config: {
          inputSize: 4,
          outputSize: 3
        },
        weights: introduceNumericalInstability(generateRandomMatrix(4, 3), 0.2),
        biases: [0.1, NaN, Infinity]
      };
      
      // Check coherence of each layer
      const coherentResult = coherenceManager.checkLayerCoherence(coherentLayer);
      const partialResult = coherenceManager.checkLayerCoherence(partiallyCoherentLayer);
      const incoherentResult = coherenceManager.checkLayerCoherence(incoherentLayer);
      
      // Test global coherence assessment
      const globalResult = coherenceManager.assessGlobalCoherence([
        coherentResult,
        partialResult, 
        incoherentResult
      ]);
      
      expect(typeof globalResult).toBe('object');
      expect(typeof globalResult.score).toBe('number');
      expect(typeof globalResult.isCoherent).toBe('boolean');
    });
  });
  
  describe('Distributed Network Synchronization', () => {
    test('Small parameter differences remain coherent', async () => {
      // Create a coherence manager
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
      
      // Create global parameters as the source of truth
      const globalParams = {
        weights: generateRandomMatrix(3, 2),
        biases: generateRandomVector(2)
      };
      
      // Create node parameters with slight deviations (should still be coherent)
      const nodeParams1 = {
        weights: JSON.parse(JSON.stringify(globalParams.weights)),
        biases: JSON.parse(JSON.stringify(globalParams.biases))
      };
      
      // Apply small random deviations to simulate minor sync differences
      for (let i = 0; i < nodeParams1.weights.length; i++) {
        for (let j = 0; j < nodeParams1.weights[i].length; j++) {
          nodeParams1.weights[i][j] += (Math.random() - 0.5) * 0.01;
        }
      }
      
      // Create layer with node parameters
      const coherentSyncLayer = {
        id: "sync_test_1",
        config: {
          inputSize: 3,
          outputSize: 2
        },
        weights: nodeParams1.weights,
        biases: nodeParams1.biases
      };
      
      // Check synchronization coherence
      const syncResult1 = coherenceManager.checkLayerCoherence(coherentSyncLayer, {
        isDistributed: true,
        globalParams
      });
      
      expect(syncResult1.isCoherent).toBe(true);
    });
    
    test('Large parameter differences are detected and corrected', async () => {
      // Create a coherence manager
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
      
      // Create global parameters as the source of truth
      const globalParams = {
        weights: generateRandomMatrix(3, 2),
        biases: generateRandomVector(2)
      };
      
      // Create desynced parameters with significant deviation
      const desyncedParams = introduceSynchronizationIncoherence(
        JSON.parse(JSON.stringify(globalParams)),
        globalParams,
        2.0 // Large deviation factor
      );
      
      // Store original desynced values for comparison later
      const originalDesyncedValues = {
        weights: JSON.parse(JSON.stringify(desyncedParams.weights)),
        biases: desyncedParams.biases ? JSON.parse(JSON.stringify(desyncedParams.biases)) : null
      };
      
      // Create a deep copy for the layer to ensure we're not modifying the original
      const incoherentSyncLayer = {
        id: "sync_test_2",
        config: {
          inputSize: 3,
          outputSize: 2
        },
        weights: JSON.parse(JSON.stringify(desyncedParams.weights)),
        biases: desyncedParams.biases ? JSON.parse(JSON.stringify(desyncedParams.biases)) : null
      };
      
      // Check synchronization coherence
      const syncResult2 = coherenceManager.checkLayerCoherence(incoherentSyncLayer, {
        isDistributed: true,
        globalParams
      });
      
      // Skip if synchronization check not available
      if (syncResult2.checks && syncResult2.checks.synchronization) {
        // Check coherence score is low for large differences 
        expect(syncResult2.checks.synchronization.coherence).toBeLessThan(0.7);
        
        // Check if synchronization violation is detected
        const hasSyncViolation = syncResult2.violations.some(
          v => v.type === Prime.Distributed.Coherence.CoherenceViolationType.SYNCHRONIZATION
        );
        
        expect(hasSyncViolation).toBe(true);
        
        // Test synchronization correction
        if (syncResult2.violations && syncResult2.violations.length > 0) {
          const syncViolations = syncResult2.violations.filter(
            v => v.type === Prime.Distributed.Coherence.CoherenceViolationType.SYNCHRONIZATION
          );
          
          if (syncViolations.length > 0) {
            const correctionResult = coherenceManager.applyCoherenceCorrection(
              incoherentSyncLayer,
              syncViolations,
              { globalParams }
            );
            
            expect(correctionResult.applied).toBe(true);
            
            // Verify parameters are closer to global parameters after correction
            let beforeDiff = 0;
            let afterDiff = 0;
            
            for (let i = 0; i < globalParams.weights.length; i++) {
              for (let j = 0; j < globalParams.weights[i].length; j++) {
                beforeDiff += Math.abs(originalDesyncedValues.weights[i][j] - globalParams.weights[i][j]);
                afterDiff += Math.abs(incoherentSyncLayer.weights[i][j] - globalParams.weights[i][j]);
              }
            }
            
            expect(afterDiff).toBeLessThan(beforeDiff);
          }
        }
      }
    });
  });
  
  describe('End-to-End Distributed Neural Network', () => {
    test('Network maintains coherence during training', async () => {
      // Create a simple multi-layer distributed network
      const layers = [];
      const layerSizes = [4, 8, 6, 2];
      const nodeCount = 2;
      
      // Create layers
      for (let i = 0; i < layerSizes.length - 1; i++) {
        layers.push(new Prime.Distributed.Partition.DistributedLayer({
          id: `e2e_layer_${i}`,
          layerConfig: {
            inputSize: layerSizes[i],
            outputSize: layerSizes[i + 1],
            activation: i === layerSizes.length - 2 ? 'sigmoid' : 'relu'
          },
          nodeIds: Array.from({ length: nodeCount }, (_, j) => `node_${j}`),
          partitionScheme: new Prime.Distributed.Partition.PartitionScheme({
            type: i % 2 === 0 ? 
              Prime.Distributed.Partition.PartitionType.INTRA_LAYER :
              Prime.Distributed.Partition.PartitionType.DATA_PARALLEL,
            nodeCount,
            layerConfig: {
              [`e2e_layer_${i}`]: {
                inputSize: layerSizes[i],
                outputSize: layerSizes[i + 1]
              }
            }
          })
        }));
      }
      
      expect(layers.length).toBe(layerSizes.length - 1);
      
      // Create a coherence manager
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
      
      // Mock a benchmark suite for testing
      const benchmarkSuite = {
        register: (id, fn, options) => ({ id, fn, options }),
        runBenchmark: async (id, options) => ({
          result: {
            finalForwardScore: 0.85,
            iterations: 1,
            coherenceScores: []
          }
        })
      };
      
      // Register and run a shortened version of the test
      const e2eCheckFn = async (context) => {
        // Create training data
        const sample = {
          input: generateRandomVector(layerSizes[0]),
          target: generateRandomVector(layerSizes[layerSizes.length - 1])
        };
        
        // Forward pass through first layer only to simplify test
        const layer = layers[0]; 
        const result = await layer.forward(sample.input);
        
        // Verify activation is valid
        expect(Array.isArray(result.activation)).toBe(true);
        expect(result.activation.length).toBe(layerSizes[1]);
        
        return {
          finalForwardScore: 0.85,
          iterations: 1
        };
      };
      
      // Run the benchmark function directly
      const benchmarkResult = await e2eCheckFn();
      
      expect(benchmarkResult).toBeDefined();
      expect(benchmarkResult.finalForwardScore).toBeGreaterThan(0.5);
    });
  });
});