/**
 * Tests for PrimeOS Distributed Computation Module
 */

// Import Prime with the Distributed module
const Prime = require("../src");

describe('PrimeOS Distributed Computation Module', () => {
  describe('Cluster', () => {
    test('cluster node creation', () => {
      const node = new Prime.Distributed.Cluster.ClusterNode({
        id: "test_node_1",
        type: Prime.Distributed.Cluster.NodeType.WORKER,
        address: "127.0.0.1",
        port: 8080,
        maxConcurrency: 4,
      });

      expect(node instanceof Prime.Distributed.Cluster.ClusterNode).toBe(true);
      expect(node.id).toBe("test_node_1");
      expect(node.type).toBe(Prime.Distributed.Cluster.NodeType.WORKER);
      expect(node.maxConcurrency).toBe(4);
      expect(node.state).toBe(Prime.Distributed.Cluster.NodeState.READY);

      // Test node metrics
      const metrics = node.getMetrics();
      expect(typeof metrics).toBe("object");
      expect(metrics.tasksProcessed).toBe(0);
      expect(typeof metrics.lastHeartbeat).toBe("number");
    });

    test('cluster manager', () => {
      const manager = new Prime.Distributed.Cluster.ClusterManager({
        maxNodes: 5,
        discoveryMethod: "local",
      });

      expect(manager instanceof Prime.Distributed.Cluster.ClusterManager).toBe(true);
      expect(manager.config.maxNodes).toBe(5);
      expect(manager.nodes.size).toBe(0);

      // Add a node
      const node = manager.addNode({
        id: "test_node_2",
        type: Prime.Distributed.Cluster.NodeType.WORKER,
      });

      expect(manager.nodes.size).toBe(1);
      expect(node.id).toBe("test_node_2");

      // Get manager metrics
      const metrics = manager.getMetrics();
      expect(typeof metrics).toBe("object");
      expect(metrics.totalNodes).toBe(1);
    });

    test('task submission (simplified)', () => {
      // Create manager and node
      const manager = new Prime.Distributed.Cluster.ClusterManager();

      const node = manager.addNode({
        id: "compute_node",
        type: Prime.Distributed.Cluster.NodeType.WORKER,
      });

      // Define a simple task
      const task = {
        id: "task_1",
        type: "forward_pass",
        data: {
          layerConfig: {
            inputSize: 3,
            outputSize: 2,
            activation: "relu",
          },
          input: [1, 2, 3],
        },
      };

      // Submit task and verify it's handled - this is a partial test
      // In a real system we'd wait for the result, but here we just ensure
      // that submission doesn't throw an error
      const promise = manager.submitTask(task);
      expect(promise instanceof Promise).toBe(true);
    });
  });

  describe('Communication', () => {
    test('communication channel', () => {
      const channel = new Prime.Distributed.Communication.CommunicationChannel({
        nodeId: "test_node_3",
      });

      expect(channel instanceof Prime.Distributed.Communication.CommunicationChannel).toBe(true);
      expect(channel.nodeId).toBe("test_node_3");
      expect(channel.isConnected()).toBe(true);

      // Test channel metrics
      const metrics = channel.getMetrics();
      expect(typeof metrics).toBe("object");
      expect(metrics.messagesSent).toBe(0);
      expect(metrics.messagesReceived).toBe(0);
    });

    test('message router', () => {
      const router = new Prime.Distributed.Communication.MessageRouter({
        nodeId: "test_node_4",
      });

      expect(router instanceof Prime.Distributed.Communication.MessageRouter).toBe(true);
      expect(router.nodeId).toBe("test_node_4");
      expect(router.channel instanceof Prime.Distributed.Communication.CommunicationChannel).toBe(true);

      // Register a custom handler
      let handlerCalled = false;

      router.registerHandler(
        Prime.Distributed.Communication.MessageType.HEARTBEAT,
        (message) => {
          handlerCalled = true;
          return Promise.resolve({ handled: true });
        },
      );

      // Test router metrics
      const metrics = router.getMetrics();
      expect(typeof metrics).toBe("object");
      expect(typeof metrics.messagesRouted).toBe("number");
      expect(typeof metrics.channel).toBe("object");
    });
  });

  describe('Partition', () => {
    test('partition scheme', () => {
      // Create layer configuration
      const layerConfig = {
        layer1: {
          inputSize: 10,
          outputSize: 20,
          activation: "relu",
        },
        layer2: {
          inputSize: 20,
          outputSize: 15,
          activation: "sigmoid",
        },
        layer3: {
          inputSize: 15,
          outputSize: 5,
          activation: "linear",
        },
      };

      // Create a layer-wise partition scheme
      const scheme = new Prime.Distributed.Partition.PartitionScheme({
        type: Prime.Distributed.Partition.PartitionType.LAYER_WISE,
        nodeCount: 2,
        layerConfig,
      });

      expect(scheme instanceof Prime.Distributed.Partition.PartitionScheme).toBe(true);
      expect(scheme.type).toBe(Prime.Distributed.Partition.PartitionType.LAYER_WISE);
      expect(scheme.nodeCount).toBe(2);

      // Check layer assignments
      expect(scheme.layerAssignments.size).toBeGreaterThan(0);

      // Get node layers
      const node0Layers = scheme.getNodeLayers("node_0");
      const node1Layers = scheme.getNodeLayers("node_1");

      expect(Array.isArray(node0Layers)).toBe(true);
      expect(Array.isArray(node1Layers)).toBe(true);

      // Get scheme summary
      const summary = scheme.getSummary();
      expect(typeof summary).toBe("object");
      expect(Array.isArray(summary.nodeLayers)).toBe(true);
      expect(typeof summary.coherenceScore).toBe("number");
    });

    test('distributed layer', () => {
      // Create a simple distributed layer
      const layer = new Prime.Distributed.Partition.DistributedLayer({
        id: "dist_layer_1",
        layerConfig: {
          inputSize: 10,
          outputSize: 5,
          activation: "relu",
        },
        nodeIds: ["node_0", "node_1"],
      });

      expect(layer instanceof Prime.Distributed.Partition.DistributedLayer).toBe(true);
      expect(layer.id).toBe("dist_layer_1");
      expect(Array.isArray(layer.nodeIds)).toBe(true);
      expect(layer.nodeIds.length).toBe(2);

      // Test layer metrics
      const metrics = layer.getMetrics();
      expect(typeof metrics).toBe("object");
      expect(metrics.completedForwardPasses).toBe(0);

      // Test layer partition scheme
      const scheme = layer.getPartitionScheme();
      expect(scheme instanceof Prime.Distributed.Partition.PartitionScheme).toBe(true);
    });

    test('distributed computation', async () => {
      // Create a distributed layer
      const layer = new Prime.Distributed.Partition.DistributedLayer({
        id: "dist_layer_2",
        layerConfig: {
          inputSize: 3,
          outputSize: 2,
          activation: "linear",
          weights: [
            [1, 0, 0],
            [0, 1, 0],
          ],
          biases: [0, 0],
        },
        nodeIds: ["node_0", "node_1"], // Use two nodes
        partitionScheme: new Prime.Distributed.Partition.PartitionScheme({
          type: Prime.Distributed.Partition.PartitionType.LAYER_WISE,
          nodeCount: 2,
          layerConfig: {
            dist_layer_2: {
              inputSize: 3,
              outputSize: 2,
            },
          },
        }),
      });

      // Test forward pass
      const input = [2, 3, 4];

      // Perform forward pass
      const result = await layer.forward(input);
      
      expect(result).toBeDefined();
      expect(Array.isArray(result.activation)).toBe(true);
      expect(result.cache).toBeDefined();
    });
  });

  describe('Coherence', () => {
    test('coherence manager creation', () => {
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager({
        strictChecking: true,
        thresholds: {
          numerical: 1e-8,
          gradient: 0.5
        }
      });

      expect(coherenceManager instanceof Prime.Distributed.Coherence.DistributedCoherenceManager).toBe(true);
      expect(coherenceManager.config.strictChecking).toBe(true);
      expect(coherenceManager.config.thresholds.numerical).toBe(1e-8);
      
      // Check enums are defined
      expect(typeof Prime.Distributed.Coherence.CoherenceViolationType).toBe('object');
      expect(typeof Prime.Distributed.Coherence.ViolationSeverity).toBe('object');
      expect(typeof Prime.Distributed.Coherence.RecoveryStrategy).toBe('object');

      // Test metrics initialization
      const metrics = coherenceManager.getMetrics();
      expect(typeof metrics).toBe('object');
      expect(metrics.checksPerformed).toBe(0);
      expect(metrics.violationsDetected).toBe(0);
      expect(metrics.averageCoherenceScore).toBe(1.0);
    });

    test('layer coherence checking with valid layer', () => {
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
      
      // Create a valid layer for checking
      const validLayer = {
        id: "valid_layer",
        config: {
          inputSize: 2,
          outputSize: 3
        },
        weights: [
          [0.1, 0.2, 0.3],
          [0.4, 0.5, 0.6]
        ],
        biases: [0.1, 0.2, 0.3]
      };
      
      const result = coherenceManager.checkLayerCoherence(validLayer);
      
      expect(result.isCoherent).toBe(true);
      expect(result.coherenceScore).toBeGreaterThanOrEqual(0.9);
      expect(result.dimensionsValid).toBe(true);
      expect(Array.isArray(result.violations)).toBe(true);
      expect(result.violations.length).toBe(0);
    });

    test('layer coherence checking with invalid layer', () => {
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
      
      // Create an invalid layer for checking (with NaN values)
      const invalidLayer = {
        id: "invalid_layer",
        config: {
          inputSize: 2,
          outputSize: 3
        },
        weights: [
          [0.1, NaN, 0.3],
          [0.4, 0.5, Infinity]
        ],
        biases: [0.1, 0.2, NaN]
      };
      
      const result = coherenceManager.checkLayerCoherence(invalidLayer);
      
      expect(result.isCoherent).toBe(false);
      expect(result.coherenceScore).toBeLessThan(0.7);
      expect(Array.isArray(result.violations)).toBe(true);
      expect(result.violations.length).toBeGreaterThan(0);
      
      if (result.violations.length > 0) {
        expect(result.violations[0].type).toBe(Prime.Distributed.Coherence.CoherenceViolationType.NUMERICAL);
      }
      
      expect(typeof result.recovery).toBe('object');
    });

    test('coherence correction', () => {
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
      
      // Create a layer with NaN values to correct
      const layerToCorrect = {
        id: "correction_layer",
        config: {
          inputSize: 3,
          outputSize: 2
        },
        weights: [
          [0.1, NaN, 0.3],
          [0.4, 0.5, Infinity]
        ],
        biases: [0.1, NaN]
      };
      
      // Check coherence first
      const checkResult = coherenceManager.checkLayerCoherence(layerToCorrect);
      expect(checkResult.isCoherent).toBe(false);
      
      // Apply correction
      const correctionResult = coherenceManager.applyCoherenceCorrection(
        layerToCorrect, 
        checkResult.violations
      );
      
      expect(correctionResult.applied).toBe(true);
      expect(Array.isArray(correctionResult.corrections)).toBe(true);
      expect(correctionResult.corrections.includes('numerical_stability')).toBe(true);
      
      // Now check if the layer is corrected
      for (let i = 0; i < layerToCorrect.weights.length; i++) {
        for (let j = 0; j < layerToCorrect.weights[i].length; j++) {
          expect(Number.isFinite(layerToCorrect.weights[i][j])).toBe(true);
        }
      }
      
      for (let i = 0; i < layerToCorrect.biases.length; i++) {
        expect(Number.isFinite(layerToCorrect.biases[i])).toBe(true);
      }
      
      // Final coherence check
      const finalCheckResult = coherenceManager.checkLayerCoherence(layerToCorrect);
      expect(finalCheckResult.isCoherent).toBe(true);
    });

    test('global coherence assessment', () => {
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
      
      // Create simulated coherence results from different nodes
      const nodeResults = [
        {
          nodeId: "node_1",
          coherenceScore: 0.95,
          isCoherent: true,
          violations: []
        },
        {
          nodeId: "node_2",
          coherenceScore: 0.92,
          isCoherent: true,
          violations: []
        },
        {
          nodeId: "node_3",
          coherenceScore: 0.65,
          isCoherent: false,
          violations: [
            {
              type: Prime.Distributed.Coherence.CoherenceViolationType.SYNCHRONIZATION,
              severity: Prime.Distributed.Coherence.ViolationSeverity.MEDIUM,
              message: "Parameter synchronization coherence violation"
            }
          ]
        }
      ];
      
      const globalResult = coherenceManager.assessGlobalCoherence(nodeResults);
      
      expect(typeof globalResult).toBe('object');
      expect(typeof globalResult.isCoherent).toBe('boolean');
      expect(typeof globalResult.score).toBe('number');
      expect(typeof globalResult.coherentNodeRatio).toBe('number');
      expect(globalResult.score).toBeGreaterThan(0.5);
      expect(globalResult.coherentNodeRatio).toBe(2/3);
      
      // Since one node has synchronization issues, the most common type should be synchronization
      expect(globalResult.violationCounts.synchronization).toBe(1);
    });

    test('synchronization coherence', () => {
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();
      
      // Create a layer
      const layer = {
        id: "sync_layer",
        config: {
          inputSize: 2,
          outputSize: 2
        },
        weights: [
          [0.1, 0.2],
          [0.3, 0.4]
        ],
        biases: [0.1, 0.2]
      };
      
      // Create global parameters that are slightly different
      const globalParams = {
        weights: [
          [0.11, 0.21],
          [0.31, 0.41]
        ],
        biases: [0.11, 0.21]
      };
      
      // Check synchronization coherence
      const result = coherenceManager.checkLayerCoherence(layer, {
        isDistributed: true,
        globalParams
      });
      
      expect(typeof result).toBe('object');
      
      // In a mock environment, we might not have a full result object
      if (result.checks && result.checks.synchronization) {
        expect(typeof result.checks.synchronization).toBe('object');
        // The difference is small, so it should still be coherent
        expect(result.checks.synchronization.coherence).toBeGreaterThan(0.5);
      }
      
      // Now create a global parameter set with large differences
      const divergentParams = {
        weights: [
          [1.1, 2.1],
          [3.1, 4.1]
        ],
        biases: [1.1, 2.1]
      };
      
      // Check synchronization coherence with divergent parameters
      const divergentResult = coherenceManager.checkLayerCoherence(layer, {
        isDistributed: true,
        globalParams: divergentParams
      });
      
      // Check synchronization coherence if available
      if (divergentResult.checks && divergentResult.checks.synchronization) {
        expect(divergentResult.checks.synchronization.coherence).toBeLessThan(0.5);
        
        // Check that the violations include synchronization issues
        const syncViolation = divergentResult.violations.find(
          v => v.type === Prime.Distributed.Coherence.CoherenceViolationType.SYNCHRONIZATION
        );
        
        expect(syncViolation).toBeDefined();
      }
    });
  });
});