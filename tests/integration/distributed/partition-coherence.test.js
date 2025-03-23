/**
 * Integration tests for PrimeOS Distributed Computation Module - Partition and Coherence
 */

const Prime = require("../../../src");
const { assertions, mocking } = require("../../utils");

describe("Distributed Partition and Coherence Integration", () => {
  let partitionManager;
  let coherenceManager;

  beforeEach(() => {
    // Create partition manager
    partitionManager = new Prime.Distributed.Partition.PartitionManager({
      strategyPreference: "balanced",
    });

    // Create coherence manager
    coherenceManager =
      new Prime.Distributed.Coherence.DistributedCoherenceManager({
        strictChecking: false,
        thresholds: {
          numerical: 1e-6,
          gradient: 0.1,
          synchronization: 0.9,
        },
      });
  });

  test("partition schemes are evaluated for coherence", () => {
    // Create network configuration
    const networkConfig = {
      layers: [
        {
          id: "layer1",
          type: "dense",
          inputSize: 10,
          outputSize: 20,
          activation: "relu",
        },
        {
          id: "layer2",
          type: "dense",
          inputSize: 20,
          outputSize: 15,
          activation: "sigmoid",
        },
        {
          id: "layer3",
          type: "dense",
          inputSize: 15,
          outputSize: 5,
          activation: "linear",
        },
      ],
    };

    // Set up nodes for partitioning
    const nodes = [
      { id: "node_1", capacity: 1.0, reliability: 0.99 },
      { id: "node_2", capacity: 0.8, reliability: 0.95 },
      { id: "node_3", capacity: 0.6, reliability: 0.9 },
    ];

    // Generate multiple partition schemes
    const schemes = partitionManager.generatePartitionSchemes(
      networkConfig,
      nodes,
    );
    expect(schemes.length).toBeGreaterThan(0);

    // Evaluate each scheme for coherence
    const evaluations = schemes.map((scheme) => {
      return {
        scheme,
        coherence: coherenceManager.evaluatePartitionSchemeCoherence(
          scheme,
          networkConfig,
        ),
      };
    });

    // Verify that coherence scores are calculated
    for (const evaluation of evaluations) {
      expect(evaluation.coherence).toBeDefined();
      expect(evaluation.coherence.score).toBeGreaterThanOrEqual(0);
      expect(evaluation.coherence.score).toBeLessThanOrEqual(1);
      expect(evaluation.coherence.factors).toBeDefined();
    }

    // Select the scheme with highest coherence
    const bestScheme = evaluations.reduce((best, current) => {
      return current.coherence.score > best.coherence.score ? current : best;
    }, evaluations[0]);

    expect(bestScheme.coherence.score).toBeGreaterThan(0.5);
  });

  test("distributed layer functions maintain coherence", async () => {
    // Create a distributed layer with coherence checking
    const layer = new Prime.Distributed.Partition.DistributedLayer({
      id: "coherent_layer",
      layerConfig: {
        inputSize: 3,
        outputSize: 2,
        activation: "linear",
        weights: [
          [0.1, 0.2, 0.3],
          [0.4, 0.5, 0.6],
        ],
        biases: [0.1, 0.2],
      },
      nodeIds: ["node_1", "node_2"],
      coherenceManager,
    });

    // Verify initial coherence
    const initialCoherence = await layer.checkCoherence();
    expect(initialCoherence.isCoherent).toBe(true);
    expect(initialCoherence.coherenceScore).toBeGreaterThan(0.9);

    // Perform forward pass
    const input = [1, 2, 3];
    const result = await layer.forward(input);

    // Check the result
    expect(result).toBeDefined();
    expect(result.activation).toBeDefined();
    expect(result.activation.length).toBe(2);

    // Verify coherence after computation
    const afterCoherence = await layer.checkCoherence();
    expect(afterCoherence.isCoherent).toBe(true);

    // Introduce an incoherence
    layer.weights[0][0] = NaN;

    // Verify coherence violation is detected
    const incoherentState = await layer.checkCoherence();
    expect(incoherentState.isCoherent).toBe(false);
    expect(incoherentState.violations.length).toBeGreaterThan(0);

    // Test auto-correction mechanism
    await layer.repairCoherence(incoherentState.violations);

    // Verify coherence is restored
    const restoredCoherence = await layer.checkCoherence();
    expect(restoredCoherence.isCoherent).toBe(true);
  });

  test("parameters stay synchronized across distributed components", async () => {
    // Create a parameter synchronization manager
    const syncManager =
      new Prime.Distributed.Coherence.ParameterSynchronizationManager({
        coherenceManager,
      });

    // Create global parameters
    const globalParams = {
      layer1: {
        weights: [
          [0.1, 0.2, 0.3],
          [0.4, 0.5, 0.6],
        ],
        biases: [0.1, 0.2],
      },
    };

    // Create node-specific parameters (with slight deviations)
    const nodeParams = {
      node_1: {
        layer1: {
          weights: [
            [0.11, 0.21, 0.31], // Slightly different
            [0.4, 0.5, 0.6], // Same
          ],
          biases: [0.1, 0.2], // Same
        },
      },
      node_2: {
        layer1: {
          weights: [
            [0.1, 0.2, 0.3], // Same
            [0.39, 0.51, 0.6], // Slightly different
          ],
          biases: [0.09, 0.21], // Slightly different
        },
      },
    };

    // Check synchronization
    const syncResult = await syncManager.checkParameterSynchronization(
      globalParams,
      nodeParams,
    );

    // Verify results
    expect(syncResult).toBeDefined();
    expect(syncResult.isCoherent).toBe(true); // Minor differences are acceptable
    expect(syncResult.nodeResults).toBeDefined();
    expect(Object.keys(syncResult.nodeResults).length).toBe(2);

    // Verify node-specific results
    for (const nodeId of ["node_1", "node_2"]) {
      expect(syncResult.nodeResults[nodeId]).toBeDefined();
      expect(syncResult.nodeResults[nodeId].deviations).toBeDefined();
    }

    // Introduce a significant deviation
    nodeParams["node_1"].layer1.weights[0][0] = 5.0; // Large deviation

    // Re-check synchronization
    const incoherentResult = await syncManager.checkParameterSynchronization(
      globalParams,
      nodeParams,
    );

    // Verify incoherence is detected
    expect(incoherentResult.isCoherent).toBe(false);
    expect(incoherentResult.nodeResults["node_1"].isCoherent).toBe(false);

    // Fix the deviation through synchronization
    await syncManager.synchronizeParameters(globalParams, nodeParams);

    // Verify parameters are now synchronized
    const node1Params = nodeParams["node_1"].layer1.weights[0][0];
    const globalValue = globalParams.layer1.weights[0][0];
    expect(node1Params).toBeCloseTo(globalValue, 5);

    // Final synchronization check
    const finalSyncResult = await syncManager.checkParameterSynchronization(
      globalParams,
      nodeParams,
    );
    expect(finalSyncResult.isCoherent).toBe(true);
  });
});
