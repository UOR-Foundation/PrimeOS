/**
 * Unit tests for PrimeOS Distributed Computation Module - Training components
 */

const Prime = require("../../../src");
const { assertions, mocking } = require("../../utils");

describe("PrimeOS Distributed Computation Module - Training", () => {
  // Set up a basic distributed training environment
  let clusterManager;
  let coherenceManager;
  let trainingCoordinator;
  
  beforeEach(() => {
    // Create cluster manager with nodes
    clusterManager = new Prime.Distributed.Cluster.ClusterManager();
    
    // Add worker nodes
    clusterManager.addNode({
      id: "worker_1",
      type: Prime.Distributed.Cluster.NodeType.WORKER
    });
    
    clusterManager.addNode({
      id: "worker_2",
      type: Prime.Distributed.Cluster.NodeType.WORKER
    });
    
    // Create coherence manager for distributed training
    coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager({
      strictChecking: false,
      thresholds: {
        numerical: 1e-6,
        gradient: 0.1,
        synchronization: 0.95
      }
    });
    
    // Create training coordinator
    trainingCoordinator = new Prime.Distributed.Training.TrainingCoordinator({
      clusterManager,
      coherenceManager
    });
  });
  
  test("creates a training coordinator with correct properties", () => {
    expect(trainingCoordinator instanceof Prime.Distributed.Training.TrainingCoordinator).toBe(true);
    expect(trainingCoordinator.clusterManager).toBe(clusterManager);
    expect(trainingCoordinator.coherenceManager).toBe(coherenceManager);
    
    // Verify initial state
    expect(trainingCoordinator.state).toBe(Prime.Distributed.Training.TrainingState.IDLE);
    expect(trainingCoordinator.currentEpoch).toBe(0);
    expect(trainingCoordinator.metrics).toBeDefined();
  });
  
  test("prepares a distributed training job correctly", () => {
    // Create a simple model for distributed training
    const modelConfig = {
      layers: [
        {
          type: "dense",
          inputSize: 10,
          outputSize: 5,
          activation: "relu"
        },
        {
          type: "dense",
          inputSize: 5,
          outputSize: 2,
          activation: "sigmoid"
        }
      ],
      optimizer: {
        type: "sgd",
        learningRate: 0.01
      }
    };
    
    // Prepare training job
    const job = trainingCoordinator.prepareTrainingJob({
      modelConfig,
      batchSize: 32,
      epochs: 5,
      validationSplit: 0.2
    });
    
    expect(job).toBeDefined();
    expect(job.id).toBeDefined();
    expect(job.config).toBeDefined();
    expect(job.config.batchSize).toBe(32);
    expect(job.config.epochs).toBe(5);
    expect(job.partitioning).toBeDefined();
  });
  
  test("distributes model parameters correctly", async () => {
    // Create a simple model with predefined parameters
    const model = {
      layers: [
        {
          id: "layer1",
          type: "dense",
          inputSize: 2,
          outputSize: 2,
          weights: [
            [0.1, 0.2],
            [0.3, 0.4]
          ],
          biases: [0.1, 0.2]
        }
      ]
    };
    
    // Distribute model parameters to nodes
    const distribution = await trainingCoordinator.distributeModelParameters(model);
    
    expect(distribution).toBeDefined();
    expect(distribution.status).toBe("success");
    expect(distribution.nodeAssignments).toBeDefined();
    expect(Object.keys(distribution.nodeAssignments).length).toBe(2); // Two worker nodes
    
    // Check that parameters were properly distributed
    const node1Assignment = distribution.nodeAssignments["worker_1"];
    expect(node1Assignment).toBeDefined();
    expect(node1Assignment.layers).toBeDefined();
    expect(node1Assignment.layers.length).toBeGreaterThan(0);
  });
  
  test("aggregates gradients correctly", () => {
    // Create sample gradients from worker nodes
    const nodeGradients = {
      "worker_1": {
        layerId: "layer1",
        weightGradients: [
          [0.01, 0.02],
          [0.03, 0.04]
        ],
        biasGradients: [0.005, 0.006]
      },
      "worker_2": {
        layerId: "layer1",
        weightGradients: [
          [0.02, 0.03],
          [0.04, 0.05]
        ],
        biasGradients: [0.007, 0.008]
      }
    };
    
    // Aggregate gradients
    const aggregatedGradients = trainingCoordinator.aggregateGradients(nodeGradients);
    
    expect(aggregatedGradients).toBeDefined();
    expect(aggregatedGradients.layerId).toBe("layer1");
    expect(aggregatedGradients.weightGradients).toBeDefined();
    expect(aggregatedGradients.weightGradients.length).toBe(2);
    expect(aggregatedGradients.weightGradients[0].length).toBe(2);
    
    // Check aggregation calculation (average in this case)
    expect(aggregatedGradients.weightGradients[0][0]).toBeCloseTo(0.015, 5); // (0.01 + 0.02) / 2
    expect(aggregatedGradients.biasGradients[0]).toBeCloseTo(0.006, 5); // (0.005 + 0.007) / 2
  });
  
  test("monitors and maintains coherence during training", async () => {
    // Setup training job
    const job = trainingCoordinator.prepareTrainingJob({
      modelConfig: {
        layers: [
          {
            type: "dense",
            inputSize: 2,
            outputSize: 2,
            activation: "relu"
          }
        ]
      },
      batchSize: 32,
      epochs: 1
    });
    
    // Create mock coherence check results
    const nodeCoherenceResults = [
      {
        nodeId: "worker_1",
        isCoherent: true,
        coherenceScore: 0.98,
        violations: []
      },
      {
        nodeId: "worker_2",
        isCoherent: true,
        coherenceScore: 0.96,
        violations: []
      }
    ];
    
    // Mock the coherenceManager's assessGlobalCoherence method
    const originalAssessGlobalCoherence = coherenceManager.assessGlobalCoherence;
    coherenceManager.assessGlobalCoherence = jest.fn().mockReturnValue({
      isCoherent: true,
      score: 0.97,
      coherentNodeRatio: 1.0,
      violationCounts: {}
    });
    
    // Check training coherence
    const coherenceStatus = await trainingCoordinator.checkTrainingCoherence(job.id, nodeCoherenceResults);
    
    expect(coherenceStatus).toBeDefined();
    expect(coherenceStatus.isCoherent).toBe(true);
    expect(coherenceStatus.globalScore).toBeCloseTo(0.97, 2);
    expect(coherenceStatus.needsRecovery).toBe(false);
    
    // Restore original method
    coherenceManager.assessGlobalCoherence = originalAssessGlobalCoherence;
  });
});