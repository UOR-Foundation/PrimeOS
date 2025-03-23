/**
 * Integration tests for PrimeOS Distributed Computation Module - Training Pipeline
 */

const Prime = require("../../../src");
const { assertions, mocking } = require("../../utils");

describe("Distributed Training Pipeline Integration", () => {
  let trainingPipeline;
  let clusterManager;
  let dataProvider;
  
  beforeEach(() => {
    // Set up cluster
    clusterManager = new Prime.Distributed.Cluster.ClusterManager();
    
    // Add coordinator node
    clusterManager.addNode({
      id: "coordinator",
      type: Prime.Distributed.Cluster.NodeType.COORDINATOR
    });
    
    // Add worker nodes
    for (let i = 1; i <= 3; i++) {
      clusterManager.addNode({
        id: `worker_${i}`,
        type: Prime.Distributed.Cluster.NodeType.WORKER,
        maxConcurrency: 2
      });
    }
    
    // Create data provider
    dataProvider = new Prime.Distributed.Data.DistributedDataProvider({
      batchSize: 32,
      prefetchBufferSize: 3
    });
    
    // Create training pipeline
    trainingPipeline = new Prime.Distributed.Training.DistributedTrainingPipeline({
      clusterManager,
      dataProvider
    });
  });
  
  test("initializes training pipeline with model and dataset", async () => {
    // Create model configuration
    const modelConfig = {
      layers: [
        {
          type: "dense",
          inputSize: 10,
          outputSize: 8,
          activation: "relu"
        },
        {
          type: "dense",
          inputSize: 8,
          outputSize: 4,
          activation: "relu" 
        },
        {
          type: "dense",
          inputSize: 4,
          outputSize: 2,
          activation: "sigmoid"
        }
      ],
      optimizer: {
        type: "adam",
        learningRate: 0.001
      },
      loss: "binaryCrossEntropy"
    };
    
    // Create dataset configuration
    const datasetConfig = {
      trainSize: 1000,
      validationSize: 200,
      features: 10,
      classes: 2
    };
    
    // Initialize pipeline
    const initResult = await trainingPipeline.initialize(modelConfig, datasetConfig);
    
    // Verify initialization
    expect(initResult.success).toBe(true);
    expect(trainingPipeline.isInitialized()).toBe(true);
    expect(trainingPipeline.modelConfig).toEqual(modelConfig);
    
    // Verify components are initialized
    expect(trainingPipeline.partitionScheme).toBeDefined();
    expect(trainingPipeline.optimizer).toBeDefined();
    expect(trainingPipeline.dataProvider.isInitialized()).toBe(true);
  });
  
  test("executes a full training iteration across nodes", async () => {
    // Initialize with model and dataset
    await trainingPipeline.initialize(
      {
        layers: [
          { type: "dense", inputSize: 4, outputSize: 2, activation: "relu" },
          { type: "dense", inputSize: 2, outputSize: 1, activation: "sigmoid" }
        ],
        optimizer: { type: "sgd", learningRate: 0.01 },
        loss: "binaryCrossEntropy"
      },
      { trainSize: 100, validationSize: 20, features: 4, classes: 1 }
    );
    
    // Setup batch results tracking
    let batchResults = [];
    
    // Mock the data provider's getNextBatch method
    const originalGetNextBatch = dataProvider.getNextBatch;
    dataProvider.getNextBatch = jest.fn().mockImplementation(() => {
      return {
        batchId: `batch_${batchResults.length + 1}`,
        features: Array(32).fill().map(() => [Math.random(), Math.random(), Math.random(), Math.random()]),
        labels: Array(32).fill().map(() => [Math.random() > 0.5 ? 1 : 0])
      };
    });
    
    // Mock the node's processTrainingBatch method for testing
    for (const nodeId of ["worker_1", "worker_2", "worker_3"]) {
      const node = clusterManager.getNode(nodeId);
      const originalProcessTrainingBatch = node.processTrainingBatch;
      
      node.processTrainingBatch = jest.fn().mockImplementation(async (batch) => {
        // Simulate processing time
        await new Promise(resolve => setTimeout(resolve, 10));
        
        // Generate simulated gradients
        const gradients = {
          layer0: {
            weightGradients: [[0.001, 0.002, 0.003, 0.004], [0.005, 0.006, 0.007, 0.008]],
            biasGradients: [0.001, 0.002]
          },
          layer1: {
            weightGradients: [[0.003, 0.004], [0.005, 0.006]],
            biasGradients: [0.002]
          }
        };
        
        // Random loss
        const loss = Math.random() * 0.5;
        
        // Record batch result
        batchResults.push({
          nodeId,
          batchId: batch.batchId,
          loss
        });
        
        return {
          batchId: batch.batchId,
          gradients,
          loss,
          metrics: {
            accuracy: Math.random() * 0.8 + 0.2
          }
        };
      });
    }
    
    // Start training iteration
    const trainingResult = await trainingPipeline.runTrainingIteration(5); // 5 batches
    
    // Verify training results
    expect(trainingResult.success).toBe(true);
    expect(trainingResult.batchesProcessed).toBe(5);
    expect(trainingResult.totalLoss).toBeGreaterThan(0);
    
    // Verify all batches were processed
    expect(batchResults.length).toBe(5);
    
    // Verify gradient aggregation occurred
    expect(trainingResult.aggregatedGradients).toBeDefined();
    expect(Object.keys(trainingResult.aggregatedGradients)).toContain("layer0");
    expect(Object.keys(trainingResult.aggregatedGradients)).toContain("layer1");
    
    // Verify model was updated
    expect(trainingResult.modelUpdated).toBe(true);
    
    // Restore original methods
    dataProvider.getNextBatch = originalGetNextBatch;
  });
  
  test("handles node failures during training", async () => {
    // Initialize pipeline
    await trainingPipeline.initialize(
      {
        layers: [
          { type: "dense", inputSize: 4, outputSize: 2, activation: "relu" },
          { type: "dense", inputSize: 2, outputSize: 1, activation: "sigmoid" }
        ],
        optimizer: { type: "sgd", learningRate: 0.01 },
        loss: "binaryCrossEntropy"
      },
      { trainSize: 100, validationSize: 20, features: 4, classes: 1 }
    );
    
    // Setup failure simulation
    const worker2 = clusterManager.getNode("worker_2");
    const originalProcessTrainingBatch = worker2.processTrainingBatch;
    
    worker2.processTrainingBatch = jest.fn().mockImplementation(async (batch) => {
      if (batch.batchId === "batch_2") {
        // Simulate node failure
        throw new Error("Simulated node failure");
      }
      
      // Normal processing for other batches
      await new Promise(resolve => setTimeout(resolve, 10));
      return {
        batchId: batch.batchId,
        gradients: {
          layer0: {
            weightGradients: [[0.001, 0.002, 0.003, 0.004], [0.005, 0.006, 0.007, 0.008]],
            biasGradients: [0.001, 0.002]
          },
          layer1: {
            weightGradients: [[0.003, 0.004], [0.005, 0.006]],
            biasGradients: [0.002]
          }
        },
        loss: 0.3,
        metrics: { accuracy: 0.7 }
      };
    });
    
    // Mock node failure detection
    const originalCheckNodeStatus = clusterManager.checkNodeStatus;
    clusterManager.checkNodeStatus = jest.fn().mockImplementation(nodeId => {
      if (nodeId === "worker_2" && worker2.processTrainingBatch.mock.calls.length > 0) {
        // Mark node as failed after first call
        return {
          isAlive: false,
          status: "FAILED",
          reason: "Communication error"
        };
      }
      return {
        isAlive: true,
        status: "READY",
        reason: null
      };
    });
    
    // Handle failures
    trainingPipeline.setOption("faultTolerance", true);
    
    // Run training with potential failure
    const result = await trainingPipeline.runTrainingIteration(3);
    
    // Verify recovery from failure
    expect(result.success).toBe(true);
    expect(result.nodeFailures).toBeDefined();
    expect(result.nodeFailures.length).toBe(1);
    expect(result.nodeFailures[0].nodeId).toBe("worker_2");
    expect(result.nodeFailures[0].recovered).toBe(true);
    
    // Verify batches were reassigned
    expect(result.reassignedBatches).toBeDefined();
    expect(result.reassignedBatches.length).toBeGreaterThanOrEqual(1);
    
    // Verify training completed despite failure
    expect(result.batchesProcessed).toBe(3);
    
    // Restore original methods
    worker2.processTrainingBatch = originalProcessTrainingBatch;
    clusterManager.checkNodeStatus = originalCheckNodeStatus;
  });
  
  test("performs distributed validation correctly", async () => {
    // Initialize pipeline
    await trainingPipeline.initialize(
      {
        layers: [
          { type: "dense", inputSize: 4, outputSize: 2, activation: "relu" },
          { type: "dense", inputSize: 2, outputSize: 1, activation: "sigmoid" }
        ],
        optimizer: { type: "sgd", learningRate: 0.01 },
        loss: "binaryCrossEntropy"
      },
      { trainSize: 100, validationSize: 20, features: 4, classes: 1 }
    );
    
    // Mock validation data provider
    const originalGetValidationBatch = dataProvider.getValidationBatch;
    dataProvider.getValidationBatch = jest.fn().mockImplementation((batchIndex) => {
      return {
        batchId: `val_batch_${batchIndex}`,
        features: Array(20).fill().map(() => [Math.random(), Math.random(), Math.random(), Math.random()]),
        labels: Array(20).fill().map(() => [Math.random() > 0.5 ? 1 : 0])
      };
    });
    
    // Mock node validation processing
    for (const nodeId of ["worker_1", "worker_2", "worker_3"]) {
      const node = clusterManager.getNode(nodeId);
      const originalProcessValidationBatch = node.processValidationBatch;
      
      node.processValidationBatch = jest.fn().mockImplementation(async (batch) => {
        // Simulate processing time
        await new Promise(resolve => setTimeout(resolve, 5));
        
        return {
          batchId: batch.batchId,
          loss: 0.2 + Math.random() * 0.1,
          metrics: {
            accuracy: 0.7 + Math.random() * 0.2,
            precision: 0.75 + Math.random() * 0.15,
            recall: 0.72 + Math.random() * 0.18
          }
        };
      });
    }
    
    // Run validation
    const validationResult = await trainingPipeline.runValidation();
    
    // Verify validation results
    expect(validationResult.success).toBe(true);
    expect(validationResult.validationLoss).toBeGreaterThan(0);
    expect(validationResult.metrics).toBeDefined();
    expect(validationResult.metrics.accuracy).toBeGreaterThan(0);
    expect(validationResult.metrics.precision).toBeGreaterThan(0);
    expect(validationResult.metrics.recall).toBeGreaterThan(0);
    
    // Restore original methods
    dataProvider.getValidationBatch = originalGetValidationBatch;
  });
});