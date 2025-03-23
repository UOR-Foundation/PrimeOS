/**
 * Mock Distributed Network Test for PrimeOS Coherence
 * Tests coherence checking in a simulated distributed neural network
 *
 * This test simulates a distributed neural network training process to
 * validate the coherence detection and correction capabilities. It creates
 * a mock network configuration, simulates parameter changes during training,
 * introduces coherence violations, and tests the system's ability to detect
 * and correct these issues. This test focuses on the coherence management
 * aspects rather than actual neural network computations.
 */

// Import Prime with the Distributed module
const Prime = require("../src");

// Mock network configuration
const NETWORK_CONFIG = {
  nodes: 4, // Number of simulated nodes
  layers: 3, // Layers per model
  layerSizes: [10, 8, 6, 4], // Input, hidden, and output sizes
  batchSize: 5, // Batch size for training
  learningRate: 0.01, // Learning rate
  epochs: 3, // Number of training epochs
  partitioning: "intra_layer", // Partitioning strategy
};

// Utility functions
const generateRandomMatrix = (rows, cols) => {
  return Array.from({ length: rows }, () =>
    Array.from({ length: cols }, () => Math.random() * 2 - 1),
  );
};

const generateRandomVector = (size) => {
  return Array.from({ length: size }, () => Math.random() * 2 - 1);
};

// Mock data generator
const generateMockData = (count, inputSize, outputSize) => {
  return Array.from({ length: count }, () => ({
    input: generateRandomVector(inputSize),
    target: generateRandomVector(outputSize),
  }));
};

// Create a mock distributed network
const createMockNetwork = (config) => {
  const { nodes, layers, layerSizes, partitioning } = config;

  // Create cluster manager
  const manager = new Prime.Distributed.Cluster.ClusterManager({
    maxNodes: nodes,
    coherencePolicy: {
      enforceGlobalCoherence: true,
      minCoherenceThreshold: 0.7,
      recoveryStrategy: "rebalance",
    },
  });

  // Add nodes to the cluster
  const clusterNodes = [];
  for (let i = 0; i < nodes; i++) {
    clusterNodes.push(
      manager.addNode({
        id: `node_${i}`,
        type: Prime.Distributed.Cluster.NodeType.WORKER,
      }),
    );
  }

  // Create network layers
  const networkLayers = [];

  // Determine partition type based on configuration
  let partitionType;
  switch (partitioning) {
    case "intra_layer":
      partitionType = Prime.Distributed.Partition.PartitionType.INTRA_LAYER;
      break;
    case "layer_wise":
      partitionType = Prime.Distributed.Partition.PartitionType.LAYER_WISE;
      break;
    case "data_parallel":
      partitionType = Prime.Distributed.Partition.PartitionType.DATA_PARALLEL;
      break;
    default:
      partitionType = Prime.Distributed.Partition.PartitionType.INTRA_LAYER;
  }

  // Create layers
  for (let i = 0; i < layers; i++) {
    // Create layer config
    const layerConfig = {};
    layerConfig[`layer_${i}`] = {
      inputSize: layerSizes[i],
      outputSize: layerSizes[i + 1],
    };

    // Create partition scheme
    const partitionScheme = new Prime.Distributed.Partition.PartitionScheme({
      type: partitionType,
      nodeCount: nodes,
      layerConfig,
    });

    // Create distributed layer
    const layer = new Prime.Distributed.Partition.DistributedLayer({
      id: `layer_${i}`,
      layerConfig: {
        inputSize: layerSizes[i],
        outputSize: layerSizes[i + 1],
        activation: i === layers - 1 ? "sigmoid" : "relu",
      },
      nodeIds: clusterNodes.map((node) => node.id),
      partitionScheme,
    });

    networkLayers.push(layer);
  }

  // Create coherence manager
  const coherenceManager =
    new Prime.Distributed.Coherence.DistributedCoherenceManager();

  return {
    manager,
    nodes: clusterNodes,
    layers: networkLayers,
    coherenceManager,
  };
};

// Simulate forward pass through the network
const forwardPass = async (network, input) => {
  let activations = [];
  let caches = [];
  let layerInput = input;

  // Propagate through each layer
  for (const layer of network.layers) {
    const result = await layer.forward(layerInput);
    activations.push(result.activation);
    caches.push(result.cache);
    layerInput = result.activation;
  }

  return {
    output: activations[activations.length - 1],
    activations,
    caches,
  };
};

// Simulate backward pass through the network
const backwardPass = async (network, outputGradient, caches) => {
  let gradients = [];
  let gradOutput = outputGradient;

  // Backpropagate through each layer
  for (let i = network.layers.length - 1; i >= 0; i--) {
    const layer = network.layers[i];
    const cache = caches[i];

    const gradResult = await layer.backward(gradOutput, cache);
    gradients.unshift(gradResult);
    gradOutput = gradResult.dX;
  }

  return gradients;
};

// Update network weights
const updateWeights = async (network, gradients, learningRate) => {
  for (let i = 0; i < network.layers.length; i++) {
    await network.layers[i].update(gradients[i], learningRate);
  }
};

// Calculate mean squared error
const calculateMSE = (output, target) => {
  let sum = 0;
  for (let i = 0; i < output.length; i++) {
    sum += Math.pow(output[i] - target[i], 2);
  }
  return sum / output.length;
};

// Check coherence during training
const checkCoherence = async (network) => {
  // Instead of using tasks, directly check coherence of layer parameters
  const nodeReports = [];

  for (let i = 0; i < network.layers.length; i++) {
    const layer = network.layers[i];

    // Get layer parameters
    const layerParams = {
      id: layer.id,
      config: {
        inputSize: layer.layerConfig.inputSize,
        outputSize: layer.layerConfig.outputSize,
        activation: layer.layerConfig.activation,
      },
      weights: layer.weights,
      biases: layer.biases,
    };

    // Check coherence directly using the coherence manager
    const coherenceResult = network.coherenceManager.checkLayerCoherence(
      layerParams,
      {
        isDistributed: true,
        partitionScheme: layer.partitionScheme,
      },
    );

    nodeReports.push(coherenceResult);
  }

  // Assess global coherence
  return network.coherenceManager.assessGlobalCoherence(nodeReports);
};

// Simplified mock training - focusing only on coherence aspects
const mockTraining = async (network, data, config) => {
  const { epochs } = config;
  const coherenceScores = [];

  console.log(
    `Simulating training: ${epochs} epochs, batch size: ${data.length}`,
  );

  // Simulate training by making direct changes to parameters
  for (let epoch = 0; epoch < epochs; epoch++) {
    // Simulate parameter changes during training
    for (const layer of network.layers) {
      // Apply small random adjustments to weights
      if (layer.weights) {
        for (let i = 0; i < layer.weights.length; i++) {
          for (let j = 0; j < layer.weights[i].length; j++) {
            // Add some small random change
            layer.weights[i][j] += Math.random() * 0.1 - 0.05;
          }
        }
      }

      // Apply small random adjustments to biases
      if (layer.biases) {
        for (let i = 0; i < layer.biases.length; i++) {
          // Add some small random change
          layer.biases[i] += Math.random() * 0.1 - 0.05;
        }
      }
    }

    // For the last epoch, introduce some coherence violations in one layer
    if (epoch === epochs - 1) {
      // Choose the middle layer
      const middleLayer = network.layers[Math.floor(network.layers.length / 2)];

      // Introduce some NaN values to simulate numerical issues
      if (middleLayer.weights && middleLayer.weights.length > 0) {
        // Make 5% of weights NaN or Infinity
        for (let i = 0; i < middleLayer.weights.length; i++) {
          for (let j = 0; j < middleLayer.weights[i].length; j++) {
            if (Math.random() < 0.05) {
              middleLayer.weights[i][j] = Math.random() < 0.5 ? NaN : Infinity;
            }
          }
        }
      }
    }

    // Check coherence after each epoch
    const coherenceResult = await checkCoherence(network);
    coherenceScores.push(coherenceResult.score);

    console.log(
      `Epoch ${epoch + 1}/${epochs} - Coherence: ${coherenceResult.score.toFixed(4)}`,
    );

    // Handle coherence violations if detected
    if (!coherenceResult.isCoherent) {
      console.log(`Coherence violation detected in epoch ${epoch + 1}:`);
      console.log(`  - Score: ${coherenceResult.score.toFixed(4)}`);
      console.log(
        `  - Coherent node ratio: ${coherenceResult.coherentNodeRatio.toFixed(2)}`,
      );

      if (coherenceResult.recovery) {
        console.log(
          `  - Recommended recovery: ${coherenceResult.recovery.strategy}`,
        );

        // Apply automatic correction
        if (
          coherenceResult.recovery.strategy === "continue" ||
          coherenceResult.recovery.strategy === "resync"
        ) {
          console.log("  - Applying coherence correction...");

          // Find and fix the problematic layer
          for (const layer of network.layers) {
            const layerParams = {
              id: layer.id,
              config: {
                inputSize: layer.layerConfig.inputSize,
                outputSize: layer.layerConfig.outputSize,
              },
              weights: layer.weights,
              biases: layer.biases,
            };

            // Check layer coherence
            const layerResult =
              network.coherenceManager.checkLayerCoherence(layerParams);

            // Apply correction if needed
            if (!layerResult.isCoherent && layerResult.violations.length > 0) {
              network.coherenceManager.applyCoherenceCorrection(
                layerParams,
                layerResult.violations,
              );
              console.log(`    - Applied correction to layer ${layer.id}`);
            }
          }
        }
      }
    }
  }

  return {
    coherenceScores,
  };
};

// Run simulation
const runMockNetworkSimulation = async () => {
  console.log("=== Running Mock Distributed Network Coherence Test ===\n");

  // Create mock network
  console.log("Creating mock distributed network with configuration:");
  console.log(NETWORK_CONFIG);
  const network = createMockNetwork(NETWORK_CONFIG);

  // Generate mock training data
  const data = generateMockData(
    NETWORK_CONFIG.batchSize,
    NETWORK_CONFIG.layerSizes[0],
    NETWORK_CONFIG.layerSizes[NETWORK_CONFIG.layerSizes.length - 1],
  );

  console.log(`Generated ${data.length} mock training samples`);

  // Initial coherence check
  console.log("\nPerforming initial coherence check...");
  const initialCoherence = await checkCoherence(network);

  console.log(`Initial coherence score: ${initialCoherence.score.toFixed(4)}`);
  console.log(
    `Initial coherence status: ${initialCoherence.isCoherent ? "Coherent" : "Incoherent"}`,
  );

  // Simulate training the network
  console.log("\nSimulating mock distributed network training...");
  const trainingResults = await mockTraining(network, data, NETWORK_CONFIG);

  // Final coherence check
  console.log("\nPerforming final coherence check...");
  const finalCoherence = await checkCoherence(network);

  console.log(`Final coherence score: ${finalCoherence.score.toFixed(4)}`);
  console.log(
    `Final coherence status: ${finalCoherence.isCoherent ? "Coherent" : "Incoherent"}`,
  );

  // Summary
  console.log("\n=== Mock Network Training Summary ===");
  console.log(
    `Coherence trend: ${trainingResults.coherenceScores.map((s) => s.toFixed(4)).join(" → ")}`,
  );
  console.log(
    `Overall coherence change: ${initialCoherence.score.toFixed(4)} → ${finalCoherence.score.toFixed(4)}`,
  );

  // Clean up
  await network.manager.shutdown();

  return {
    initialCoherence,
    finalCoherence,
    trainingResults,
  };
};

// Run the simulation
try {
  runMockNetworkSimulation().catch((error) => {
    console.error("Simulation failed:", error.message);
    console.error(error.stack);
    process.exit(1);
  });
} catch (error) {
  console.error("Simulation setup failed:", error.message);
  console.error(error.stack);
  process.exit(1);
}
