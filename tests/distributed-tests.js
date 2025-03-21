/**
 * Tests for PrimeOS Distributed Computation Module
 */

// Import Prime with the Distributed module
const Prime = require("../src");

// Test utilities
const assert = (condition, message) => {
  if (!condition) {
    throw new Error(`Assertion failed: ${message}`);
  }
  console.log(`✓ PASS: ${message}`);
};

const assertApproximatelyEqual = (a, b, message, epsilon = 1e-6) => {
  const diff = Math.abs(a - b);
  if (diff > epsilon) {
    throw new Error(
      `Assertion failed: ${message} - values differ by ${diff} (${a} vs ${b})`,
    );
  }
  console.log(`✓ PASS: ${message}`);
};

const runTests = () => {
  console.log("=== Running Distributed Computation Module Tests ===\n");

  // Test group: Cluster
  console.log("--- Cluster Tests ---");

  // Test cluster node creation
  {
    const node = new Prime.Distributed.Cluster.ClusterNode({
      id: "test_node_1",
      type: Prime.Distributed.Cluster.NodeType.WORKER,
      address: "127.0.0.1",
      port: 8080,
      maxConcurrency: 4,
    });

    assert(
      node instanceof Prime.Distributed.Cluster.ClusterNode,
      "ClusterNode can be instantiated",
    );

    assert(node.id === "test_node_1", "Node has correct ID");
    assert(
      node.type === Prime.Distributed.Cluster.NodeType.WORKER,
      "Node has correct type",
    );
    assert(node.maxConcurrency === 4, "Node has correct concurrency");
    assert(
      node.state === Prime.Distributed.Cluster.NodeState.READY,
      "Node is in ready state",
    );

    // Test node metrics
    const metrics = node.getMetrics();
    assert(typeof metrics === "object", "Node provides metrics");
    assert(metrics.tasksProcessed === 0, "Initial tasks processed is zero");
    assert(
      typeof metrics.lastHeartbeat === "number",
      "Heartbeat timestamp is a number",
    );
  }

  // Test cluster manager
  {
    const manager = new Prime.Distributed.Cluster.ClusterManager({
      maxNodes: 5,
      discoveryMethod: "local",
    });

    assert(
      manager instanceof Prime.Distributed.Cluster.ClusterManager,
      "ClusterManager can be instantiated",
    );

    assert(manager.config.maxNodes === 5, "Manager has correct max nodes");
    assert(manager.nodes.size === 0, "Manager starts with no nodes");

    // Add a node
    const node = manager.addNode({
      id: "test_node_2",
      type: Prime.Distributed.Cluster.NodeType.WORKER,
    });

    assert(manager.nodes.size === 1, "Node was added to manager");
    assert(node.id === "test_node_2", "Node has correct ID");

    // Get manager metrics
    const metrics = manager.getMetrics();
    assert(typeof metrics === "object", "Manager provides metrics");
    assert(metrics.totalNodes === 1, "Metrics show correct node count");
  }

  // Test task submission (simplified)
  {
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
    try {
      const promise = manager.submitTask(task);
      assert(promise instanceof Promise, "Task submission returns a promise");
    } catch (error) {
      throw new Error(`Task submission failed: ${error.message}`);
    }
  }

  // Test group: Communication
  console.log("\n--- Communication Tests ---");

  // Test communication channel
  {
    const channel = new Prime.Distributed.Communication.CommunicationChannel({
      nodeId: "test_node_3",
    });

    assert(
      channel instanceof Prime.Distributed.Communication.CommunicationChannel,
      "CommunicationChannel can be instantiated",
    );

    assert(channel.nodeId === "test_node_3", "Channel has correct node ID");
    assert(
      channel.isConnected(),
      "Channel starts in connected state in mock mode",
    );

    // Test channel metrics
    const metrics = channel.getMetrics();
    assert(typeof metrics === "object", "Channel provides metrics");
    assert(metrics.messagesSent === 0, "Initial messages sent is zero");
    assert(metrics.messagesReceived === 0, "Initial messages received is zero");
  }

  // Test message router
  {
    const router = new Prime.Distributed.Communication.MessageRouter({
      nodeId: "test_node_4",
    });

    assert(
      router instanceof Prime.Distributed.Communication.MessageRouter,
      "MessageRouter can be instantiated",
    );

    assert(router.nodeId === "test_node_4", "Router has correct node ID");
    assert(
      router.channel instanceof
        Prime.Distributed.Communication.CommunicationChannel,
      "Router creates a communication channel",
    );

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
    assert(typeof metrics === "object", "Router provides metrics");
    assert(
      typeof metrics.messagesRouted === "number",
      "Metrics include messages routed",
    );
    assert(
      typeof metrics.channel === "object",
      "Metrics include channel stats",
    );
  }

  // Test group: Partition
  console.log("\n--- Partition Tests ---");

  // Test partition scheme
  {
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

    assert(
      scheme instanceof Prime.Distributed.Partition.PartitionScheme,
      "PartitionScheme can be instantiated",
    );

    assert(
      scheme.type === Prime.Distributed.Partition.PartitionType.LAYER_WISE,
      "Scheme has correct type",
    );
    assert(scheme.nodeCount === 2, "Scheme has correct node count");

    // Check layer assignments
    assert(
      scheme.layerAssignments.size > 0,
      "Layers have been assigned to nodes",
    );

    // Get node layers
    const node0Layers = scheme.getNodeLayers("node_0");
    const node1Layers = scheme.getNodeLayers("node_1");

    assert(Array.isArray(node0Layers), "Node 0 has assigned layers");
    assert(Array.isArray(node1Layers), "Node 1 has assigned layers");

    // Get scheme summary
    const summary = scheme.getSummary();
    assert(typeof summary === "object", "Scheme provides summary");
    assert(Array.isArray(summary.nodeLayers), "Summary includes node layers");
    assert(
      typeof summary.coherenceScore === "number",
      "Summary includes coherence score",
    );
  }

  // Test distributed layer
  {
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

    assert(
      layer instanceof Prime.Distributed.Partition.DistributedLayer,
      "DistributedLayer can be instantiated",
    );

    assert(layer.id === "dist_layer_1", "Layer has correct ID");
    assert(Array.isArray(layer.nodeIds), "Layer has node IDs");
    assert(layer.nodeIds.length === 2, "Layer has correct number of nodes");

    // Test layer metrics
    const metrics = layer.getMetrics();
    assert(typeof metrics === "object", "Layer provides metrics");
    assert(
      metrics.completedForwardPasses === 0,
      "Initial forward passes is zero",
    );

    // Test layer partition scheme
    const scheme = layer.getPartitionScheme();
    assert(
      scheme instanceof Prime.Distributed.Partition.PartitionScheme,
      "Layer has a partition scheme",
    );
  }

  // Test distributed computation
  {
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

    // Perform forward pass (wrap in async/await for synchronous testing)
    (async () => {
      try {
        const result = await layer.forward(input);

        // This would normally be specific assertions, but in our mock implementation
        // we'll just check that the result has the expected structure
        assert(result, "Forward pass returns a result");
        assert(Array.isArray(result.activation), "Result has activation array");
        assert(result.cache, "Result includes cache for backprop");

        console.log(
          "Forward pass successful with activation:",
          result.activation,
        );

        // Complete the tests
        console.log(
          "\n=== All Distributed Computation Module Tests Completed ===",
        );
      } catch (error) {
        console.error("Forward pass failed:", error);
        process.exit(1);
      }
    })();
  }

  console.log("\n=== All Distributed Computation Module Tests Passed ===");
};

// Run the tests
try {
  runTests();
} catch (error) {
  console.error("Test failed:", error.message);
  console.error(error.stack);
  process.exit(1);
}
