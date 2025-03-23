/**
 * Unit tests for PrimeOS Distributed Computation Module - Cluster components
 */

const Prime = require("../../../src");
const { assertions, mocking } = require("../../utils");

describe("PrimeOS Distributed Computation Module - Cluster", () => {
  describe("ClusterNode", () => {
    test("creates a cluster node with correct properties", () => {
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
  });

  describe("ClusterManager", () => {
    test("creates a cluster manager with correct properties", () => {
      const manager = new Prime.Distributed.Cluster.ClusterManager({
        maxNodes: 5,
        discoveryMethod: "local",
      });

      expect(manager instanceof Prime.Distributed.Cluster.ClusterManager).toBe(
        true,
      );
      expect(manager.config.maxNodes).toBe(5);
      expect(manager.nodes.size).toBe(0);
    });

    test("adds and manages nodes correctly", () => {
      const manager = new Prime.Distributed.Cluster.ClusterManager({
        maxNodes: 5,
        discoveryMethod: "local",
      });

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

    test("handles task submission correctly", () => {
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

      // Submit task and verify it's handled
      const promise = manager.submitTask(task);
      expect(promise instanceof Promise).toBe(true);
    });
  });
});
