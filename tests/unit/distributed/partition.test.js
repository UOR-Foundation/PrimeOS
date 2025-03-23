/**
 * Unit tests for PrimeOS Distributed Computation Module - Partition components
 */

const Prime = require("../../../src");
const { assertions, mocking } = require("../../utils");

describe("PrimeOS Distributed Computation Module - Partition", () => {
  describe("PartitionScheme", () => {
    test("creates a partition scheme with correct properties", () => {
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

      expect(
        scheme instanceof Prime.Distributed.Partition.PartitionScheme,
      ).toBe(true);
      expect(scheme.type).toBe(
        Prime.Distributed.Partition.PartitionType.LAYER_WISE,
      );
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
  });

  describe("DistributedLayer", () => {
    test("creates a distributed layer with correct properties", () => {
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

      expect(
        layer instanceof Prime.Distributed.Partition.DistributedLayer,
      ).toBe(true);
      expect(layer.id).toBe("dist_layer_1");
      expect(Array.isArray(layer.nodeIds)).toBe(true);
      expect(layer.nodeIds.length).toBe(2);

      // Test layer metrics
      const metrics = layer.getMetrics();
      expect(typeof metrics).toBe("object");
      expect(metrics.completedForwardPasses).toBe(0);

      // Test layer partition scheme
      const scheme = layer.getPartitionScheme();
      expect(
        scheme instanceof Prime.Distributed.Partition.PartitionScheme,
      ).toBe(true);
    });

    test("performs distributed computation correctly", async () => {
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
});
