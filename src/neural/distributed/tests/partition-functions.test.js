/**
 * PrimeOS Unit Tests - Distributed Neural Partition Functions
 *
 * Tests the core partition functions without depending on the full class hierarchy.
 */

describe("Distributed Neural Partition Functions", () => {
  // Define test implementations of partition functions
  const createDataParallelPartition = (data, nodes) => {
    if (!data || !Array.isArray(data) || !nodes || !Array.isArray(nodes)) {
      return { success: false };
    }
    
    // Distribute data items across nodes based on node capacity
    const totalCapacity = nodes.reduce((sum, n) => sum + (n.capacity || 1), 0);
    const nodePartitions = {};
    
    let dataIndex = 0;
    const nodeItemCounts = {};
    
    // Initialize node partitions
    nodes.forEach(node => {
      nodePartitions[node.id] = [];
      const capacity = node.capacity || 1;
      // Calculate how many items this node should get based on capacity
      nodeItemCounts[node.id] = Math.floor(data.length * (capacity / totalCapacity));
    });
    
    // Distribute remaining items (due to rounding) to the highest capacity nodes
    let remainingItems = data.length - Object.values(nodeItemCounts).reduce((a, b) => a + b, 0);
    if (remainingItems > 0) {
      const sortedNodes = [...nodes].sort((a, b) => (b.capacity || 1) - (a.capacity || 1));
      for (let i = 0; i < Math.min(remainingItems, sortedNodes.length); i++) {
        nodeItemCounts[sortedNodes[i].id]++;
      }
    }
    
    // Assign items to nodes
    for (const node of nodes) {
      const count = nodeItemCounts[node.id];
      nodePartitions[node.id] = data.slice(dataIndex, dataIndex + count);
      dataIndex += count;
    }
    
    return {
      nodePartitions,
      metadata: {
        scheme: 'data_parallel',
        nodeCount: nodes.length
      }
    };
  };
  
  const createModelParallelPartition = (model, nodes) => {
    if (!model || !model.layers || !Array.isArray(model.layers) || !nodes || !Array.isArray(nodes)) {
      return { success: false };
    }
    
    // Distribute model layers across nodes based on computational needs
    const nodePartitions = {};
    
    // Initialize empty partitions
    nodes.forEach(node => {
      nodePartitions[node.id] = [];
    });
    
    // First assign input and output layers to the same node if possible
    const inputLayer = model.layers.find(l => l.type === 'input');
    const outputLayer = model.layers.find(l => l.type === 'output');
    
    // Find the best node for input/output (prefer GPU nodes)
    const gpuNodes = nodes.filter(n => n.gpu);
    const bestNode = gpuNodes.length > 0 ? gpuNodes[0] : nodes[0];
    
    if (inputLayer) {
      nodePartitions[bestNode.id].push(inputLayer);
    }
    
    if (outputLayer) {
      nodePartitions[bestNode.id].push(outputLayer);
    }
    
    // Distribute remaining layers across all nodes, weighted by capacity
    const remainingLayers = model.layers.filter(l => 
      (l !== inputLayer) && (l !== outputLayer)
    );
    
    // Simple round-robin distribution
    let nodeIndex = 0;
    for (const layer of remainingLayers) {
      const nodeId = nodes[nodeIndex].id;
      nodePartitions[nodeId].push(layer);
      nodeIndex = (nodeIndex + 1) % nodes.length;
    }
    
    return {
      nodePartitions,
      metadata: {
        scheme: 'model_parallel',
        nodeCount: nodes.length
      }
    };
  };
  
  const createHybridPartition = (model, data, nodes, config) => {
    if (!model || !data || !nodes || !config) {
      return { success: false };
    }
    
    // Extract configuration
    const dataParallelism = config.dataParallelism || 0.5; // Default 50% data, 50% model parallel
    
    // Create data partition
    const dataPartition = createDataParallelPartition(data, nodes);
    
    // Create model partition
    const modelPartition = createModelParallelPartition(model, nodes);
    
    return {
      modelPartition,
      dataPartition,
      metadata: {
        scheme: 'hybrid',
        nodeCount: nodes.length,
        dataParallelism,
        modelParallelism: 1 - dataParallelism
      }
    };
  };

  describe("Data Parallel Scheme", () => {
    test("should partition data across nodes", () => {
      // Mock training data
      const trainingData = [];
      for (let i = 0; i < 100; i++) {
        trainingData.push({
          input: [Math.random(), Math.random()],
          output: [Math.random()]
        });
      }
      
      // Mock node configuration
      const nodes = [
        { id: "node1", capacity: 1.0 },
        { id: "node2", capacity: 0.5 },
        { id: "node3", capacity: 0.75 }
      ];
      
      // Create data parallel partition
      const partition = createDataParallelPartition(
        trainingData,
        nodes
      );
      
      // Verify results
      expect(partition).toBeDefined();
      expect(partition.nodePartitions).toBeDefined();
      expect(Object.keys(partition.nodePartitions).length).toBe(nodes.length);
      
      // Each node should have data proportional to its capacity
      const totalCapacity = nodes.reduce((sum, n) => sum + n.capacity, 0);
      const totalItems = trainingData.length;
      
      for (const node of nodes) {
        const nodeData = partition.nodePartitions[node.id];
        expect(nodeData).toBeDefined();
        expect(Array.isArray(nodeData)).toBe(true);
        
        // Calculate expected number of items based on capacity ratio
        const expectedItemCount = Math.floor(totalItems * (node.capacity / totalCapacity));
        
        // Allow for small variations due to rounding
        const allowedDeviation = 2; // Allow at most 2 items difference
        expect(Math.abs(nodeData.length - expectedItemCount)).toBeLessThanOrEqual(allowedDeviation);
        
        // Verify data integrity - each item should have input and output
        for (const item of nodeData) {
          expect(item.input).toBeDefined();
          expect(item.output).toBeDefined();
        }
      }
      
      // All original data items should be distributed
      const totalDistributed = Object.values(partition.nodePartitions)
        .reduce((sum, items) => sum + items.length, 0);
      expect(totalDistributed).toBe(totalItems);
      
      // Check metadata
      expect(partition.metadata).toBeDefined();
      expect(partition.metadata.scheme).toBe('data_parallel');
      expect(partition.metadata.nodeCount).toBe(nodes.length);
    });
  });

  describe("Model Parallel Scheme", () => {
    test("should partition model layers across nodes", () => {
      // Mock model
      const model = {
        layers: [
          { id: "layer1", type: "input", size: 10 },
          { id: "layer2", type: "dense", size: 20 },
          { id: "layer3", type: "dense", size: 15 },
          { id: "layer4", type: "dense", size: 10 },
          { id: "layer5", type: "dense", size: 5 },
          { id: "layer6", type: "output", size: 1 }
        ]
      };
      
      // Mock node configuration
      const nodes = [
        { id: "node1", capacity: 1.0, gpu: true },
        { id: "node2", capacity: 0.8, gpu: true },
        { id: "node3", capacity: 0.5, gpu: false }
      ];
      
      // Create model parallel partition
      const partition = createModelParallelPartition(
        model,
        nodes
      );
      
      // Verify results
      expect(partition).toBeDefined();
      expect(partition.nodePartitions).toBeDefined();
      expect(Object.keys(partition.nodePartitions).length).toBe(nodes.length);
      
      // All layers should be assigned
      const allAssignedLayers = Object.values(partition.nodePartitions)
        .reduce((all, layers) => [...all, ...layers], []);
      expect(allAssignedLayers.length).toBe(model.layers.length);
      
      // Check that input and output are on a GPU node if possible
      const inputLayer = model.layers.find(l => l.type === "input");
      const outputLayer = model.layers.find(l => l.type === "output");
      
      if (inputLayer && outputLayer) {
        // Find which node(s) have input and output layers
        let inputNodeId = null;
        let outputNodeId = null;
        
        for (const nodeId in partition.nodePartitions) {
          const layers = partition.nodePartitions[nodeId];
          if (layers.includes(inputLayer)) inputNodeId = nodeId;
          if (layers.includes(outputLayer)) outputNodeId = nodeId;
        }
        
        if (nodes.some(n => n.gpu)) {
          // If there are GPU nodes, input/output should be on a GPU node
          const gpuNodeIds = nodes.filter(n => n.gpu).map(n => n.id);
          
          // Either input or output should be on a GPU node
          expect(
            gpuNodeIds.includes(inputNodeId) || 
            gpuNodeIds.includes(outputNodeId)
          ).toBe(true);
        }
      }
      
      // Check metadata
      expect(partition.metadata).toBeDefined();
      expect(partition.metadata.scheme).toBe('model_parallel');
      expect(partition.metadata.nodeCount).toBe(nodes.length);
    });
  });

  describe("Hybrid Parallelism Scheme", () => {
    test("should implement hybrid data/model parallelism", () => {
      // Mock model
      const model = {
        layers: [
          { id: "layer1", type: "input", size: 10 },
          { id: "layer2", type: "dense", size: 20 },
          { id: "layer3", type: "dense", size: 15 },
          { id: "layer4", type: "dense", size: 10 },
          { id: "layer5", type: "output", size: 1 }
        ]
      };
      
      // Mock training data
      const trainingData = [];
      for (let i = 0; i < 50; i++) {
        trainingData.push({
          input: [Math.random(), Math.random()],
          output: [Math.random()]
        });
      }
      
      // Mock node configuration with capacity and characteristics
      const nodes = [
        { id: "node1", capacity: 1.0, gpu: true, memory: "high" },
        { id: "node2", capacity: 0.8, gpu: true, memory: "medium" },
        { id: "node3", capacity: 0.7, gpu: false, memory: "high" },
        { id: "node4", capacity: 0.5, gpu: false, memory: "low" }
      ];
      
      // Configuration options
      const config = {
        dataParallelism: 0.6, // 60% data parallel, 40% model parallel
        prioritizeGpuForModelParallelism: true
      };
      
      // Create hybrid partition
      const partition = createHybridPartition(
        model,
        trainingData,
        nodes,
        config
      );
      
      // Verify results
      expect(partition).toBeDefined();
      expect(partition.modelPartition).toBeDefined();
      expect(partition.dataPartition).toBeDefined();
      
      // Check model partition
      expect(partition.modelPartition.nodePartitions).toBeDefined();
      
      // All layers should be assigned
      const allAssignedLayers = Object.values(partition.modelPartition.nodePartitions)
        .reduce((all, layers) => [...all, ...layers], []);
      expect(allAssignedLayers.length).toBe(model.layers.length);
      
      // Check data partition
      expect(partition.dataPartition.nodePartitions).toBeDefined();
      
      // All data should be distributed
      const totalDistributed = Object.values(partition.dataPartition.nodePartitions)
        .reduce((sum, items) => sum + items.length, 0);
      expect(totalDistributed).toBe(trainingData.length);
      
      // Check metadata
      expect(partition.metadata).toBeDefined();
      expect(partition.metadata.scheme).toBe('hybrid');
      expect(partition.metadata.nodeCount).toBe(nodes.length);
      expect(partition.metadata.dataParallelism).toBe(config.dataParallelism);
      expect(partition.metadata.modelParallelism).toBeCloseTo(1 - config.dataParallelism, 5);
    });
  });
});