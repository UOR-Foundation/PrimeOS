# PrimeOS Distributed Package API

## Overview

The PrimeOS Distributed package provides robust tools for distributed neural network training, inference, and coordination across multiple nodes. The modules in this package are designed to maintain coherence, provide secure communication, and efficiently distribute computational workloads.

## Namespaces

The distributed package is available under the following namespaces:

- `Prime.Distributed` - Primary namespace (recommended)
- `Prime.distributed` - Legacy namespace (for backward compatibility)

## Core Components

### Communication

The communication module handles secure message passing between nodes in a distributed system.

#### CommunicationChannel

```javascript
// Create a communication channel
const channel = new Prime.Distributed.Communication.CommunicationChannel({
  nodeId: 'node-1',
  endpoint: 'tcp://example.com:9000',
  securityLevel: 'high'
});

// Send message
await channel.sendMessage({
  type: 'data',
  payload: { tensors: [...] }
});

// Listen for messages
channel.on('message', (msg) => {
  console.log('Received:', msg);
});
```

#### MessageRouter

```javascript
// Create a message router
const router = new Prime.Distributed.Communication.MessageRouter({
  localNodeId: 'node-1',
  knownNodes: ['node-2', 'node-3'],
  routingStrategy: 'shortest-path'
});

// Register routes
router.registerRoute('node-2', { via: 'direct', channel: channel1 });
router.registerRoute('node-3', { via: 'node-2', channel: channel1 });

// Route a message
await router.routeMessage('node-3', { 
  type: 'model-update', 
  data: { gradients: [...] }
});
```

#### CommunicationHub

```javascript
// Create a communication hub
const hub = new Prime.Distributed.Communication.CommunicationHub({
  nodeId: 'coordinator',
  securityOptions: {
    encryptionRequired: true,
    authenticationRequired: true
  }
});

// Add channels
hub.addChannel(channel1);
hub.addChannel(channel2);

// Broadcast a message to all connected nodes
await hub.broadcast({
  type: 'synchronize',
  timestamp: Date.now()
});

// Get cluster status
const status = hub.getClusterStatus();
```

### Coherence

The coherence module maintains mathematical integrity across distributed computations.

#### DistributedCoherenceManager

```javascript
// Create a coherence manager
const coherenceManager = new Prime.Distributed.Coherence.Core.Manager({
  strictChecking: true,
  thresholds: {
    numerical: 1e-7,
    gradient: 10.0,
    synchronization: 0.01
  }
});

// Check layer coherence
const result = coherenceManager.checkLayerCoherence(layer, {
  isDistributed: true,
  globalParams: globalParameters,
  gradients: currentGradients
});

if (!result.isCoherent) {
  console.warn('Coherence violation detected:', result.violations);
  // Apply corrections
  const corrected = coherenceManager.applyCoherenceCorrections(layer, result);
  // Use corrected layer
}
```

#### Coherence Violations Detection

```javascript
// Detect gradient violations
const gradientCheck = Prime.Distributed.Coherence.Violations.Detector.detectGradientViolations(
  gradients, 
  { explodinThreshold: 5.0, vanishingThreshold: 1e-10 }
);

if (gradientCheck.isExploding) {
  console.warn('Exploding gradient detected:', gradientCheck.stats.maxAbsGradient);
}

// Detect numerical violations
const numericalCheck = Prime.Distributed.Coherence.Violations.Detector.detectNumericalViolations(
  tensor,
  1e-7 // precision threshold
);

if (numericalCheck.hasViolations) {
  console.warn(`Found ${numericalCheck.violationsCount} numerical violations`);
}
```

#### Coherence Recovery

```javascript
// Get recovery recommendations for incoherent state
const recovery = Prime.Distributed.Coherence.Recovery.Manager.recommendRecoveryActions(
  coherenceResult
);

console.log(`Recommended strategy: ${recovery.strategy}`);

// Apply numerical corrections
const corrected = Prime.Distributed.Coherence.Recovery.Manager.applyNumericalCorrections(
  tensor,
  {
    threshold: 1e-7,
    maxValue: 1e6
  }
);

// Apply gradient clipping
const clippedGradients = Prime.Distributed.Coherence.Recovery.Manager.applyGradientClipping(
  gradients,
  {
    clipMethod: 'value',
    clipValue: 5.0
  }
);
```

### Cluster

The cluster module manages distributed compute resources and task execution.

#### ClusterManager

```javascript
// Create a cluster manager
const clusterManager = new Prime.Distributed.Cluster.Manager({
  nodeId: 'master-node',
  maxNodes: 10,
  taskQueueSize: 100
});

// Add nodes to the cluster
clusterManager.addNode({
  id: 'worker-1',
  capabilities: ['gpu', 'high-memory'],
  status: 'ready'
});

// Submit a task for distributed execution
const taskResult = await clusterManager.submitTask({
  type: 'training-iteration',
  data: { batchId: 42, learningRate: 0.01 },
  targetNode: 'worker-1' // optional, otherwise auto-assigned
});

// Get cluster status
const status = clusterManager.getClusterStatus();
console.log(`Active nodes: ${status.activeNodeCount}`);
```

#### TaskQueue

```javascript
// Create a task queue
const taskQueue = new Prime.Distributed.Cluster.TaskQueue({
  maxSize: 1000,
  priorityLevels: 5
});

// Add tasks
taskQueue.enqueue({
  id: 'task-1',
  type: 'inference',
  priority: 2,
  data: { input: [...] }
});

// Process tasks
const nextTask = taskQueue.dequeue();
if (nextTask) {
  // Process the task
  processTask(nextTask);
}

// Get queue statistics
const stats = taskQueue.getStatistics();
console.log(`Tasks waiting: ${stats.queuedCount}`);
```

#### ClusterNode

```javascript
// Create a cluster node
const node = new Prime.Distributed.Cluster.Node({
  id: 'worker-2',
  capabilities: {
    compute: 'gpu',
    memory: 16,
    storage: 1000
  }
});

// Register with manager
node.connect('master-node');

// Register task handlers
node.registerTaskHandler('training-iteration', async (task) => {
  // Process training iteration
  return { loss: 0.05, accuracy: 0.92 };
});

// Start the node
node.start();
```

### Partition

The partition module handles distribution strategies for neural network layers and data.

#### PartitionManager

```javascript
// Create a partition manager
const partitionManager = new Prime.Distributed.Partition.Manager({
  networkDefinition: model,
  nodeCount: 4,
  strategy: 'layer-wise'
});

// Create a partition scheme
const scheme = partitionManager.createPartitionScheme();

// Apply the scheme
const partitionedModel = partitionManager.applyPartitioning(model, scheme);

// Get node assignment for a layer
const nodeAssignment = scheme.getNodeForLayer('dense_1');
```

## Error Handling

All distributed components use the standard Prime error hierarchy:

```javascript
try {
  // Some distributed operation
} catch (error) {
  if (error instanceof Prime.ValidationError) {
    // Handle validation errors
  } else if (error instanceof Prime.InvalidOperationError) {
    // Handle invalid operations
  } else if (error instanceof Prime.CoherenceError) {
    // Handle coherence violations
  } else if (error instanceof Prime.CommunicationError) {
    // Handle communication failures
  } else {
    // Handle other errors
  }
}
```

## Event System

All distributed components emit events that can be monitored:

```javascript
// Listen for coherence events
Prime.EventBus.subscribe('distributed:coherence:violation', (event) => {
  console.log('Coherence violation:', event);
});

// Listen for communication events
Prime.EventBus.subscribe('distributed:communication:connected', (event) => {
  console.log('Node connected:', event.nodeId);
});

// Listen for cluster events
Prime.EventBus.subscribe('distributed:cluster:task-completed', (event) => {
  console.log('Task completed:', event.taskId);
});
```

## Best Practices

1. **Namespace Usage**: Always use the `Prime.Distributed` namespace (capitalized) for new code. The lowercase `Prime.distributed` namespace is maintained for backward compatibility.

2. **Error Handling**: Always use specific Prime error classes for error handling. Avoid generic errors.

3. **Coherence Checking**: For distributed neural networks, always use coherence checks after operations that modify tensors.

4. **Security**: Always enable encryption for communication channels in production environments.

5. **Event-Driven Architecture**: Use the event system for monitoring and coordination rather than polling.

6. **Resource Management**: Remember to close channels and release resources when they're no longer needed:

```javascript
// Proper cleanup
channel.close();
clusterManager.shutdown();
```

7. **Testing**: Use mock implementations for testing by setting the appropriate flags:

```javascript
// For testing
const channel = new Prime.Distributed.Communication.CommunicationChannel({
  nodeId: 'test-node',
  mockMode: true
});
```

## Migration Guide

If you're migrating from the legacy lowercase namespace:

```javascript
// Old code (deprecated)
const manager = new Prime.distributed.coherence.CoherenceCore.Manager();

// New code (recommended)
const manager = new Prime.Distributed.Coherence.Core.Manager();
```

The legacy namespace will continue to work but is not recommended for new code.