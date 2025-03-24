# Distributed Neural Network API

This document provides comprehensive API documentation for the distributed neural network functionality in PrimeOS.

## Overview

The distributed neural module enables training and inference across multiple nodes while maintaining neural coherence. It provides:

- Parameter synchronization strategies
- Error recovery mechanisms
- Model and data partitioning schemes
- Distributed training coordination
- Coherence validation

## Core Classes and Methods

### DistributedModel

`DistributedModel` extends the base neural model to support distributed training and inference.

#### Constructor

```javascript
const model = new Prime.Neural.Distributed.DistributedModel(config);
```

**Parameters:**
- `config` (Object): Configuration object with the following properties:
  - `syncStrategy` (String, optional): Synchronization strategy ('weighted_average', 'majority_vote', 'parameter_server'). Default: 'weighted_average'
  - `recoveryStrategy` (String, optional): Recovery strategy ('retry', 'conservative_merge', 'checkpoint_rollback'). Default: 'retry'
  - `partitionScheme` (String, optional): Partition scheme ('data_parallel', 'model_parallel', 'hybrid'). Default: 'data_parallel'
  - `checkpointInterval` (Number, optional): Interval between checkpoints in milliseconds. Default: 60000
  - `syncInterval` (Number, optional): Interval between synchronizations in milliseconds. Default: 10000
  - `coherenceThreshold` (Number, optional): Minimum coherence threshold for accepting updates. Default: 0.8
  - `nodes` (Array, optional): Array of node configurations.

#### Key Methods

##### setNodes

```javascript
model.setNodes(nodes);
```

**Parameters:**
- `nodes` (Array): Array of node configurations with properties:
  - `id` (String): Unique node identifier
  - `capacity` (Number): Relative computational capacity
  - `role` (String, optional): 'server', 'client', or 'auto'

##### train

```javascript
const result = await model.train(config);
```

**Parameters:**
- `config` (Object): Training configuration with the following properties:
  - `data` (Array): Training data
  - `epochs` (Number): Number of epochs to train
  - `batchSize` (Number, optional): Batch size for training. Default: 32
  - `distributionConfig` (Object, optional): Custom distribution configuration

**Returns:**
- `result` (Object): Training result with history and metrics

##### synchronize

```javascript
const result = await model.synchronize(options);
```

**Parameters:**
- `options` (Object, optional): Synchronization options
  - `force` (Boolean, optional): Force synchronization regardless of interval. Default: false
  - `strategy` (String, optional): Override the default synchronization strategy for this sync
  - `timeout` (Number, optional): Timeout in milliseconds for the synchronization

**Returns:**
- `result` (Object): Synchronization result with success indicator and metrics

##### createCheckpoint

```javascript
const checkpoint = model.createCheckpoint();
```

**Returns:**
- `checkpoint` (Object): Checkpoint object with model parameters and metadata

##### restoreCheckpoint

```javascript
const success = model.restoreCheckpoint(checkpointId);
```

**Parameters:**
- `checkpointId` (String): Identifier of the checkpoint to restore

**Returns:**
- `success` (Boolean): Whether the checkpoint was successfully restored

### Synchronization Strategies

#### weighted_average

Synchronizes parameters using a weighted average approach, with weights based on performance metrics, training time, coherence values, and other factors.

```javascript
model.setSyncStrategy('weighted_average', {
  performanceWeight: 0.6,
  coherenceWeight: 0.3,
  timeDecayFactor: 0.1,
  outlierThreshold: 3.0
});
```

#### majority_vote

Synchronizes parameters using a majority vote mechanism, with automatic clustering to determine the majority for continuous parameters and explicit voting for discrete parameters.

```javascript
model.setSyncStrategy('majority_vote', {
  outlierSigma: 2.0,
  minVotesRequired: 3,
  continuousClusterThreshold: 0.2
});
```

#### parameter_server

Implements a parameter server architecture where one node serves as the central parameter server while others act as clients.

```javascript
model.setSyncStrategy('parameter_server', {
  serverSelectionMethod: 'auto', // 'auto', 'fastest', 'most_stable'
  updateCompression: true,
  gradientAccumulation: true
});
```

### Recovery Strategies

#### retry

Implements exponential backoff with jitter for retrying failed operations.

```javascript
model.setRecoveryStrategy('retry', {
  maxRetries: 5,
  baseDelayMs: 100,
  maxDelayMs: 30000,
  jitterFactor: 0.3
});
```

#### conservative_merge

Attempts to merge divergent parameters with confidence-based weighting and special handling for highly divergent values.

```javascript
model.setRecoveryStrategy('conservative_merge', {
  divergenceThreshold: 0.5,
  maxDivergentParameterRatio: 0.1,
  fallbackToRollback: true
});
```

#### checkpoint_rollback

Maintains a rotating set of checkpoints and rolls back to the most recent valid checkpoint when failures occur.

```javascript
model.setRecoveryStrategy('checkpoint_rollback', {
  maxCheckpoints: 5,
  validateCheckpoints: true,
  validationBatchSize: 10
});
```

### Partition Schemes

#### data_parallel

Partitions the training data across nodes while keeping the full model on each node.

```javascript
model.setPartitionScheme('data_parallel', {
  balanceStrategy: 'capacity', // 'capacity', 'even', 'adaptive'
  shuffleData: true,
  rebalanceInterval: 5 // epochs
});
```

#### model_parallel

Partitions the neural network layers across nodes for coordinated processing.

```javascript
model.setPartitionScheme('model_parallel', {
  layerAssignmentStrategy: 'computational_balance',
  minimizeCommunication: true,
  pipelineBatchSize: 4
});
```

#### hybrid

Combines data and model parallelism for optimal performance.

```javascript
model.setPartitionScheme('hybrid', {
  dataParallelism: 0.7, // 70% data parallel, 30% model parallel
  prioritizeGpuForModelParallelism: true,
  dynamicAdjustment: true
});
```

## Events

The distributed neural module emits events that can be observed:

```javascript
model.on('sync:start', (data) => {
  console.log(`Starting synchronization: ${data.strategy}`);
});

model.on('sync:complete', (data) => {
  console.log(`Synchronization complete: ${data.timeMs}ms, coherence: ${data.coherence}`);
});

model.on('recovery:triggered', (data) => {
  console.log(`Recovery triggered: ${data.reason}, strategy: ${data.strategy}`);
});

model.on('checkpoint:created', (data) => {
  console.log(`Checkpoint created: ${data.id}, coherence: ${data.coherence}`);
});
```

## Example Usage

### Basic Usage

```javascript
// Create a distributed model
const model = new Prime.Neural.Distributed.DistributedModel({
  syncStrategy: 'weighted_average',
  recoveryStrategy: 'retry',
  partitionScheme: 'data_parallel'
});

// Add layers
model.addLayer({
  type: 'dense',
  inputSize: 10,
  outputSize: 20,
  activation: 'relu'
});

model.addLayer({
  type: 'dense',
  outputSize: 1,
  activation: 'sigmoid'
});

// Configure nodes
model.setNodes([
  { id: 'node1', capacity: 1.0, role: 'auto' },
  { id: 'node2', capacity: 0.8, role: 'auto' },
  { id: 'node3', capacity: 0.5, role: 'auto' }
]);

// Compile model
model.compile({
  loss: 'binaryCrossentropy',
  optimizer: {
    type: 'adam',
    learningRate: 0.001
  }
});

// Train model
const result = await model.train({
  data: trainingData,
  epochs: 10,
  batchSize: 32
});

// Create checkpoint
const checkpoint = model.createCheckpoint();

// Make prediction
const prediction = model.predict(inputData);
```

### Advanced Configuration

```javascript
// Create a model with advanced configuration
const model = new Prime.Neural.Distributed.DistributedModel({
  syncStrategy: 'majority_vote',
  syncOptions: {
    outlierSigma: 2.5,
    minVotesRequired: 2
  },
  recoveryStrategy: 'conservative_merge',
  recoveryOptions: {
    divergenceThreshold: 0.3,
    fallbackToRollback: true
  },
  partitionScheme: 'hybrid',
  partitionOptions: {
    dataParallelism: 0.6,
    dynamicAdjustment: true
  },
  coherenceConfig: {
    enabled: true,
    minThreshold: 0.85,
    checkFrequency: 50
  },
  checkpointInterval: 120000, // 2 minutes
  syncInterval: 5000 // 5 seconds
});

// Add event listeners
model.on('coherence:violation', (data) => {
  console.log(`Coherence violation detected: ${data.value} < ${data.threshold}`);
  console.log(`Location: ${data.layerIndex}, parameter type: ${data.parameterType}`);
});

// Set custom synchronization handler
model.setCustomSyncHandler(async (nodes, params, options) => {
  // Custom synchronization logic
  return customSyncResult;
});
```

## Performance Considerations

For optimal performance with distributed neural networks:

1. Match partition scheme to your hardware topology
2. Adjust synchronization frequency based on network bandwidth
3. Use differential updates to minimize communication overhead
4. Consider model complexity when choosing between data and model parallelism
5. Set appropriate coherence thresholds based on model size and complexity
6. Enable checkpoint validation for critical workloads
7. Use hybrid partitioning for very large models

## Error Handling

The distributed neural module uses structured error handling:

```javascript
try {
  await model.synchronize();
} catch (error) {
  if (error instanceof Prime.Neural.Errors.SynchronizationError) {
    console.error(`Synchronization failed: ${error.message}`);
    console.error(`Affected nodes: ${error.metadata.failedNodes.join(', ')}`);
  } else if (error instanceof Prime.Neural.Errors.CoherenceViolationError) {
    console.error(`Coherence violation: ${error.message}`);
    console.error(`Violation details: ${JSON.stringify(error.metadata.violations)}`);
  } else {
    console.error(`Unexpected error: ${error.message}`);
  }
}
```