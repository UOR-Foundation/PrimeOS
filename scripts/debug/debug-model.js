/**
 * Debug neural model creation
 */

// Import the Prime object from core
const Prime = require('./src/core.js');

// Load mathematics module
require('./src/mathematics.js');
Prime.Math = Prime.Math || {};

// Explicitly import math modules
require('./src/math/vector.js');
require('./src/math/matrix.js');

// Import other required modules
require('./src/coherence.js');
require('./src/distributed/index.js');
require('./src/distributed/coherence.js');
require('./src/distributed/cluster/index.js');
require('./src/neural/index.js');
require('./src/neural/distributed/index.js');

// Monkey patch Matrix.create for debugging
const originalCreate = Prime.Math.Matrix.create;
Prime.Math.Matrix.create = function (rows, cols, initialValue = 0) {
  console.log(`Matrix.create called with rows=${rows}, cols=${cols}`);
  console.log('Call stack:', new Error().stack);
  return originalCreate.call(this, rows, cols, initialValue);
};

// Try to create a regular NeuralModel first
console.log('\nCreating regular NeuralModel:');
try {
  const model = new Prime.Neural.Model.NeuralModel({
    inputSize: 10,
    layers: [
      {
        type: 'dense',
        outputSize: 5,
        activation: 'relu',
        initParams: {
          distribution: 'zeros',
        },
      },
    ],
  });

  console.log('Regular model created successfully!');
  console.log('Model has', model.layers.length, 'layers');
  console.log(
    'Layer weights dimensions:',
    model.layers[0].weights.length,
    'x',
    model.layers[0].weights[0].length,
  );
} catch (error) {
  console.error('NeuralModel creation failed:', error.message);
  console.error('Error stack:', error.stack);
}

// Now try to create a DistributedNeuralModel
console.log('\nCreating DistributedNeuralModel:');
try {
  const model = new Prime.Neural.Distributed.DistributedNeuralModel({
    inputSize: 10,
    layers: [
      {
        type: 'dense',
        outputSize: 5,
        activation: 'relu',
        initParams: {
          distribution: 'zeros',
        },
      },
    ],
    distributed: {
      enabled: true,
      partitionScheme: 'layer-wise',
      syncFrequency: 2,
    },
  });

  console.log('Distributed model created successfully!');
  console.log('Model has', model.layers.length, 'layers');
  console.log(
    'Layer weights dimensions:',
    model.layers[0].weights.length,
    'x',
    model.layers[0].weights[0].length,
  );
} catch (error) {
  console.error('DistributedNeuralModel creation failed:', error.message);
  console.error('Error stack:', error.stack);
}
