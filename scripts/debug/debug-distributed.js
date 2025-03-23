/**
 * Debug file to understand DistributedNeuralModel creation issue
 */

// Import the Prime object from core
const Prime = require('./src/core.js');

// Load mathematics module
require('./src/mathematics.js');
Prime.Math = Prime.Math || {};

// Load math modules
require('./src/math/vector.js');
require('./src/math/matrix.js');

// Print diagnostics
console.log('Math module diagnostics:');
console.log('- Prime.Math exists:', !!Prime.Math);
console.log('- Prime.Math.Vector exists:', !!Prime.Math.Vector);
console.log('- Prime.Math.Matrix exists:', !!Prime.Math.Matrix);

// Test Matrix creation
try {
  console.log('\nAttempting to create a matrix with dimensions (5, 10):');
  const matrix = Prime.Math.Matrix.create(5, 10);
  console.log('Matrix creation successful!');
  console.log('Matrix dimensions:', matrix.length, 'x', matrix[0].length);
  console.log('First element:', matrix[0][0]);
} catch (error) {
  console.error('Matrix creation failed:', error.message);
  console.error('Error details:', error);
}

// Load remaining required modules
console.log('\nLoading additional modules:');
try {
  require('./src/coherence.js');
  console.log('- Coherence module loaded');

  require('./src/distributed/index.js');
  console.log('- Distributed module loaded');

  require('./src/distributed/coherence.js');
  console.log('- Distributed.Coherence module loaded');

  require('./src/distributed/cluster/index.js');
  console.log('- Distributed.Cluster module loaded');

  // Now load neural modules after everything else is ready
  require('./src/neural/index.js');
  console.log('- Neural module loaded');

  require('./src/neural/distributed/index.js');
  console.log('- Neural.Distributed module loaded');
} catch (error) {
  console.error('Module loading failed:', error.message);
  console.error('Error stack:', error.stack);
}

// Now let's try to create a DistributedNeuralModel
console.log('\nCreating DistributedNeuralModel:');
try {
  if (
    !Prime.Neural ||
    !Prime.Neural.Distributed ||
    !Prime.Neural.Distributed.DistributedNeuralModel
  ) {
    console.error('DistributedNeuralModel class not found in:', Prime.Neural);
  } else {
    const modelConfig = {
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
    };

    const model = new Prime.Neural.Distributed.DistributedNeuralModel(
      modelConfig,
    );

    console.log('Model created successfully!');
    console.log('Model has', model.layers.length, 'layers');
    console.log('Layer input size:', model.layers[0].inputSize);
    console.log('Layer output size:', model.layers[0].outputSize);
    console.log('Model distributed config:', model.distributedConfig);
  }
} catch (error) {
  console.error('DistributedNeuralModel creation failed:', error.message);
  console.error('Error stack:', error.stack);
}
