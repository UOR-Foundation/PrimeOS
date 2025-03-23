/**
 * Debug file to understand Matrix creation issue
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

// Check if the Neural modules are properly loading
console.log('\nTesting Neural module loading:');
try {
  require('./src/neural/index.js');
  console.log('- Neural module loaded successfully');

  require('./src/neural/layer/index.js');
  console.log('- Neural.Layer module loaded successfully');

  require('./src/neural/model/index.js');
  console.log('- Neural.Model module loaded successfully');

  require('./src/neural/distributed/index.js');
  console.log('- Neural.Distributed module loaded successfully');

  console.log('\nTesting NeuralLayer creation:');
  const layerConfig = {
    inputSize: 10,
    outputSize: 5,
    activation: 'relu',
    initParams: {
      distribution: 'zeros',
    },
  };

  const NeuralLayer = Prime.Neural.Layer.NeuralLayer;
  if (!NeuralLayer) {
    console.error('NeuralLayer class not found');
  } else {
    try {
      const layer = new NeuralLayer(layerConfig);
      console.log('Layer created successfully!');
      console.log(
        'Layer weights dimensions:',
        layer.weights.length,
        'x',
        layer.weights[0].length,
      );
      console.log('Layer biases length:', layer.biases.length);
    } catch (error) {
      console.error('Layer creation failed:', error.message);
      console.error('Error stack:', error.stack);
    }
  }
} catch (error) {
  console.error('Neural module loading failed:', error.message);
  console.error('Error stack:', error.stack);
}
