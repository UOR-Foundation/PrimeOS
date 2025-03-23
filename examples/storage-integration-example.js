/**
 * PrimeOS Storage Integration Example
 * 
 * This example demonstrates the integration between the Storage module
 * and other PrimeOS components like Matrix and Neural Models.
 */

const Prime = require('../src');

/**
 * Example using SwappableMatrix with standard Matrix operations
 */
async function matrixExample() {
  console.log('===== Matrix Storage Integration Example =====');
  
  // Create a storage manager
  const storageManager = Prime.Storage.createManager();
  await storageManager.init();
  
  // Create a standard matrix using Prime.Math.Matrix
  const size = 500; // Not too large for an example, but large enough to show benefits
  console.log(`Creating a ${size}x${size} matrix...`);
  const matrix = Prime.Math.Matrix.create(size, size);
  
  // Fill with deterministic pattern
  console.log('Filling matrix with data...');
  for (let i = 0; i < size; i++) {
    for (let j = 0; j < size; j++) {
      matrix[i][j] = (i * j) % 100;
    }
  }
  
  // Store in swappable matrix format
  console.log('Converting to swappable matrix backed by storage...');
  const swappableMatrix = await Prime.Storage.createSwappableMatrixFromMatrix(
    storageManager,
    matrix,
    'large-matrix-example',
    {
      blockSize: 50,   // Use 50x50 blocks
      maxCachedBlocks: 5 // Only keep 5 blocks in memory at once
    }
  );
  
  // Free up original matrix to save memory
  console.log('Freeing original matrix from memory...');
  // In a real application, you might set it to null and let the garbage collector handle it
  
  // Access some values from the swappable matrix
  console.log('Accessing values from the swappable matrix...');
  console.log(`Value at (10, 10): ${await swappableMatrix.get(10, 10)}`);
  console.log(`Value at (100, 100): ${await swappableMatrix.get(100, 100)}`);
  console.log(`Value at (400, 400): ${await swappableMatrix.get(400, 400)}`);
  
  // Calculate partial trace to demonstrate performance
  console.log('Calculating partial trace (sum of diagonal elements)...');
  let trace = 0;
  for (let i = 0; i < 100; i++) { // Just do a subset for the example
    trace += await swappableMatrix.get(i, i);
  }
  console.log(`Partial trace (first 100 diagonal elements): ${trace}`);
  
  // Get a submatrix
  console.log('Extracting a submatrix...');
  const subMatrix = await swappableMatrix.submatrix(200, 200, 250, 250);
  console.log(`Submatrix dimensions: ${subMatrix.length}x${subMatrix[0].length}`);
  console.log(`Submatrix sample value at (10, 10): ${subMatrix[10][10]}`);
  
  // Convert part back to standard matrix for operations
  console.log('Converting a portion back to standard matrix for operations...');
  const standardMatrix = await swappableMatrix.toMatrix();
  
  // Calculate determinant of a small section (determinant is expensive for large matrices)
  const smallSection = Prime.Math.Matrix.create(3, 3);
  for (let i = 0; i < 3; i++) {
    for (let j = 0; j < 3; j++) {
      smallSection[i][j] = standardMatrix[i][j];
    }
  }
  
  const det = Prime.Math.Matrix.determinant(smallSection);
  console.log(`Determinant of 3x3 section: ${det}`);
  
  console.log('Matrix example completed successfully!');
}

/**
 * Example using Storage for Neural Model persistence and training
 */
async function neuralModelExample() {
  console.log('\n===== Neural Model Storage Integration Example =====');
  
  // Create a storage manager
  const storageManager = Prime.Storage.createManager();
  await storageManager.init();
  
  // Create a small neural network for XOR problem
  console.log('Creating neural model for XOR problem...');
  const model = new Prime.Neural.Model.NeuralModel({
    useTypedArrays: false, // For simplicity in the example
    layers: [
      {
        type: 'dense',
        inputSize: 2,
        outputSize: 4,
        activation: 'sigmoid'
      },
      {
        type: 'dense',
        inputSize: 4,
        outputSize: 1,
        activation: 'sigmoid'
      }
    ],
    optimizer: {
      type: 'adam',
      learningRate: 0.1
    }
  });
  
  // Compile the model
  model.compile({
    loss: 'mse',
    metric: 'accuracy'
  });
  
  // Store the untrained model
  console.log('Storing the untrained model...');
  const untrained_id = await Prime.Storage.storeModel(storageManager, model, 'xor-model-untrained');
  
  // Create XOR training data
  const training_data = {
    inputs: [
      [0, 0], [0, 1], [1, 0], [1, 1]
    ],
    outputs: [
      [0], [1], [1], [0]
    ]
  };
  
  // Store the training data
  console.log('Storing training data...');
  const inputs_id = await storageManager.store(training_data.inputs, 'xor-inputs');
  const outputs_id = await storageManager.store(training_data.outputs, 'xor-outputs');
  
  // Create a data provider from the stored data
  console.log('Creating data provider from stored data...');
  const dataProvider = Prime.Storage.createDataProvider(storageManager, {
    inputId: inputs_id,
    outputId: outputs_id,
    batchSize: 2,
    shuffle: true
  });
  
  // Train the model for a few iterations
  console.log('Training model with data from storage...');
  for (let epoch = 0; epoch < 100; epoch++) {
    let epochLoss = 0;
    
    // Train for one complete pass through the data (2 batches of size 2)
    for (let i = 0; i < 2; i++) {
      const batch = await dataProvider.nextBatch();
      const result = model.trainOnBatch(batch.inputs, batch.outputs);
      epochLoss += result.loss;
    }
    
    // Log every 10 epochs
    if (epoch % 10 === 0 || epoch === 99) {
      console.log(`Epoch ${epoch+1}/100, Loss: ${epochLoss/2}`);
    }
  }
  
  // Store the trained model
  console.log('Storing the trained model...');
  const trained_id = await Prime.Storage.storeModel(storageManager, model, 'xor-model-trained');
  
  // Test the trained model
  console.log('Testing the trained model...');
  const inputs = training_data.inputs;
  const expected = training_data.outputs.map(o => o[0] > 0.5 ? 1 : 0);
  
  console.log('XOR Results:');
  console.log('Input  | Expected | Prediction');
  console.log('-------------------------------');
  
  for (let i = 0; i < inputs.length; i++) {
    const input = inputs[i];
    const output = model.predict(input);
    const prediction = output[0] > 0.5 ? 1 : 0;
    console.log(`${input[0]}, ${input[1]}   | ${expected[i]}        | ${prediction} (${output[0].toFixed(4)})`);
  }
  
  // Load the model in a new instance to demonstrate persistence
  console.log('\nLoading the trained model from storage...');
  const loadedModel = await Prime.Storage.loadModel(storageManager, trained_id);
  
  console.log('Testing the loaded model:');
  console.log('Input  | Expected | Prediction');
  console.log('-------------------------------');
  
  for (let i = 0; i < inputs.length; i++) {
    const input = inputs[i];
    const output = loadedModel.predict(input);
    const prediction = output[0] > 0.5 ? 1 : 0;
    console.log(`${input[0]}, ${input[1]}   | ${expected[i]}        | ${prediction} (${output[0].toFixed(4)})`);
  }
  
  console.log('Neural model example completed successfully!');
}

/**
 * Run the examples
 */
async function runExamples() {
  try {
    await matrixExample();
    await neuralModelExample();
    
    console.log('\nAll examples completed successfully!');
    console.log('The storage module is now fully integrated with PrimeOS components.');
  } catch (error) {
    console.error('Error running examples:', error);
  }
}

// Run the examples
runExamples();