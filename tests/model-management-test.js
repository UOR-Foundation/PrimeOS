/**
 * PrimeOS JavaScript Library - Model Management Tests
 * Tests for the neural network model management functionality
 */

const Prime = require('../src/neural/index');
const assert = require('assert');

describe('Neural Network Model Management', () => {
  describe('Model Creation and Structure', () => {
    it('should create a model using ModelBuilder', () => {
      const model = Prime.Neural.Model.ModelBuilder.sequential([
        { type: 'dense', inputSize: 5, units: 10, activation: 'relu' },
        { type: 'dense', units: 3, activation: 'sigmoid' }
      ]);
      
      assert.ok(model);
      assert.equal(model.layers.length, 2);
      assert.equal(model.layers[0].inputSize, 5);
      assert.equal(model.layers[0].outputSize, 10);
      assert.equal(model.layers[0].activation, 'relu');
      assert.equal(model.layers[1].inputSize, 10);
      assert.equal(model.layers[1].outputSize, 3);
      assert.equal(model.layers[1].activation, 'sigmoid');
    });
    
    it('should create a model using fluent builder API', () => {
      const builder = new Prime.Neural.Model.ModelBuilder();
      
      const model = builder
        .input(4)
        .dense({ units: 8, activation: 'relu' })
        .dense({ units: 2, activation: 'sigmoid' })
        .withOptimizer('adam', { learningRate: 0.001 })
        .withLoss('binaryCrossEntropy')
        .build();
      
      assert.ok(model);
      assert.equal(model.layers.length, 2);
      assert.equal(model.layers[0].inputSize, 4);
      assert.equal(model.layers[1].outputSize, 2);
      assert.ok(model.optimizer);
      assert.equal(model.optimizer.learningRate, 0.001);
      assert.ok(model.compiled);
    });
    
    it('should create predefined model architectures', () => {
      const mlpModel = Prime.Neural.Model.ModelBuilder.fromArchitecture('mlp', {
        inputSize: 10,
        outputSize: 2
      });
      
      assert.ok(mlpModel);
      assert.equal(mlpModel.layers.length, 3);
      assert.equal(mlpModel.layers[0].inputSize, 10);
      assert.equal(mlpModel.layers[2].outputSize, 2);
      
      const cnnModel = Prime.Neural.Model.ModelBuilder.fromArchitecture('cnn', {
        inputSize: 784,
        outputSize: 10
      });
      
      assert.ok(cnnModel);
      assert.ok(cnnModel.layers.length > 3);
      assert.equal(cnnModel.layers[cnnModel.layers.length - 1].outputSize, 10);
    });
    
    it('should support model compilation', () => {
      // Create model
      const model = new Prime.Neural.Model.NeuralModel();
      
      // Add layers
      model.addLayer({
        type: 'dense',
        inputSize: 3,
        outputSize: 2,
        activation: 'sigmoid'
      });
      
      // Set optimizer
      model.setOptimizer('sgd', { learningRate: 0.01 });
      
      // Compile
      model.compile({ loss: 'mse', metric: 'accuracy' });
      
      assert.ok(model.compiled);
      assert.ok(model.lossFunction);
      assert.ok(model.metric);
    });
  });
  
  describe('Forward and Backward Pass', () => {
    it('should perform forward pass', () => {
      const model = Prime.Neural.Model.ModelBuilder.sequential([
        { type: 'dense', inputSize: 2, units: 3, activation: 'sigmoid' },
        { type: 'dense', units: 1, activation: 'sigmoid' }
      ]);
      
      const input = [0.5, 0.8];
      const { output } = model.forward(input);
      
      assert.ok(output);
      assert.equal(output.length, 1);
      assert.ok(output[0] >= 0 && output[0] <= 1); // Sigmoid output
    });
    
    it('should compute gradients with backward pass', () => {
      const model = Prime.Neural.Model.ModelBuilder.sequential([
        { type: 'dense', inputSize: 2, units: 3, activation: 'sigmoid' },
        { type: 'dense', units: 1, activation: 'sigmoid' }
      ], {
        optimizer: 'sgd',
        loss: 'mse'
      });
      
      const input = [0.5, 0.8];
      const target = [1];
      
      // Forward pass
      const { output, cache } = model.forward(input, { training: true });
      
      // Backward pass
      const { loss, gradients } = model.backward(target, output, cache);
      
      assert.ok(typeof loss === 'number');
      assert.ok(Array.isArray(gradients));
      assert.equal(gradients.length, 2); // One for each layer
      assert.ok(gradients[0].dW); // Weights gradients
      assert.ok(gradients[0].dB); // Bias gradients
    });
  });
  
  describe('Model Training', () => {
    it('should train on a batch', async () => {
      const model = Prime.Neural.Model.ModelBuilder.sequential([
        { type: 'dense', inputSize: 2, units: 3, activation: 'sigmoid' },
        { type: 'dense', units: 1, activation: 'sigmoid' }
      ], {
        optimizer: 'sgd',
        loss: 'mse'
      });
      
      const inputs = [
        [0, 0],
        [0, 1],
        [1, 0],
        [1, 1]
      ];
      
      const targets = [
        [0],
        [1],
        [1],
        [0]
      ];
      
      // Initial prediction
      const initialPredictions = [];
      for (const input of inputs) {
        const { output } = model.forward(input);
        initialPredictions.push(output[0]);
      }
      
      // Train for a few epochs
      const trainingLoop = new Prime.Neural.Model.TrainingLoop(model, {
        epochs: 50,
        batchSize: 4,
        verbose: false
      });
      
      const result = await trainingLoop.train(inputs, targets);
      
      // Final predictions
      const finalPredictions = [];
      for (const input of inputs) {
        const { output } = model.forward(input);
        finalPredictions.push(output[0]);
      }
      
      // Check that loss decreased
      assert.ok(result.history.loss[0] > result.history.loss[result.history.loss.length - 1]);
      
      // Check that predictions improved
      for (let i = 0; i < 4; i++) {
        const target = targets[i][0];
        const initialError = Math.abs(initialPredictions[i] - target);
        const finalError = Math.abs(finalPredictions[i] - target);
        assert.ok(finalError < initialError, `Prediction error did not decrease for input ${i}`);
      }
    });
  });
  
  describe('Model Serialization', () => {
    it('should serialize and deserialize a model', () => {
      const originalModel = Prime.Neural.Model.ModelBuilder.sequential([
        { type: 'dense', inputSize: 2, units: 3, activation: 'sigmoid' },
        { type: 'dense', units: 1, activation: 'sigmoid' }
      ]);
      
      // Serialize model
      const serialized = Prime.Neural.Model.ModelIO.serialize(originalModel);
      
      // Deserialize model
      const restoredModel = Prime.Neural.Model.ModelIO.deserialize(serialized);
      
      // Check structure
      assert.equal(restoredModel.layers.length, originalModel.layers.length);
      assert.equal(restoredModel.layers[0].inputSize, originalModel.layers[0].inputSize);
      assert.equal(restoredModel.layers[0].outputSize, originalModel.layers[0].outputSize);
      assert.equal(restoredModel.layers[0].activation, originalModel.layers[0].activation);
    });
    
    it('should extract and apply weights', () => {
      const model = Prime.Neural.Model.ModelBuilder.sequential([
        { type: 'dense', inputSize: 2, units: 3, activation: 'sigmoid' },
        { type: 'dense', units: 1, activation: 'sigmoid' }
      ]);
      
      // Extract weights
      const weights = Prime.Neural.Model.ModelIO.extractWeights(model);
      
      // Modify some weights
      weights.layers[0].weights[0][0] = 1.5;
      weights.layers[0].biases[0] = 0.5;
      
      // Apply modified weights
      Prime.Neural.Model.ModelIO.applyWeights(model, weights);
      
      // Check that weights were applied
      assert.equal(model.layers[0].weights[0][0], 1.5);
      assert.equal(model.layers[0].biases[0], 0.5);
    });
  });
  
  describe('ModelManagement Facade', () => {
    it('should provide easy access to model management functions', () => {
      // Create a model
      const model = Prime.Neural.ModelManagement.createSequential([
        { type: 'dense', inputSize: 2, units: 3, activation: 'sigmoid' },
        { type: 'dense', units: 1, activation: 'sigmoid' }
      ], {
        optimizer: 'sgd',
        loss: 'mse'
      });
      
      // Create a training loop
      const training = Prime.Neural.ModelManagement.createTraining(model, {
        epochs: 10,
        batchSize: 4
      });
      
      // Save model
      const serialized = Prime.Neural.ModelManagement.saveModel(model);
      
      // Load model
      const loaded = Prime.Neural.ModelManagement.loadModel(serialized);
      
      assert.ok(loaded);
      assert.equal(loaded.layers.length, model.layers.length);
    });
  });
});