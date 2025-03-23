/**
 * PrimeOS Unit Tests - Neural Optimization
 * 
 * Tests for the optimization components in the Neural module.
 */

const Prime = require('../../../src');
const { Assertions } = require('../../utils');

describe('Neural Optimization', () => {
  describe('Coherence SGD Optimizer', () => {
    test('should create coherence SGD optimizer with correct properties', () => {
      const optimizer = new Prime.Neural.Optimization.CoherenceSGD({
        learningRate: 0.1,
        momentum: 0.9,
        minCoherence: 0.5,
      });

      expect(optimizer instanceof Prime.Neural.Optimization.CoherenceOptimizer).toBe(true);
      expect(optimizer.learningRate).toBe(0.1);
      expect(optimizer.momentum).toBe(0.9);
      expect(optimizer.minCoherence).toBe(0.5);
    });

    test('should update parameters with coherence constraint', () => {
      const optimizer = new Prime.Neural.Optimization.CoherenceSGD({
        learningRate: 0.1,
        minCoherence: 0.5,
      });

      // Simple parameters and gradients
      const params = {
        weights: [
          [1, 1],
          [1, 1],
        ],
        biases: [0, 0],
      };

      const gradients = {
        weights: [
          [0.1, 0.1],
          [0.1, 0.1],
        ],
        biases: [0.1, 0.1],
      };

      // Simple coherence function that returns 0.8 for any input
      const coherenceFn = () => 0.8;

      const updatedParams = optimizer.update(params, gradients, coherenceFn);

      expect(updatedParams.weights[0][0]).toBeLessThan(params.weights[0][0]);
      expect(typeof optimizer.getStatistics().iterations).toBe("number");
    });

    test('should handle coherence violation', () => {
      const optimizer = new Prime.Neural.Optimization.CoherenceSGD({
        learningRate: 0.1,
        minCoherence: 0.7,
      });

      // Simple parameters and gradients
      const params = {
        weights: [
          [1, 1],
          [1, 1],
        ],
        biases: [0, 0],
      };

      const gradients = {
        weights: [
          [0.1, 0.1],
          [0.1, 0.1],
        ],
        biases: [0.1, 0.1],
      };

      // Coherence function that starts at 0.8 but drops to 0.6 after update
      let calls = 0;
      const coherenceFn = () => {
        calls++;
        return calls === 1 ? 0.8 : 0.6;
      };

      const updatedParams = optimizer.update(params, gradients, coherenceFn);

      expect(updatedParams.weights[0][0]).toBeLessThan(params.weights[0][0]);
      expect(calls).toBeGreaterThan(1);
    });
  });

  describe('Coherence Adam Optimizer', () => {
    test('should create and use Adam optimizer correctly', () => {
      const optimizer = new Prime.Neural.Optimization.CoherenceAdam({
        learningRate: 0.001,
        beta1: 0.9,
        beta2: 0.999,
        minCoherence: 0.5,
      });

      expect(optimizer instanceof Prime.Neural.Optimization.CoherenceOptimizer).toBe(true);
      expect(optimizer.learningRate).toBe(0.001);
      expect(optimizer.beta1).toBe(0.9);
      expect(optimizer.beta2).toBe(0.999);

      // Simple parameters and gradients
      const params = {
        weights: [
          [1, 1],
          [1, 1],
        ],
        biases: [0, 0],
      };

      const gradients = {
        weights: [
          [0.1, 0.1],
          [0.1, 0.1],
        ],
        biases: [0.1, 0.1],
      };

      // Simple coherence function that returns 0.8 for any input
      const coherenceFn = () => 0.8;

      const updatedParams = optimizer.update(params, gradients, coherenceFn);

      expect(updatedParams.weights[0][0]).toBeLessThan(params.weights[0][0]);
    });

    test('should manage first and second moment state', () => {
      const optimizer = new Prime.Neural.Optimization.CoherenceAdam({
        learningRate: 0.001,
        beta1: 0.9,
        beta2: 0.999,
        minCoherence: 0.5,
      });

      // Simple parameters and gradients
      const params = {
        weights: [
          [1, 1],
          [1, 1],
        ],
        biases: [0, 0],
      };

      const gradients = {
        weights: [
          [0.1, 0.1],
          [0.1, 0.1],
        ],
        biases: [0.1, 0.1],
      };

      // Simple coherence function
      const coherenceFn = () => 0.8;

      // Update multiple times to build up momentum
      let currentParams = params;
      for (let i = 0; i < 5; i++) {
        currentParams = optimizer.update(currentParams, gradients, coherenceFn);
      }

      // Check statistics
      const stats = optimizer.getStatistics();
      expect(stats.iterations).toBe(5);
      expect(stats.coherenceViolations).toBe(0);
      
      // Internal state should exist for momentum tracking
      expect(optimizer._m).toBeDefined();
      expect(optimizer._v).toBeDefined();
    });

    test('should handle extremely small gradients appropriately', () => {
      const optimizer = new Prime.Neural.Optimization.CoherenceAdam({
        learningRate: 0.001,
        beta1: 0.9,
        beta2: 0.999,
        minCoherence: 0.5,
        epsilon: 1e-8, // Small epsilon for numerical stability
      });

      // Simple parameters
      const params = {
        weights: [
          [1, 1],
          [1, 1],
        ],
        biases: [0, 0],
      };

      // Extremely small gradients
      const tinyGradients = {
        weights: [
          [1e-15, 1e-15],
          [1e-15, 1e-15],
        ],
        biases: [1e-15, 1e-15],
      };

      // Simple coherence function
      const coherenceFn = () => 0.8;

      // Should not cause numerical issues
      const updatedParams = optimizer.update(params, tinyGradients, coherenceFn);
      
      // Parameters should change, but by extremely small amounts
      expect(updatedParams.weights[0][0]).not.toBe(params.weights[0][0]);
      expect(Math.abs(updatedParams.weights[0][0] - params.weights[0][0])).toBeLessThan(1e-10);
    });
  });

  describe('Optimizer Factory', () => {
    test('should create optimizer from config', () => {
      // Create optimizer with SGD config
      const sgdConfig = {
        type: 'sgd',
        learningRate: 0.01,
        momentum: 0.9,
        minCoherence: 0.5,
      };

      const sgdOptimizer = Prime.Neural.Optimization.createOptimizer(sgdConfig);
      expect(sgdOptimizer instanceof Prime.Neural.Optimization.CoherenceSGD).toBe(true);
      expect(sgdOptimizer.learningRate).toBe(0.01);
      expect(sgdOptimizer.momentum).toBe(0.9);

      // Create optimizer with Adam config
      const adamConfig = {
        type: 'adam',
        learningRate: 0.001,
        beta1: 0.9,
        beta2: 0.999,
        minCoherence: 0.6,
      };

      const adamOptimizer = Prime.Neural.Optimization.createOptimizer(adamConfig);
      expect(adamOptimizer instanceof Prime.Neural.Optimization.CoherenceAdam).toBe(true);
      expect(adamOptimizer.learningRate).toBe(0.001);
      expect(adamOptimizer.minCoherence).toBe(0.6);
    });

    test('should create optimizer with default values when not specified', () => {
      // Create with minimal config
      const minimalConfig = {
        type: 'sgd',
      };

      const optimizer = Prime.Neural.Optimization.createOptimizer(minimalConfig);
      expect(optimizer instanceof Prime.Neural.Optimization.CoherenceSGD).toBe(true);
      // Should use default learning rate
      expect(optimizer.learningRate).toBeDefined();
      // Should use default coherence threshold
      expect(optimizer.minCoherence).toBeDefined();
    });
  });
});