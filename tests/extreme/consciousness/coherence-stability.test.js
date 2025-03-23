/**
 * PrimeOS JavaScript Library - Consciousness Coherence Stability Tests
 * Tests for numerical stability of coherence calculations in extreme conditions
 */

const Prime = require('../../../src/core.js');
require('../../../src/math/index.js');
require('../../../src/consciousness/index.js');

describe('Consciousness Coherence Stability', () => {
  describe('Extreme Coherence Values', () => {
    test('should handle extremely small coherence values', () => {
      const module = new Prime.Consciousness.Module({
        dimension: 5,
        coherenceThreshold: 1e-10, // Extremely small threshold
      });
      
      module.initialize();
      
      // Create input with extremely small values
      const input = {
        value: [1e-10, 1e-10, 1e-10, 1e-10, 1e-10],
        importance: 1e-10,
      };
      
      // Process should not throw or produce NaN
      const result = module.processInput(input);
      
      expect(result).not.toBe(null);
      expect(Number.isFinite(result.coherence)).toBe(true);
      expect(result.vector.every(v => Number.isFinite(v))).toBe(true);
    });
    
    test('should handle extremely divergent states', () => {
      const module = new Prime.Consciousness.Module({
        dimension: 3,
      });
      
      // Initialize with a state
      const initialState = {
        id: 'initial',
        vector: [0.1, 0.1, 0.1],
        coherence: 0.7,
      };
      
      module.initialize(initialState);
      
      // Process a completely divergent input
      const divergentInput = {
        value: [0.9, 0.9, 0.9], // Opposite direction
        importance: 0.9,
      };
      
      const result = module.processInput(divergentInput);
      
      // Result should be valid even with extreme divergence
      expect(result).not.toBe(null);
      expect(Number.isFinite(result.coherence)).toBe(true);
    });
    
    test('should maintain stability with rapidly oscillating states', () => {
      const module = new Prime.Consciousness.Module({
        dimension: 2,
        timeStep: 0.01, // Small time step
      });
      
      module.initialize({
        vector: [0.5, 0.5],
        coherence: 0.7,
      });
      
      // Create rapidly oscillating inputs
      const results = [];
      for (let i = 0; i < 100; i++) {
        // Alternate between opposite values
        const input = {
          value: i % 2 === 0 ? [0.1, 0.1] : [0.9, 0.9],
          importance: 0.8,
        };
        
        const result = module.processInput(input);
        results.push(result);
      }
      
      // System should remain stable despite oscillation
      const finalState = results[results.length - 1];
      expect(Number.isFinite(finalState.coherence)).toBe(true);
      expect(finalState.vector.every(v => Number.isFinite(v))).toBe(true);
      
      // Coherence should not collapse to zero or explode
      expect(finalState.coherence).toBeGreaterThan(0);
      expect(finalState.coherence).toBeLessThanOrEqual(1);
    });
  });
  
  describe('Memory Capacity Limits', () => {
    test('should handle memory overflow gracefully', () => {
      const memory = new Prime.Consciousness.MemoryStructure({
        indexDimension: 3,
        shortTermCapacity: 10,
        longTermCapacity: 20,
      });
      
      // Generate a massive number of states
      for (let i = 0; i < 1000; i++) {
        memory.storeState({
          id: `state_${i}`,
          vector: [i/1000, (i+1)/1000, (i+2)/1000],
          coherence: 0.7,
          timestamp: Date.now() - (1000 - i),
        });
      }
      
      // Memory should remain within capacity
      expect(memory.shortTermMemory.length).toBeLessThanOrEqual(memory.shortTermCapacity);
      expect(memory.longTermMemory.length).toBeLessThanOrEqual(memory.longTermCapacity);
      
      // Operations should still work
      const state = memory.findSimilarState([0.5, 0.5, 0.5]);
      expect(state).not.toBe(null);
    });
    
    test('should handle very high dimensional states', () => {
      // Create high dimensional memory and module
      const highDimension = 100;
      
      const memory = new Prime.Consciousness.MemoryStructure({
        indexDimension: highDimension,
      });
      
      const module = new Prime.Consciousness.Module({
        dimension: highDimension,
      });
      
      // Create high-dimensional state
      const highDimState = {
        id: 'high_dim',
        vector: Array(highDimension).fill(0).map(() => Math.random()),
        coherence: 0.7,
      };
      
      // Operations should work without numerical issues
      memory.storeState(highDimState);
      module.initialize(highDimState);
      
      // Create similar state with small differences
      const similarVector = [...highDimState.vector];
      for (let i = 0; i < 5; i++) {
        const idx = Math.floor(Math.random() * highDimension);
        similarVector[idx] += 0.01;
      }
      
      // Search should find original state
      const found = memory.findSimilarState(similarVector);
      expect(found.id).toBe('high_dim');
      
      // Processing should maintain numerical stability
      const result = module.processInput({
        value: similarVector,
        importance: 0.5,
      });
      
      expect(result).not.toBe(null);
      expect(Number.isFinite(result.coherence)).toBe(true);
    });
  });
  
  describe('Temporal Stability', () => {
    test('should maintain stability with extreme time steps', () => {
      // Test with very small time step
      const smallStepModule = new Prime.Consciousness.Module({
        dimension: 3,
        timeStep: 1e-6, // Extremely small
      });
      
      smallStepModule.initialize({
        vector: [0.5, 0.5, 0.5],
        coherence: 0.7,
      });
      
      // Process with small step
      smallStepModule.processInput({
        value: [0.6, 0.6, 0.6],
        importance: 0.7,
      });
      
      // Test with very large time step
      const largeStepModule = new Prime.Consciousness.Module({
        dimension: 3,
        timeStep: 100, // Extremely large
      });
      
      largeStepModule.initialize({
        vector: [0.5, 0.5, 0.5],
        coherence: 0.7,
      });
      
      // Process with large step
      largeStepModule.processInput({
        value: [0.6, 0.6, 0.6],
        importance: 0.7,
      });
      
      // Both should produce valid results
      expect(Number.isFinite(smallStepModule.currentState.coherence)).toBe(true);
      expect(Number.isFinite(largeStepModule.currentState.coherence)).toBe(true);
      
      // Values should remain in valid range
      expect(smallStepModule.currentState.vector.every(v => v >= 0 && v <= 1)).toBe(true);
      expect(largeStepModule.currentState.vector.every(v => v >= 0 && v <= 1)).toBe(true);
    });
    
    test('should handle extreme temporal sequences', () => {
      const temporal = new Prime.Consciousness.TemporalIntegration({
        dimension: 3,
      });
      
      // Create extremely rapid sequence
      const rapidSequence = [];
      const baseTime = Date.now();
      
      for (let i = 0; i < 100; i++) {
        rapidSequence.push({
          id: `rapid_${i}`,
          vector: [i/100, i/100, i/100],
          coherence: 0.7,
          timestamp: baseTime + i, // 1ms intervals
        });
      }
      
      // Create extremely slow sequence
      const slowSequence = [];
      
      for (let i = 0; i < 5; i++) {
        slowSequence.push({
          id: `slow_${i}`,
          vector: [i/5, i/5, i/5],
          coherence: 0.7,
          timestamp: baseTime + i * 86400000, // 1 day intervals
        });
      }
      
      // Both should produce valid coherence measures
      const rapidCoherence = temporal.calculateTemporalCoherence(rapidSequence);
      const slowCoherence = temporal.calculateTemporalCoherence(slowSequence);
      
      expect(Number.isFinite(rapidCoherence)).toBe(true);
      expect(Number.isFinite(slowCoherence)).toBe(true);
      
      // Projection should work for both
      const rapidProjection = temporal.projectFuture(
        rapidSequence[rapidSequence.length - 1],
        rapidSequence.slice(0, 5)
      );
      
      const slowProjection = temporal.projectFuture(
        slowSequence[slowSequence.length - 1],
        slowSequence.slice(0, 3)
      );
      
      expect(rapidProjection.length).toBeGreaterThan(0);
      expect(slowProjection.length).toBeGreaterThan(0);
    });
  });
});