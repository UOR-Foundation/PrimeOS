/**
 * PrimeOS JavaScript Library - Attention Mechanism Unit Tests
 * Tests for the consciousness module's AttentionMechanism component
 */

const Prime = require('../../../src/core.js');
require('../../../src/math/index.js');
require('../../../src/consciousness/index.js');

// Import test utilities
const { assertThrows } = require('../../utils/assertions');

describe('Consciousness AttentionMechanism', () => {
  describe('Instantiation and Configuration', () => {
    test('should instantiate with default parameters', () => {
      const attention = new Prime.Consciousness.AttentionMechanism();

      expect(attention instanceof Prime.Consciousness.AttentionMechanism).toBe(true);
      expect(attention.attentionCapacity).toBe(1.0);
      expect(attention.fieldDimension).toBe(7);
      expect(Array.isArray(attention.attentionField.values)).toBe(true);
      expect(attention.attentionField.values.length).toBe(7);
    });

    test('should accept custom dimensions and capacity', () => {
      const attention = new Prime.Consciousness.AttentionMechanism({
        fieldDimension: 5,
        attentionCapacity: 1.5,
      });

      expect(attention.fieldDimension).toBe(5);
      expect(attention.attentionCapacity).toBe(1.5);
      expect(attention.attentionField.values.length).toBe(5);
    });
    
    test('should enforce minimum field dimension', () => {
      // Create with too low a dimension
      const attention = new Prime.Consciousness.AttentionMechanism({
        fieldDimension: 1, // Below minimum
      });
      
      // Should auto-correct to minimum
      expect(attention.fieldDimension).toBeGreaterThan(1);
    });
  });

  describe('Initialization and State Handling', () => {
    test('should initialize with a state', () => {
      const attention = new Prime.Consciousness.AttentionMechanism({
        fieldDimension: 5,
      });

      // Create a test state
      const testState = {
        attention: 0.5,
        awareness: 0.6,
        coherence: 0.7,
        integration: 0.4,
        differentiation: 0.3,
      };

      const result = attention.initialize(testState);
      expect(result).toBe(true);
      expect(attention.attentionField.values.some(v => v > 0)).toBe(true);
      expect(Object.keys(attention.lastCoherenceMap).length).toBeGreaterThan(0);
    });
    
    test('should handle invalid state gracefully', () => {
      const attention = new Prime.Consciousness.AttentionMechanism();
      
      // Null state should not throw but return false
      const result = attention.initialize(null);
      expect(result).toBe(false);
    });
  });

  describe('Attention Field Updates', () => {
    test('should update attention field based on saliency', () => {
      const attention = new Prime.Consciousness.AttentionMechanism({
        fieldDimension: 3,
      });
      
      // Create initial field state
      attention.attentionField = {
        values: [0.2, 0.3, 0.5],
        saliency: [0.1, 0.8, 0.1],
      };
      
      // Update with saliency
      attention.update();
      
      // Field should shift toward saliency
      expect(attention.attentionField.values[1]).toBeGreaterThan(0.3);
    });
    
    test('should maintain total attention within capacity', () => {
      const attention = new Prime.Consciousness.AttentionMechanism({
        fieldDimension: 5,
        attentionCapacity: 1.0,
      });
      
      // Initialize with some state
      const testState = {
        vector: [0.1, 0.2, 0.3, 0.4, 0.5],
        coherence: 0.7,
      };
      
      attention.initialize(testState);
      attention.update();
      
      // Sum of field values should not exceed capacity
      const sum = attention.attentionField.values.reduce((a, b) => a + b, 0);
      expect(sum).toBeLessThanOrEqual(attention.attentionCapacity * 1.001); // Small buffer for floating point
    });
  });

  describe('Focus and Distribution', () => {
    test('should focus attention on specific dimensions', () => {
      const attention = new Prime.Consciousness.AttentionMechanism({
        fieldDimension: 5,
      });
      
      // Set initial even distribution
      attention.attentionField.values = [0.2, 0.2, 0.2, 0.2, 0.2];
      
      // Focus on dimension 2
      attention.focus(2, 0.5);
      
      // That dimension should have increased attention
      expect(attention.attentionField.values[2]).toBe(0.5);
      
      // And total should still be within capacity
      const sum = attention.attentionField.values.reduce((a, b) => a + b, 0);
      expect(sum).toBeLessThanOrEqual(attention.attentionCapacity * 1.001);
    });
    
    test('should distribute attention evenly', () => {
      const attention = new Prime.Consciousness.AttentionMechanism({
        fieldDimension: 4,
        attentionCapacity: 1.0,
      });
      
      // Set uneven distribution
      attention.attentionField.values = [0.7, 0.1, 0.1, 0.1];
      
      // Distribute evenly
      attention.distributeEvenly();
      
      // Should be more even
      expect(attention.attentionField.values[0]).toBe(0.25);
      expect(attention.attentionField.values[1]).toBe(0.25);
      expect(attention.attentionField.values[2]).toBe(0.25);
      expect(attention.attentionField.values[3]).toBe(0.25);
    });
  });

  describe('Coherence Calculation', () => {
    test('should calculate coherence relative to a target state', () => {
      const attention = new Prime.Consciousness.AttentionMechanism({
        fieldDimension: 3,
      });
      
      // Set a known state
      attention.attentionField.values = [0.2, 0.3, 0.5];
      
      // Target state
      const targetState = {
        vector: [0.2, 0.3, 0.5], // Exact match
        coherence: 1.0,
      };
      
      const coherence = attention.calculateCoherence(targetState);
      expect(coherence).toBeGreaterThan(0.9); // Should be high since vectors match
    });
    
    test('should handle divergent states appropriately', () => {
      const attention = new Prime.Consciousness.AttentionMechanism({
        fieldDimension: 3,
      });
      
      // Set a known state
      attention.attentionField.values = [0.2, 0.3, 0.5];
      
      // Target state that's different
      const targetState = {
        vector: [0.8, 0.1, 0.1], // Very different
        coherence: 1.0,
      };
      
      const coherence = attention.calculateCoherence(targetState);
      expect(coherence).toBeLessThan(0.5); // Should be low since vectors are different
    });
  });
});