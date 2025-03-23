/**
 * PrimeOS JavaScript Library - Memory Structure Unit Tests
 * Tests for the consciousness module's memory component
 */

const Prime = require('../../../src/core.js');
require('../../../src/math/index.js');
require('../../../src/consciousness/index.js');

// Import test utilities
const { assertThrows } = require('../../utils/assertions');

describe('Consciousness MemoryStructure', () => {
  describe('Instantiation and Configuration', () => {
    test('should instantiate with default parameters', () => {
      const memory = new Prime.Consciousness.MemoryStructure();

      expect(memory instanceof Prime.Consciousness.MemoryStructure).toBe(true);
      expect(memory.indexDimension).toBeGreaterThan(0);
      expect(memory.shortTermCapacity).toBeGreaterThan(0);
      expect(memory.longTermCapacity).toBeGreaterThan(0);
      expect(memory.shortTermMemory).toBeInstanceOf(Array);
      expect(memory.longTermMemory).toBeInstanceOf(Array);
    });

    test('should accept custom configuration', () => {
      const memory = new Prime.Consciousness.MemoryStructure({
        indexDimension: 7,
        shortTermCapacity: 20,
        longTermCapacity: 100,
      });

      expect(memory.indexDimension).toBe(7);
      expect(memory.shortTermCapacity).toBe(20);
      expect(memory.longTermCapacity).toBe(100);
    });
    
    test('should enforce minimum capacities', () => {
      // Create with too small capacities
      const memory = new Prime.Consciousness.MemoryStructure({
        shortTermCapacity: 0,
        longTermCapacity: 1,
      });
      
      // Should auto-correct to minimum values
      expect(memory.shortTermCapacity).toBeGreaterThan(0);
      expect(memory.longTermCapacity).toBeGreaterThan(1);
    });
  });

  describe('Initialization', () => {
    test('should initialize with a state', () => {
      const memory = new Prime.Consciousness.MemoryStructure({
        indexDimension: 3,
      });

      const initialState = {
        id: 'initial_state',
        vector: [0.5, 0.6, 0.7],
        coherence: 0.8,
      };

      memory.initialize(initialState);
      
      // Should have added state to memory
      expect(memory.shortTermMemory.length).toBe(1);
      expect(memory.shortTermMemory[0].id).toBe('initial_state');
    });
    
    test('should handle invalid state gracefully', () => {
      const memory = new Prime.Consciousness.MemoryStructure();
      
      // Should not throw with null state
      expect(() => {
        memory.initialize(null);
      }).not.toThrow();
      
      // Memory should be empty
      expect(memory.shortTermMemory.length).toBe(0);
    });
  });

  describe('Memory Operations', () => {
    let memory;
    
    beforeEach(() => {
      memory = new Prime.Consciousness.MemoryStructure({
        indexDimension: 5,
        shortTermCapacity: 10,
        longTermCapacity: 20,
      });
      
      // Initialize with a state
      memory.initialize({
        id: 'initial_state',
        vector: [0.1, 0.2, 0.3, 0.4, 0.5],
        coherence: 0.7,
      });
    });
    
    test('should store and retrieve memories', () => {
      // Add test states
      for (let i = 0; i < 5; i++) {
        memory.storeState({
          id: `state_${i}`,
          vector: [i/10, (i+1)/10, (i+2)/10, (i+3)/10, (i+4)/10],
          coherence: 0.7 + i/100,
        });
      }
      
      // Short-term memory should contain states
      expect(memory.shortTermMemory.length).toBe(6); // 5 + initial
      
      // Retrieve a specific state by ID
      const state = memory.retrieveStateById('state_3');
      expect(state).not.toBe(null);
      expect(state.id).toBe('state_3');
      
      // Retrieve by vector similarity
      const similarState = memory.findSimilarState([0.3, 0.4, 0.5, 0.6, 0.7]);
      expect(similarState).not.toBe(null);
      expect(similarState.id).toBe('state_3');
    });
    
    test('should handle short-term memory capacity limits', () => {
      // Fill short-term memory beyond capacity
      for (let i = 0; i < 15; i++) {
        memory.storeState({
          id: `state_${i}`,
          vector: [i/10, (i+1)/10, (i+2)/10, (i+3)/10, (i+4)/10],
          coherence: 0.7,
        });
      }
      
      // Memory should be limited to capacity
      expect(memory.shortTermMemory.length).toBe(memory.shortTermCapacity);
      
      // Earlier states should have been pushed out (FIFO)
      expect(memory.retrieveStateById('initial_state')).toBe(null);
      expect(memory.retrieveStateById('state_0')).toBe(null);
    });
    
    test('should transfer to long-term memory based on coherence', () => {
      // Add a few states with high coherence
      for (let i = 0; i < 3; i++) {
        memory.storeState({
          id: `high_coherence_${i}`,
          vector: [i/10, (i+1)/10, (i+2)/10, (i+3)/10, (i+4)/10],
          coherence: 0.95, // High coherence
        });
      }
      
      // Force consolidation
      memory.consolidateMemory();
      
      // Should have moved high coherence states to long-term memory
      expect(memory.longTermMemory.length).toBeGreaterThan(0);
      
      // Should be able to retrieve from long-term memory
      const state = memory.retrieveStateById('high_coherence_1');
      expect(state).not.toBe(null);
      expect(state.id).toBe('high_coherence_1');
    });
  });

  describe('Memory Search and Retrieval', () => {
    let memory;
    
    beforeEach(() => {
      memory = new Prime.Consciousness.MemoryStructure({
        indexDimension: 3,
        shortTermCapacity: 20,
        longTermCapacity: 50,
      });
      
      // Add test states in different regions of vector space
      memory.storeState({
        id: 'region1_1',
        vector: [0.1, 0.1, 0.1],
        coherence: 0.7,
      });
      
      memory.storeState({
        id: 'region1_2',
        vector: [0.15, 0.12, 0.11],
        coherence: 0.7,
      });
      
      memory.storeState({
        id: 'region2_1',
        vector: [0.8, 0.8, 0.8],
        coherence: 0.7,
      });
      
      memory.storeState({
        id: 'region2_2', 
        vector: [0.85, 0.82, 0.81],
        coherence: 0.7,
      });
    });
    
    test('should find closest state by vector similarity', () => {
      // Search near region 1
      const result1 = memory.findSimilarState([0.12, 0.11, 0.10]);
      expect(result1.id).toBe('region1_1');
      
      // Search near region 2
      const result2 = memory.findSimilarState([0.84, 0.83, 0.82]);
      expect(result2.id).toBe('region2_2');
    });
    
    test('should find states by coherence threshold', () => {
      // Add some states with varying coherence
      memory.storeState({
        id: 'low_coherence',
        vector: [0.5, 0.5, 0.5],
        coherence: 0.3,
      });
      
      memory.storeState({
        id: 'high_coherence',
        vector: [0.6, 0.6, 0.6],
        coherence: 0.9,
      });
      
      // Find high coherence states
      const highCoherenceStates = memory.findStatesByCoherence(0.8);
      expect(highCoherenceStates.length).toBe(1);
      expect(highCoherenceStates[0].id).toBe('high_coherence');
      
      // Find all states with low threshold
      const allStates = memory.findStatesByCoherence(0.2);
      expect(allStates.length).toBe(6);
    });
    
    test('should search by time and recency', () => {
      // Force timestamps for testing
      memory.shortTermMemory[0].timestamp = Date.now() - 10000;
      memory.shortTermMemory[1].timestamp = Date.now() - 8000;
      memory.shortTermMemory[2].timestamp = Date.now() - 5000;
      memory.shortTermMemory[3].timestamp = Date.now() - 2000;
      
      // Get recent states
      const recentStates = memory.getRecentStates(2);
      expect(recentStates.length).toBe(2);
      expect(recentStates[0].id).toBe('region2_2');
      expect(recentStates[1].id).toBe('region2_1');
    });
  });
});