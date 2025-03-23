/**
 * PrimeOS JavaScript Library - Memory and Temporal Integration Tests
 * Tests for the integration between MemoryStructure and TemporalIntegration components
 */

const Prime = require('../../../src/core.js');
require('../../../src/math/index.js');
require('../../../src/consciousness/index.js');

describe('Memory-Temporal Integration', () => {
  describe('State Persistence and Temporal Evolution', () => {
    let memory;
    let temporal;
    
    beforeEach(() => {
      // Create both components
      memory = new Prime.Consciousness.MemoryStructure({
        indexDimension: 5,
        shortTermCapacity: 20,
      });
      
      temporal = new Prime.Consciousness.TemporalIntegration({
        dimension: 5,
        timeStep: 0.1,
      });
      
      // Initialize both with the same initial state
      const initialState = {
        id: 'initial_state',
        vector: [0.2, 0.4, 0.6, 0.3, 0.5],
        coherence: 0.7,
        timestamp: Date.now(),
      };
      
      memory.initialize(initialState);
      temporal.initialize(initialState);
    });
    
    test('should evolve and store state sequences', () => {
      // Generate a sequence of states using temporal evolution
      let currentState = temporal.currentState;
      
      // Evolve a few states
      for (let i = 0; i < 5; i++) {
        // Apply temporal evolution
        const nextState = temporal.evolveState(currentState);
        
        // Store in memory
        memory.storeState(nextState);
        
        // Update current state
        currentState = nextState;
      }
      
      // Memory should contain the full sequence
      expect(memory.shortTermMemory.length).toBe(6); // Initial + 5 evolved
      
      // Retrieve and verify the sequence is intact
      const sequence = memory.getRecentStates(6);
      expect(sequence.length).toBe(6);
      
      // Each state should have a timestamp
      for (let state of sequence) {
        expect(state.timestamp).toBeDefined();
      }
      
      // Test time ordering
      for (let i = 1; i < sequence.length; i++) {
        expect(sequence[i-1].timestamp).toBeGreaterThan(sequence[i].timestamp);
      }
    });
    
    test('should detect temporal patterns in memory', () => {
      // Create a repeating sequence of states
      const pattern = [
        { vector: [0.1, 0.2, 0.3, 0.4, 0.5], coherence: 0.7 },
        { vector: [0.2, 0.3, 0.4, 0.5, 0.6], coherence: 0.7 },
        { vector: [0.3, 0.4, 0.5, 0.6, 0.7], coherence: 0.7 },
        { vector: [0.2, 0.3, 0.4, 0.5, 0.6], coherence: 0.7 }, // Repeats
        { vector: [0.1, 0.2, 0.3, 0.4, 0.5], coherence: 0.7 }, // Repeats
      ];
      
      // Store pattern with proper timestamps
      for (let i = 0; i < pattern.length; i++) {
        const state = {
          ...pattern[i],
          id: `pattern_${i}`,
          timestamp: Date.now() - (pattern.length - i) * 1000, // Older to newer
        };
        memory.storeState(state);
      }
      
      // Use temporal integration to predict next state
      const recentStates = memory.getRecentStates(3);
      const predictedState = temporal.predictNextState(recentStates);
      
      // Should predict a state similar to the pattern
      expect(predictedState).not.toBe(null);
      
      // Should be similar to the expected next state
      const expectedVector = [0.2, 0.3, 0.4, 0.5, 0.6]; // Based on pattern
      const similarityScore = temporal.calculateStateSimilarity(
        predictedState.vector, 
        expectedVector
      );
      
      expect(similarityScore).toBeGreaterThan(0.8);
    });
    
    test('should integrate memory recall with temporal projection', () => {
      // Store some past states in memory
      for (let i = 0; i < 10; i++) {
        memory.storeState({
          id: `past_${i}`,
          vector: [i/10, (i+1)/10, (i+2)/10, (i+3)/10, (i+4)/10],
          coherence: 0.7,
          timestamp: Date.now() - (10 - i) * 1000, // Increasing timestamps
        });
      }
      
      // Get current state
      const currentState = {
        id: 'current',
        vector: [0.5, 0.6, 0.7, 0.8, 0.9],
        coherence: 0.8,
        timestamp: Date.now(),
      };
      
      // Find similar past states from memory
      const similarState = memory.findSimilarState(currentState.vector);
      expect(similarState).not.toBe(null);
      
      // Get states that followed the similar state
      const followingStates = memory.getStatesAfter(similarState.timestamp, 3);
      expect(followingStates.length).toBeGreaterThan(0);
      
      // Use temporal integration to project based on this pattern
      const projectedFuture = temporal.projectFuture(currentState, followingStates);
      expect(projectedFuture.length).toBeGreaterThan(0);
      
      // Projected states should have increasing timestamps
      for (let i = 1; i < projectedFuture.length; i++) {
        expect(projectedFuture[i].timestamp).toBeGreaterThan(projectedFuture[i-1].timestamp);
      }
    });
  });
  
  describe('Temporal Coherence Measurement', () => {
    let memory;
    let temporal;
    
    beforeEach(() => {
      memory = new Prime.Consciousness.MemoryStructure({
        indexDimension: 3,
      });
      
      temporal = new Prime.Consciousness.TemporalIntegration({
        dimension: 3,
      });
      
      // Initialize
      const initialState = {
        id: 'initial',
        vector: [0.5, 0.5, 0.5],
        coherence: 0.7,
        timestamp: Date.now() - 10000,
      };
      
      memory.initialize(initialState);
      temporal.initialize(initialState);
    });
    
    test('should calculate temporal coherence of state sequences', () => {
      // Create smooth trajectory
      const smoothTrajectory = [
        { id: 'smooth_1', vector: [0.1, 0.1, 0.1], coherence: 0.7, timestamp: Date.now() - 5000 },
        { id: 'smooth_2', vector: [0.2, 0.2, 0.2], coherence: 0.7, timestamp: Date.now() - 4000 },
        { id: 'smooth_3', vector: [0.3, 0.3, 0.3], coherence: 0.7, timestamp: Date.now() - 3000 },
        { id: 'smooth_4', vector: [0.4, 0.4, 0.4], coherence: 0.7, timestamp: Date.now() - 2000 },
        { id: 'smooth_5', vector: [0.5, 0.5, 0.5], coherence: 0.7, timestamp: Date.now() - 1000 },
      ];
      
      // Create jumpy trajectory
      const jumpyTrajectory = [
        { id: 'jumpy_1', vector: [0.1, 0.1, 0.1], coherence: 0.7, timestamp: Date.now() - 5000 },
        { id: 'jumpy_2', vector: [0.9, 0.9, 0.9], coherence: 0.7, timestamp: Date.now() - 4000 },
        { id: 'jumpy_3', vector: [0.1, 0.1, 0.1], coherence: 0.7, timestamp: Date.now() - 3000 },
        { id: 'jumpy_4', vector: [0.9, 0.9, 0.9], coherence: 0.7, timestamp: Date.now() - 2000 },
        { id: 'jumpy_5', vector: [0.1, 0.1, 0.1], coherence: 0.7, timestamp: Date.now() - 1000 },
      ];
      
      // Calculate temporal coherence
      const smoothCoherence = temporal.calculateTemporalCoherence(smoothTrajectory);
      const jumpyCoherence = temporal.calculateTemporalCoherence(jumpyTrajectory);
      
      // Smooth trajectory should have higher temporal coherence
      expect(smoothCoherence).toBeGreaterThan(jumpyCoherence);
    });
    
    test('should integrate memory consolidation with temporal coherence', () => {
      // Store varying sequences in memory
      
      // Sequence 1: Coherent
      for (let i = 0; i < 5; i++) {
        memory.storeState({
          id: `coherent_${i}`,
          vector: [i/10, i/10, i/10],
          coherence: 0.7,
          timestamp: Date.now() - (10 - i) * 1000,
        });
      }
      
      // Sequence 2: Incoherent
      for (let i = 0; i < 5; i++) {
        memory.storeState({
          id: `incoherent_${i}`,
          vector: [Math.random(), Math.random(), Math.random()],
          coherence: 0.5,
          timestamp: Date.now() - (5 - i) * 1000,
        });
      }
      
      // Use temporal integration to evaluate the sequences
      const states = memory.getAllStates();
      
      // Group states into sequences (normally this would use temporal proximity)
      const sequence1 = states.filter(s => s.id.startsWith('coherent'));
      const sequence2 = states.filter(s => s.id.startsWith('incoherent'));
      
      // Evaluate temporal coherence
      const coherence1 = temporal.calculateTemporalCoherence(sequence1);
      const coherence2 = temporal.calculateTemporalCoherence(sequence2);
      
      // Coherent sequence should have higher temporal coherence
      expect(coherence1).toBeGreaterThan(coherence2);
      
      // Consolidate memory based on temporal coherence
      for (const state of sequence1) {
        state.temporalCoherence = coherence1;
      }
      
      for (const state of sequence2) {
        state.temporalCoherence = coherence2;
      }
      
      // Force memory consolidation
      memory.consolidateMemory();
      
      // Coherent sequences should be more likely to move to long-term memory
      const longTermStates = memory.longTermMemory;
      let coherentCount = 0;
      let incoherentCount = 0;
      
      for (const state of longTermStates) {
        if (state.id.startsWith('coherent')) coherentCount++;
        if (state.id.startsWith('incoherent')) incoherentCount++;
      }
      
      // More coherent states should be in long-term memory
      expect(coherentCount).toBeGreaterThanOrEqual(incoherentCount);
    });
  });
});