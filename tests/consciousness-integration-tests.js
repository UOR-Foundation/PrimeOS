/**
 * Comprehensive Integration Tests for PrimeOS Consciousness Module
 * 
 * These tests verify the integration of all consciousness components:
 * - MemoryStructure
 * - DecisionMaking
 * - ThresholdManager
 * - ConsciousnessModule (integrating all components)
 */

// Import Prime with all required modules
const Prime = require("../src");

describe('Consciousness Module Integration Tests', () => {
  // Helper function for testing if an object has all required properties
  const hasAllProperties = (obj, properties) => {
    const missing = properties.filter(prop => obj[prop] === undefined);
    return missing.length === 0;
  };
  
  // Create a standard initial state for consistent testing
  const createInitialState = () => ({
    id: 'initial_state',
    vector: [0.5, 0.6, 0.7, 0.4, 0.3, 0.5, 0.6],
    coherence: 0.7
  });
  
  describe('MemoryStructure Component', () => {
    let memory;
    let initialState;
    
    beforeEach(() => {
      // Setup memory structure for each test
      memory = new Prime.Consciousness.MemoryStructure({
        indexDimension: 7,
        shortTermCapacity: 20,
        longTermCapacity: 100
      });
      
      initialState = createInitialState();
      memory.initialize(initialState);
    });
    
    test('MemoryStructure can be instantiated', () => {
      expect(memory).toBeInstanceOf(Prime.Consciousness.MemoryStructure);
    });
    
    test('Can store and retrieve memories', () => {
      // Store test memories
      for (let i = 0; i < 5; i++) {
        const testState = {
          id: `test_state_${i}`,
          vector: [
            0.5 + (Math.random() * 0.2 - 0.1),
            0.6 + (Math.random() * 0.2 - 0.1),
            0.7 + (Math.random() * 0.2 - 0.1),
            0.4 + (Math.random() * 0.2 - 0.1),
            0.3 + (Math.random() * 0.2 - 0.1),
            0.5 + (Math.random() * 0.2 - 0.1),
            0.6 + (Math.random() * 0.2 - 0.1)
          ],
          coherence: 0.7 + (Math.random() * 0.2 - 0.1)
        };
        
        const memoryRecord = memory.store(testState, { type: 'test', timestamp: Date.now() });
        expect(memoryRecord).not.toBeNull();
      }
      
      // Test retrieving memories
      const retrieveQuery = {
        vector: [0.55, 0.65, 0.75, 0.45, 0.35, 0.55, 0.65]
      };
      
      const retrievedMemories = memory.retrieve(retrieveQuery, { limit: 3 });
      expect(Array.isArray(retrievedMemories)).toBe(true);
      expect(retrievedMemories.length).toBeGreaterThan(0);
      
      // Verify retrieved memory structure
      if (retrievedMemories.length > 0) {
        expect(hasAllProperties(retrievedMemories[0], ['memory', 'similarity'])).toBe(true);
      }
    });
    
    test('Can get recent memories', () => {
      // Store some test memories first
      for (let i = 0; i < 3; i++) {
        memory.store({
          id: `recent_${i}`,
          vector: [0.5, 0.6, 0.7, 0.4, 0.3, 0.5, 0.6],
          coherence: 0.7
        }, { type: 'test', timestamp: Date.now() + i });
      }
      
      const recentMemories = memory.getRecentMemories(3);
      expect(Array.isArray(recentMemories)).toBe(true);
      expect(recentMemories.length).toBeGreaterThan(0);
    });
    
    test('Memory statistics track usage metrics', () => {
      const memoryStats = memory.getStats();
      expect(hasAllProperties(memoryStats, 
        ['memoriesStored', 'memoriesRetrieved', 'shortTermCount', 'longTermCount']))
        .toBe(true);
    });
  });
  
  describe('DecisionMaking Component', () => {
    let decision;
    let initialState;
    
    beforeEach(() => {
      // Setup decision making system for each test
      decision = new Prime.Consciousness.DecisionMaking({
        perspectives: 3,
        coherenceThreshold: 0.6
      });
      
      initialState = createInitialState();
      decision.initialize(initialState);
    });
    
    test('DecisionMaking can be instantiated', () => {
      expect(decision).toBeInstanceOf(Prime.Consciousness.DecisionMaking);
    });
    
    test('Can make simple decisions', () => {
      const alternatives = ["Option A", "Option B", "Option C"];
      const decisionResult = decision.decide(alternatives, initialState, { importance: 0.7 });
      
      expect(hasAllProperties(decisionResult, 
        ['selected', 'alternatives', 'certainty', 'coherence', 'explanation']))
        .toBe(true);
      
      expect(alternatives).toContain(decisionResult.selected);
      expect(decisionResult.certainty).toBeGreaterThanOrEqual(0);
      expect(decisionResult.certainty).toBeLessThanOrEqual(1);
    });
    
    test('Can make complex deliberative decisions', () => {
      const complexAlternatives = [
        { id: "opt1", name: "Complex Option A", coherence: 0.8, utility: 0.7 },
        { id: "opt2", name: "Complex Option B", coherence: 0.6, utility: 0.9 },
        { id: "opt3", name: "Complex Option C", coherence: 0.7, utility: 0.8 }
      ];
      
      const complexDecision = decision.decide(
        complexAlternatives, 
        initialState, 
        { importance: 0.9, deliberate: true }
      );
      
      expect(hasAllProperties(complexDecision, 
        ['selected', 'alternatives', 'certainty', 'coherence', 'explanation']))
        .toBe(true);
      
      expect(complexAlternatives).toContain(complexDecision.selected);
    });
    
    test('Can record decision outcomes', () => {
      // First make a decision
      const alternatives = ["Option A", "Option B", "Option C"];
      const decisionResult = decision.decide(alternatives, initialState, { importance: 0.7 });
      
      // Record outcome
      const recordResult = decision.recordOutcome(
        decisionResult.selected, 
        { success: 0.8, feedback: "Good outcome" }
      );
      
      expect(recordResult).toBe(true);
      
      // Check decision history
      const recentDecisions = decision.getRecentDecisions(3);
      expect(Array.isArray(recentDecisions)).toBe(true);
      expect(recentDecisions.length).toBeGreaterThan(0);
    });
  });
  
  describe('ThresholdManager Component', () => {
    let threshold;
    let initialState;
    
    beforeEach(() => {
      // Setup threshold manager for each test
      threshold = new Prime.Consciousness.ThresholdManager({
        baseCoherenceThreshold: 0.65,
        adaptationRate: 0.2
      });
      
      initialState = createInitialState();
      threshold.initialize(initialState);
    });
    
    test('ThresholdManager can be instantiated', () => {
      expect(threshold).toBeInstanceOf(Prime.Consciousness.ThresholdManager);
    });
    
    test('Can update thresholds', () => {
      const updatedThresholds = threshold.update(initialState);
      
      expect(hasAllProperties(updatedThresholds, 
        ['attention', 'awareness', 'coherence', 'integration', 'differentiation']))
        .toBe(true);
    });
    
    test('Can evaluate state transitions', () => {
      const newState = {
        id: 'new_state',
        vector: [0.7, 0.8, 0.75, 0.5, 0.4, 0.6, 0.7],
        coherence: 0.75
      };
      
      const transition = threshold.evaluateTransition(initialState, newState);
      
      expect(hasAllProperties(transition, 
        ['isSignificant', 'overallChange', 'coherence', 'transitions', 'thresholdExceeded']))
        .toBe(true);
    });
    
    test('Can set arousal level', () => {
      const arousalResult = threshold.setArousalLevel(0.8, { sustained: true });
      
      expect(hasAllProperties(arousalResult, ['previous', 'current', 'delta']))
        .toBe(true);
      
      expect(arousalResult.current).toBeGreaterThan(arousalResult.previous);
    });
    
    test('Can determine consciousness level', () => {
      const newState = {
        id: 'new_state',
        vector: [0.7, 0.8, 0.75, 0.5, 0.4, 0.6, 0.7],
        coherence: 0.75
      };
      
      const consciousnessLevel = threshold.determineConsciousnessLevel(newState);
      
      expect(hasAllProperties(consciousnessLevel, ['level', 'integrated', 'coherence']))
        .toBe(true);
      
      expect(typeof consciousnessLevel.level).toBe('string');
    });
  });
  
  describe('Full Consciousness Module Integration', () => {
    let module;
    
    beforeEach(() => {
      // Setup consciousness module for each test
      module = new Prime.Consciousness.Module({
        dimension: 7,
        coherenceThreshold: 0.7,
        meta: {
          id: 'test_consciousness_module',
          type: 'consciousness',
          name: 'Test Consciousness Module'
        }
      });
      
      module.initialize();
    });
    
    test('ConsciousnessModule can be instantiated and initialized', () => {
      expect(module).toBeInstanceOf(Prime.Consciousness.Module);
      expect(module.isInitialized).toBe(true);
      expect(module.isActive).toBe(true);
    });
    
    test('Can update module state', () => {
      const updatedState = module.update({ novelty: 0.8 });
      
      expect(hasAllProperties(updatedState, ['vector', 'coherence']))
        .toBe(true);
      expect(module.previousState).not.toBeNull();
    });
    
    test('Can make decisions through module', () => {
      const moduleDecision = module.decide(
        ["Module Option A", "Module Option B", "Module Option C"]
      );
      
      expect(hasAllProperties(moduleDecision, ['selected', 'alternatives']))
        .toBe(true);
    });
    
    test('Can retrieve memories through module', () => {
      // Update a few times to create memories
      for (let i = 0; i < 3; i++) {
        module.update({ novelty: 0.5 + i * 0.1 });
      }
      
      const updatedState = module.currentState;
      const moduleMemories = module.retrieveMemories(updatedState);
      
      expect(Array.isArray(moduleMemories)).toBe(true);
    });
    
    test('Can get consciousness level through module', () => {
      const moduleLevel = module.getConsciousnessLevel();
      
      expect(hasAllProperties(moduleLevel, ['level', 'integrated', 'coherence']))
        .toBe(true);
    });
    
    test('Can focus attention through module', () => {
      const attentionResult = module.focusAttention(2, 0.9);
      expect(typeof attentionResult).toBe('boolean');
    });
    
    test('Can set arousal level through module', () => {
      const moduleArousalResult = module.setArousalLevel(0.7);
      expect(moduleArousalResult.current).toBeDefined();
    });
    
    test('Fires events on module updates', () => {
      let updateEventFired = false;
      
      module.on('update', (data) => {
        updateEventFired = true;
        expect(data.state).not.toBeNull();
      });
      
      module.run(3);
      expect(updateEventFired).toBe(true);
    });
    
    test('Can create a system snapshot', () => {
      const snapshot = module.getSnapshot();
      
      expect(hasAllProperties(snapshot, 
        ['timestamp', 'currentState', 'selfModel', 'consciousness']))
        .toBe(true);
    });
    
    test('Module has pause/resume functionality', () => {
      module.pause();
      expect(module.isActive).toBe(false);
      
      module.resume();
      expect(module.isActive).toBe(true);
    });
    
    test('Module tracks statistics', () => {
      module.run(3); // Run to generate some stats
      
      const moduleStats = module.getStats();
      expect(hasAllProperties(moduleStats, 
        ['cycles', 'stateTransitions', 'decisions', 'averageCycleTime']))
        .toBe(true);
      
      expect(moduleStats.cycles).toBeGreaterThan(0);
    });
    
    test('Module can be reset', () => {
      module.reset();
      
      expect(module.isInitialized).toBe(false);
      expect(module.isActive).toBe(false);
      expect(module.currentState).toBeNull();
    });
  });
});