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

// Define a simple test framework
const runTests = async () => {
  console.log("\n=== Running Consciousness Module Integration Tests ===\n");
  let passCount = 0;
  let failCount = 0;
  
  // Helper function for assertions
  const assert = (condition, message) => {
    if (!condition) {
      console.log(`❌ FAIL: ${message}`);
      failCount++;
      return false;
    }
    console.log(`✓ PASS: ${message}`);
    passCount++;
    return true;
  };

  // Helper function for approximate equality
  const assertApproximatelyEqual = (a, b, message, epsilon = 1e-6) => {
    const diff = Math.abs(a - b);
    return assert(diff <= epsilon, message);
  };

  // Helper for testing object properties
  const assertHasProperties = (obj, properties, message) => {
    const missing = properties.filter(prop => obj[prop] === undefined);
    return assert(missing.length === 0, 
      `${message} (missing: ${missing.length > 0 ? missing.join(', ') : 'none'})`);
  };

  try {
    // Test Group 1: MemoryStructure Component
    console.log("\n--- Memory Structure Tests ---");
    
    // Create memory structure
    const memory = new Prime.Consciousness.MemoryStructure({
      indexDimension: 7,
      shortTermCapacity: 20,
      longTermCapacity: 100
    });
    
    assert(memory instanceof Prime.Consciousness.MemoryStructure, 
      "MemoryStructure can be instantiated");
    
    // Test initialization
    const initialState = {
      id: 'initial_state',
      vector: [0.5, 0.6, 0.7, 0.4, 0.3, 0.5, 0.6],
      coherence: 0.7
    };
    
    const initialized = memory.initialize(initialState);
    assert(initialized, "MemoryStructure initializes successfully");
    
    // Test storing memories
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
      assert(memoryRecord !== null, `MemoryStructure stores state ${i+1}`);
    }
    
    // Test retrieving memories
    const retrieveQuery = {
      vector: [0.55, 0.65, 0.75, 0.45, 0.35, 0.55, 0.65]
    };
    
    const retrievedMemories = memory.retrieve(retrieveQuery, { limit: 3 });
    assert(Array.isArray(retrievedMemories), "MemoryStructure retrieves memories as array");
    assert(retrievedMemories.length > 0, "MemoryStructure finds matching memories");
    
    // Verify retrieved memory structure
    if (retrievedMemories.length > 0) {
      assertHasProperties(retrievedMemories[0], ['memory', 'similarity'], 
        "Retrieved memory has correct structure");
    }
    
    // Test recent memories
    const recentMemories = memory.getRecentMemories(3);
    assert(Array.isArray(recentMemories), "MemoryStructure returns recent memories");
    assert(recentMemories.length > 0, "MemoryStructure has recent memories");
    
    // Test statistics
    const memoryStats = memory.getStats();
    assertHasProperties(memoryStats, 
      ['memoriesStored', 'memoriesRetrieved', 'shortTermCount', 'longTermCount'], 
      "MemoryStructure statistics include core metrics");
    
    assert(memoryStats.memoriesStored >= 5, "Memory statistics track stored count");

    // Test Group 2: Decision Making Component
    console.log("\n--- Decision Making Tests ---");
    
    // Create decision making system
    const decision = new Prime.Consciousness.DecisionMaking({
      perspectives: 3,
      coherenceThreshold: 0.6
    });
    
    assert(decision instanceof Prime.Consciousness.DecisionMaking, 
      "DecisionMaking can be instantiated");
    
    // Test initialization
    const decisionInitialized = decision.initialize(initialState);
    assert(decisionInitialized, "DecisionMaking initializes successfully");
    
    // Test fast decision making
    const alternatives = ["Option A", "Option B", "Option C"];
    const decisionResult = decision.decide(alternatives, initialState, { importance: 0.7 });
    
    assertHasProperties(decisionResult, 
      ['selected', 'alternatives', 'certainty', 'coherence', 'explanation'], 
      "Decision result has correct structure");
    
    assert(alternatives.includes(decisionResult.selected), 
      "Decision selects from provided alternatives");
    
    assert(decisionResult.certainty >= 0 && decisionResult.certainty <= 1, 
      "Decision provides valid certainty value");
    
    // Test deliberative decision making
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
    
    assertHasProperties(complexDecision, 
      ['selected', 'alternatives', 'certainty', 'coherence', 'explanation'], 
      "Complex decision has correct structure");
    
    assert(complexAlternatives.includes(complexDecision.selected), 
      "Complex decision selects from provided alternatives");
    
    // Test outcome recording
    const recordResult = decision.recordOutcome(
      complexDecision.selected, 
      { success: 0.8, feedback: "Good outcome" }
    );
    
    assert(recordResult, "Decision outcome can be recorded");
    
    // Test decision history
    const recentDecisions = decision.getRecentDecisions(3);
    assert(Array.isArray(recentDecisions), "Decision history is tracked");
    assert(recentDecisions.length > 0, "Recent decisions can be retrieved");
    
    // Test Group 3: Threshold Manager Component
    console.log("\n--- Threshold Manager Tests ---");
    
    // Create threshold manager
    const threshold = new Prime.Consciousness.ThresholdManager({
      baseCoherenceThreshold: 0.65,
      adaptationRate: 0.2
    });
    
    assert(threshold instanceof Prime.Consciousness.ThresholdManager, 
      "ThresholdManager can be instantiated");
    
    // Test initialization
    const thresholdInitialized = threshold.initialize(initialState);
    assert(thresholdInitialized, "ThresholdManager initializes successfully");
    
    // Test threshold adaptation
    const updatedThresholds = threshold.update(initialState);
    assertHasProperties(updatedThresholds, 
      ['attention', 'awareness', 'coherence', 'integration', 'differentiation'], 
      "ThresholdManager updates thresholds");
    
    // Test transition evaluation
    const newState = {
      id: 'new_state',
      vector: [0.7, 0.8, 0.75, 0.5, 0.4, 0.6, 0.7],
      coherence: 0.75
    };
    
    const transition = threshold.evaluateTransition(initialState, newState);
    assertHasProperties(transition, 
      ['isSignificant', 'overallChange', 'coherence', 'transitions', 'thresholdExceeded'], 
      "Transition evaluation has correct structure");
    
    // Test arousal level setting
    const arousalResult = threshold.setArousalLevel(0.8, { sustained: true });
    assertHasProperties(arousalResult, 
      ['previous', 'current', 'delta'], 
      "Arousal update has correct structure");
    
    assert(arousalResult.current > arousalResult.previous, 
      "Arousal level can be increased");
    
    // Test consciousness level detection
    const consciousnessLevel = threshold.determineConsciousnessLevel(newState);
    assertHasProperties(consciousnessLevel, 
      ['level', 'integrated', 'coherence'], 
      "Consciousness level detection has correct structure");
    
    assert(typeof consciousnessLevel.level === 'string', 
      "Consciousness level has a valid name");
    
    // Test Group 4: Full Consciousness Module Integration
    console.log("\n--- Consciousness Module Integration Tests ---");
    
    // Create consciousness module with proper meta properties
    const module = new Prime.Consciousness.Module({
      dimension: 7,
      coherenceThreshold: 0.7,
      meta: {
        id: 'test_consciousness_module',
        type: 'consciousness',
        name: 'Test Consciousness Module'
      }
    });
    
    assert(module instanceof Prime.Consciousness.Module, 
      "ConsciousnessModule can be instantiated");
    
    // Test module initialization
    const moduleInitialState = module.initialize();
    assertHasProperties(moduleInitialState, 
      ['vector', 'coherence'], 
      "ConsciousnessModule initializes with valid state");
    
    assert(module.isInitialized, "Module is properly initialized");
    assert(module.isActive, "Module is active after initialization");
    
    // Test updating the module
    const updatedState = module.update({ novelty: 0.8 });
    assertHasProperties(updatedState, 
      ['vector', 'coherence'], 
      "ConsciousnessModule updates successfully");
    
    assert(module.previousState !== null, "Previous state is tracked");
    
    // Test decision making through module
    const moduleDecision = module.decide(
      ["Module Option A", "Module Option B", "Module Option C"]
    );
    
    assertHasProperties(moduleDecision, 
      ['selected', 'alternatives'], 
      "Module decision has correct structure");
    
    // Test memory retrieval through module
    const moduleMemories = module.retrieveMemories(updatedState);
    assert(Array.isArray(moduleMemories), "Module retrieves memories");
    
    // Test consciousness level through module
    const moduleLevel = module.getConsciousnessLevel();
    assertHasProperties(moduleLevel, 
      ['level', 'integrated', 'coherence'], 
      "Module consciousness level has correct structure");
    
    // Test attention focusing
    const attentionResult = module.focusAttention(2, 0.9);
    assert(typeof attentionResult === 'boolean', "Attention focus returns boolean result");
    
    // Test arousal setting through module
    const moduleArousalResult = module.setArousalLevel(0.7);
    assert(moduleArousalResult.current !== undefined, "Module arousal can be set");
    
    // Test event subscription
    let updateEventFired = false;
    module.on('update', (data) => {
      updateEventFired = true;
      assert(data.state !== null, "Update event includes state data");
    });
    
    // Run module to trigger events
    module.run(3);
    assert(updateEventFired, "Module events are fired properly");
    
    // Test module snapshot
    const snapshot = module.getSnapshot();
    assertHasProperties(snapshot, 
      ['timestamp', 'currentState', 'selfModel', 'consciousness'], 
      "Module snapshot has correct structure");
    
    // Test module pause/resume
    module.pause();
    assert(!module.isActive, "Module can be paused");
    
    module.resume();
    assert(module.isActive, "Module can be resumed");
    
    // Test module stats
    const moduleStats = module.getStats();
    assertHasProperties(moduleStats, 
      ['cycles', 'stateTransitions', 'decisions', 'averageCycleTime'],
      "Module statistics have correct structure");
    
    assert(moduleStats.cycles > 0, "Module stats track cycle count");
    
    // Test module reset
    module.reset();
    assert(!module.isInitialized, "Module can be reset");
    assert(!module.isActive, "Module is inactive after reset");
    assert(module.currentState === null, "Module state is cleared after reset");

    // Print summary
    console.log("\n=== Test Results ===");
    console.log(`Passed: ${passCount}, Failed: ${failCount}`);
    
    const success = failCount === 0;
    console.log(`\nOVERALL STATUS: ${success ? 'SUCCESS' : 'FAILURE'}`);
    return success;
  } catch (error) {
    console.error("\n❌ TEST ERROR:", error);
    console.error(error.stack);
    return false;
  }
};

// Run all tests
runTests().then(success => {
  if (!success) {
    process.exit(1);
  }
});