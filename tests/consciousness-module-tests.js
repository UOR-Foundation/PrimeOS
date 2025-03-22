/**
 * Tests for PrimeOS Consciousness Module Integration
 * 
 * These tests verify that the integrated ConsciousnessModule works correctly,
 * combining all the components into a coherent whole.
 */

// Import Prime with the Consciousness module
const Prime = require("../src");

// Test utilities
const assert = (condition, message) => {
  if (!condition) {
    throw new Error(`Assertion failed: ${message}`);
  }
  console.log(`✓ PASS: ${message}`);
};

const assertApproximatelyEqual = (a, b, message, epsilon = 1e-6) => {
  const diff = Math.abs(a - b);
  if (diff > epsilon) {
    throw new Error(
      `Assertion failed: ${message} - values differ by ${diff} (${a} vs ${b})`,
    );
  }
  console.log(`✓ PASS: ${message}`);
};

const runTests = async () => {
  console.log("=== Running Consciousness Module Integration Tests ===\n");

  // Test group: Module Initialization
  console.log("--- Module Initialization Tests ---");

  // Test module creation
  {
    const module = new Prime.Consciousness.Module({
      dimension: 7,
      coherenceThreshold: 0.7,
      timeStep: 0.1
    });

    assert(
      module instanceof Prime.Consciousness.Module,
      "ConsciousnessModule can be instantiated"
    );

    assert(module.dimension === 7, "Module has correct dimension");
    assert(module.coherenceThreshold === 0.7, "Module has correct threshold");
    assert(module.timeStep === 0.1, "Module has correct time step");
    
    assert(!module.isInitialized, "Module starts uninitialized");
    assert(!module.isActive, "Module starts inactive");
    assert(module.currentState === null, "Module starts with no state");
  }

  // Test module initialization
  {
    const module = new Prime.Consciousness.Module({
      dimension: 5,
      coherenceThreshold: 0.6
    });

    const initialState = module.initialize();

    assert(module.isInitialized, "Module is initialized after initialize()");
    assert(module.isActive, "Module becomes active after initialize()");
    assert(module.currentState !== null, "Module has a current state");
    
    // Verify that all components are initialized
    assert(module.operator !== null, "Operator component is initialized");
    assert(module.selfReference !== null, "SelfReference component is initialized");
    assert(module.temporalIntegration !== null, "TemporalIntegration component is initialized");
    assert(module.memoryStructure !== null, "MemoryStructure component is initialized");
    assert(module.decisionMaking !== null, "DecisionMaking component is initialized");
    assert(module.thresholdManager !== null, "ThresholdManager component is initialized");
    
    // Verify initial state properties
    assert(Array.isArray(initialState.vector), "Initial state has a vector");
    assert(initialState.vector.length === 5, "Vector has correct dimension");
    assert(typeof initialState.coherence === 'number', "State has coherence value");
  }

  // Test group: State Updates
  console.log("\n--- State Update Tests ---");

  // Test basic state update
  {
    const module = new Prime.Consciousness.Module({
      dimension: 7,
      timeStep: 0.1
    });

    module.initialize();
    const firstState = { ...module.currentState };
    
    // Run update cycle
    const updatedState = module.update();
    
    assert(updatedState !== firstState, "Update produces a new state");
    assert(module.previousState === firstState, "Previous state is tracked");
    
    // Run multiple updates
    module.run(5);
    
    assert(module._cycleCount >= 6, "Cycle count increases with updates");
  }

  // Test state with inputs
  {
    const module = new Prime.Consciousness.Module({
      dimension: 5
    });

    module.initialize();
    
    // Update with external inputs
    const updatedState = module.update({
      attention: 0.8,
      novelty: 0.6
    });
    
    // Inputs should influence state
    assert(
      updatedState.attention > module.previousState.attention,
      "External attention input influences state"
    );
  }

  // Test event listeners
  {
    const module = new Prime.Consciousness.Module();
    module.initialize();
    
    let updateFired = false;
    let transitionFired = false;
    
    // Register event listeners
    const unsubscribeUpdate = module.on('update', (data) => {
      updateFired = true;
      assert(data.state !== null, "Update event includes state");
      assert(data.previousState !== null, "Update event includes previous state");
    });
    
    module.on('stateTransition', (data) => {
      transitionFired = true;
      assert(data.transition !== null, "Transition event includes transition info");
    });
    
    // Run updates to trigger events
    module.run(5);
    
    assert(updateFired, "Update event triggered");
    
    // Clean up listener
    unsubscribeUpdate();
    
    // Verify unsubscribe works
    updateFired = false;
    module.update();
    assert(!updateFired, "Unsubscribed listener not triggered");
  }

  // Test group: Integration Features
  console.log("\n--- Integration Feature Tests ---");

  // Test attention focus
  {
    const module = new Prime.Consciousness.Module({
      dimension: 7
    });

    module.initialize();
    
    // Focus attention on a specific dimension
    const result = module.focusAttention(2, 0.9);
    assert(result === true, "Attention focus succeeds");
    
    // Update state
    module.update();
    
    // Get attention field
    const attentionField = module.attentionMechanism.getAttentionField();
    assert(attentionField[2] > 0.7, "Attention field reflects focus");
  }

  // Test decision making
  {
    const module = new Prime.Consciousness.Module();
    module.initialize();
    
    // Run a few cycles to develop state
    module.run(3);
    
    // Make a decision
    const alternatives = ['Option A', 'Option B', 'Option C'];
    const decision = module.decide(alternatives, { importance: 0.8 });
    
    assert(alternatives.includes(decision.selected), "Decision selects from alternatives");
    assert(typeof decision.certainty === 'number', "Decision includes certainty");
    assert(typeof decision.coherence === 'number', "Decision includes coherence");
    assert(decision.alternatives.length === 2, "Decision includes non-selected alternatives");
  }

  // Test memory storage and retrieval
  {
    const module = new Prime.Consciousness.Module();
    module.initialize();
    
    // Create different states by running updates
    for (let i = 0; i < 5; i++) {
      module.update({
        attention: 0.5 + i * 0.1,
        novelty: 0.3 + i * 0.1
      });
    }
    
    // Query for similar states
    const query = {
      attention: 0.7,
      awareness: 0.6
    };
    
    const memories = module.retrieveMemories(query);
    
    assert(Array.isArray(memories), "Memory retrieval returns an array");
    assert(memories.length > 0, "Memories are retrieved");
    assert(typeof memories[0].similarity === 'number', "Memories include similarity score");
  }

  // Test consciousness level determination
  {
    const module = new Prime.Consciousness.Module();
    module.initialize();
    
    // Get initial consciousness level
    const level = module.getConsciousnessLevel();
    
    assert(typeof level.level === 'string', "Consciousness level has a name");
    assert(typeof level.integrated === 'number', "Consciousness level has integrated value");
    assert(typeof level.coherence === 'number', "Consciousness level has coherence value");
    
    // Run updates to potentially change level
    module.run(5);
    
    // Get updated level
    const updatedLevel = module.getConsciousnessLevel();
    assert(updatedLevel !== null, "Can get updated consciousness level");
  }

  // Test arousal level setting
  {
    const module = new Prime.Consciousness.Module();
    module.initialize();
    
    // Set arousal to high level
    const result = module.setArousalLevel(0.9, { sustained: true });
    
    assert(result.previous < result.current, "Arousal level increases");
    assert(result.current > 0.8, "Arousal level is set correctly");
    
    // Should affect thresholds
    module.update();
    const thresholds = module.thresholdManager.getCurrentThresholds();
    
    // Higher arousal typically means higher thresholds
    assert(
      thresholds.adaptive.attention > module.thresholdManager.dimensionThresholds.attention,
      "Arousal affects adaptive thresholds"
    );
  }

  // Test system statistics
  {
    const module = new Prime.Consciousness.Module();
    module.initialize();
    
    // Run several cycles
    module.run(10);
    
    // Get stats
    const stats = module.getStats();
    
    assert(stats.cycles >= 10, "Stats track cycle count");
    assert(typeof stats.averageCycleTime === 'number', "Stats include timing information");
    assert(typeof stats.operator === 'object', "Stats include component-specific stats");
    assert(typeof stats.attentionMechanism === 'object', "Stats include attention mechanism stats");
    assert(typeof stats.memoryStructure === 'object', "Stats include memory structure stats");
  }

  // Test system snapshot
  {
    const module = new Prime.Consciousness.Module();
    module.initialize();
    
    // Run a few cycles
    module.run(3);
    
    // Get snapshot
    const snapshot = module.getSnapshot();
    
    assert(typeof snapshot.timestamp === 'number', "Snapshot includes timestamp");
    assert(snapshot.currentState !== null, "Snapshot includes current state");
    assert(typeof snapshot.consciousness === 'object', "Snapshot includes consciousness level");
    assert(typeof snapshot.arousal === 'object', "Snapshot includes arousal state");
    assert(Array.isArray(snapshot.attention), "Snapshot includes attention field");
  }

  // Test module lifecycle
  {
    const module = new Prime.Consciousness.Module();
    module.initialize();
    
    assert(module.isActive, "Module is active after initialization");
    
    // Pause module
    module.pause();
    assert(!module.isActive, "Module becomes inactive after pause()");
    
    const stateBefore = module.currentState;
    
    // Update should not change state when paused
    module.update();
    assert(module.currentState === stateBefore, "State doesn't change when paused");
    
    // Resume module
    module.resume();
    assert(module.isActive, "Module becomes active after resume()");
    
    // Update should change state when active
    module.update();
    assert(module.currentState !== stateBefore, "State changes when active");
    
    // Reset module
    module.reset();
    assert(!module.isInitialized, "Module is uninitialized after reset()");
    assert(!module.isActive, "Module is inactive after reset()");
    assert(module.currentState === null, "Module has no state after reset()");
  }

  console.log("\n=== All Consciousness Module Integration Tests Passed ===");
};

// Run the tests
try {
  runTests();
} catch (error) {
  console.error("Test failed:", error.message);
  console.error(error.stack);
  process.exit(1);
}