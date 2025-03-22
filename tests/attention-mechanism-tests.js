/**
 * Tests for PrimeOS Consciousness Module - AttentionMechanism
 */

// Import Prime with the Consciousness module
const Prime = require("../src");
const AttentionMechanism = Prime.Consciousness.AttentionMechanism;
const StateRepresentation = Prime.Consciousness.StateRepresentation;

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
  console.log("=== Running AttentionMechanism Tests ===\n");

  // Test: Basic instantiation
  console.log("--- Basic Instantiation Tests ---");
  {
    const attention = new AttentionMechanism();
    
    assert(
      attention instanceof AttentionMechanism,
      "AttentionMechanism can be instantiated"
    );
    
    assert(
      attention.attentionCapacity === 1.0,
      "Default attention capacity is 1.0"
    );
    
    assert(
      attention.fieldDimension === 7,
      "Default field dimension is 7"
    );
    
    assert(
      Array.isArray(attention.attentionField.values),
      "Attention field values are initialized"
    );
    
    assert(
      attention.attentionField.values.length === 7,
      "Attention field has correct dimensions"
    );
  }
  
  // Test: Initialization with state
  console.log("\n--- Initialization Tests ---");
  {
    const attention = new AttentionMechanism({
      fieldDimension: 5,
      attentionCapacity: 1.5
    });
    
    // Create a test state
    const testState = {
      attention: 0.5,
      awareness: 0.6,
      coherence: 0.7,
      integration: 0.4,
      differentiation: 0.3
    };
    
    assert(
      attention.initialize(testState),
      "Can initialize with a state"
    );
    
    assert(
      attention.attentionField.values.some(v => v > 0),
      "Attention values initialized from state"
    );
    
    assert(
      Object.keys(attention.lastCoherenceMap).length > 0,
      "Coherence map initialized"
    );
  }
  
  // Test: Attention update
  console.log("\n--- Attention Update Tests ---");
  {
    const attention = new AttentionMechanism();
    
    // Create state representation helper
    const stateRep = new StateRepresentation();
    
    // Create initial state
    const initialState = stateRep.createInitialState('neutral');
    
    // Initialize attention with state
    attention.initialize(initialState);
    
    // Record initial values
    const initialValues = [...attention.attentionField.values];
    
    // Create a simulated next state with higher coherence
    const nextState = stateRep.createInitialState('focused');
    
    // Update attention with new state
    attention.update(nextState, initialState);
    
    // Attention should change in response to the coherence gradient
    assert(
      !attention.attentionField.values.every((v, i) => v === initialValues[i]),
      "Attention field changes after update"
    );
    
    assert(
      attention.attentionField.hotspots.length > 0,
      "Hotspots detected after update"
    );
  }
  
  // Test: Focus and release
  console.log("\n--- Focus and Release Tests ---");
  {
    const attention = new AttentionMechanism();
    
    // Initialize with empty state
    attention.initialize({});
    
    // Focus on specific dimension
    assert(
      attention.focus(2, 0.8),
      "Can focus on a specific dimension"
    );
    
    assert(
      attention.attentionField.values[2] === 0.8,
      "Attention value set correctly after focus"
    );
    
    assert(
      attention.focusPoints.length === 1,
      "Focus point added"
    );
    
    assert(
      attention.focusPoints[0].dimension === 2,
      "Focus point has correct dimension"
    );
    
    // Release focus
    assert(
      attention.releaseFocus(2),
      "Can release focus"
    );
    
    assert(
      attention.focusPoints.length === 0,
      "Focus point removed after release"
    );
    
    assert(
      attention.attentionField.values[2] < 0.8,
      "Attention value reduced after release"
    );
  }
  
  // Test: Attention capacity
  console.log("\n--- Attention Capacity Tests ---");
  {
    const attention = new AttentionMechanism({
      attentionCapacity: 1.0
    });
    
    // Initialize
    attention.initialize({});
    
    // Focus on multiple dimensions
    attention.focus(0, 0.5);
    attention.focus(1, 0.5);
    
    // This should succeed but may be adjusted based on capacity
    assert(
      attention.focus(2, 0.5),
      "Can add focus within capacity"
    );
    
    // Check total capacity used
    const stats = attention.getStats();
    assert(
      stats.currentCapacity <= stats.maxCapacity,
      "Capacity constraints respected"
    );
    
    // Reset for next test
    attention.reset();
    
    // Set a limited capacity
    attention.attentionCapacity = 0.3;
    attention.initialize({});
    
    // Fill capacity
    attention.focus(0, 0.3);
    
    // Try to exceed capacity with high intensity focus
    const canExceedCapacity = attention.focus(1, 1.0);
    
    // Either it fails or it reduces intensity automatically
    if (canExceedCapacity) {
      const intensityLimited = attention.attentionField.values[1] < 1.0;
      assert(
        intensityLimited,
        "Focus intensity limited based on capacity"
      );
    } else {
      assert(
        !canExceedCapacity,
        "Cannot exceed attention capacity"
      );
    }
  }
  
  // Test: Attention decay
  console.log("\n--- Attention Decay Tests ---");
  {
    const attention = new AttentionMechanism({
      decayRate: 0.5  // High decay for testing
    });
    
    // Initialize
    attention.initialize({});
    
    // Focus fully on a dimension
    attention.focus(3, 1.0);
    
    // Record current value
    const initialValue = attention.attentionField.values[3];
    
    // Manipulate timestamp to simulate time passing
    attention._lastUpdateTime = Date.now() - 1000;  // 1 second ago
    
    // Update to trigger decay
    attention.update({});
    
    assert(
      attention.attentionField.values[3] < initialValue,
      "Attention decays over time"
    );
  }
  
  // Test: Apply attention to state
  console.log("\n--- Apply Attention Tests ---");
  {
    const attention = new AttentionMechanism();
    
    // Create a test state
    const testState = {
      vector: [0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5],
      attention: 0.5,
      awareness: 0.5,
      coherence: 0.5,
      integration: 0.5,
      differentiation: 0.5,
      selfReference: 0.5,
      temporalBinding: 0.5
    };
    
    // Initialize
    attention.initialize(testState);
    
    // Focus strongly on one dimension
    attention.focus(2, 1.0);  // High focus on coherence
    
    // Apply attention to state
    const modulatedState = attention.applyAttentionToState(testState);
    
    assert(
      modulatedState !== null,
      "Returns a modulated state"
    );
    
    assert(
      modulatedState !== testState,
      "Does not modify original state"
    );
    
    assert(
      modulatedState.coherence > testState.coherence,
      "High attention enhances the corresponding dimension"
    );
    
    assert(
      modulatedState._attention !== undefined,
      "Modulated state includes attention metadata"
    );
  }
  
  // Test: Attention mask
  console.log("\n--- Attention Mask Tests ---");
  {
    const attention = new AttentionMechanism();
    
    // Initialize
    attention.initialize({});
    
    // Apply focus to several dimensions
    attention.focus(0, 0.8);
    attention.focus(1, 0.7);
    attention.focus(2, 0.6);
    
    // Create a mask that blocks dimension 0
    const mask = [0, 1, 1, 1, 1, 1, 1];
    
    assert(
      attention.setAttentionMask(mask),
      "Can set attention mask"
    );
    
    assert(
      attention.attentionField.values[0] === 0,
      "Masked dimension has zero attention"
    );
    
    assert(
      attention.attentionField.values[1] > 0,
      "Unmasked dimension retains attention"
    );
  }
  
  // Test: Visualization data
  console.log("\n--- Visualization Data Tests ---");
  {
    const attention = new AttentionMechanism();
    
    // Initialize
    attention.initialize({});
    
    // Add some focus points
    attention.focus(1, 0.7);
    attention.focus(3, 0.8);
    
    // Get visualization data
    const visData = attention.getVisualizationData();
    
    assert(
      Array.isArray(visData.dimensions),
      "Visualization data includes dimension labels"
    );
    
    assert(
      Array.isArray(visData.dataset),
      "Visualization data includes dataset"
    );
    
    assert(
      visData.dimensions.length === attention.fieldDimension,
      "Correct number of dimension labels"
    );
    
    assert(
      visData.dataset.length === attention.fieldDimension,
      "Dataset has entry for each dimension"
    );
    
    assert(
      typeof visData.globalAttention === 'number',
      "Includes global attention value"
    );
    
    assert(
      Array.isArray(visData.focusPoints),
      "Includes focus points data"
    );
  }
  
  console.log("\n=== All AttentionMechanism Tests Passed ===");
};

// Run the tests
try {
  runTests();
} catch (error) {
  console.error("Test failed:", error.message);
  console.error(error.stack);
  process.exit(1);
}