/**
 * Tests for PrimeOS Consciousness Module - AttentionMechanism
 */

// Import Prime with the Consciousness module
const Prime = require("../src");
const AttentionMechanism = Prime.Consciousness.AttentionMechanism;
const StateRepresentation = Prime.Consciousness.StateRepresentation;

describe("AttentionMechanism Tests", () => {
  describe("Basic Instantiation", () => {
    test("AttentionMechanism can be instantiated with default parameters", () => {
      const attention = new AttentionMechanism();

      expect(attention instanceof AttentionMechanism).toBe(true);
      expect(attention.attentionCapacity).toBe(1.0);
      expect(attention.fieldDimension).toBe(7);
      expect(Array.isArray(attention.attentionField.values)).toBe(true);
      expect(attention.attentionField.values.length).toBe(7);
    });
  });

  describe("Initialization", () => {
    test("Can initialize with a state", () => {
      const attention = new AttentionMechanism({
        fieldDimension: 5,
        attentionCapacity: 1.5,
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
      expect(attention.attentionField.values.some((v) => v > 0)).toBe(true);
      expect(Object.keys(attention.lastCoherenceMap).length).toBeGreaterThan(0);
    });
  });

  describe("Attention Update", () => {
    test("Attention field changes after update", () => {
      const attention = new AttentionMechanism();

      // Create state representation helper
      const stateRep = new StateRepresentation();

      // Create initial state
      const initialState = stateRep.createInitialState("neutral");

      // Initialize attention with state
      attention.initialize(initialState);

      // Record initial values
      const initialValues = [...attention.attentionField.values];

      // Create a simulated next state with higher coherence
      const nextState = stateRep.createInitialState("focused");

      // Update attention with new state
      attention.update(nextState, initialState);

      // Attention should change in response to the coherence gradient
      const unchanged = attention.attentionField.values.every(
        (v, i) => v === initialValues[i],
      );
      expect(unchanged).toBe(false);
      expect(attention.attentionField.hotspots.length).toBeGreaterThan(0);
    });
  });

  describe("Focus and Release", () => {
    test("Can focus and release attention on specific dimensions", () => {
      const attention = new AttentionMechanism();

      // Initialize with empty state
      attention.initialize({});

      // Focus on specific dimension
      const focusResult = attention.focus(2, 0.8);
      expect(focusResult).toBe(true);
      expect(attention.attentionField.values[2]).toBe(0.8);
      expect(attention.focusPoints.length).toBe(1);
      expect(attention.focusPoints[0].dimension).toBe(2);

      // Release focus
      const releaseResult = attention.releaseFocus(2);
      expect(releaseResult).toBe(true);
      expect(attention.focusPoints.length).toBe(0);
      expect(attention.attentionField.values[2]).toBeLessThan(0.8);
    });
  });

  describe("Attention Capacity", () => {
    test("Capacity constraints are respected", () => {
      const attention = new AttentionMechanism({
        attentionCapacity: 1.0,
      });

      // Initialize
      attention.initialize({});

      // Focus on multiple dimensions
      attention.focus(0, 0.5);
      attention.focus(1, 0.5);

      // This should succeed but may be adjusted based on capacity
      const canFocus = attention.focus(2, 0.5);
      expect(canFocus).toBe(true);

      // Check total capacity used
      const stats = attention.getStats();
      expect(stats.currentCapacity).toBeLessThanOrEqual(stats.maxCapacity);
    });

    test("Focus intensity may be limited based on capacity", () => {
      const attention = new AttentionMechanism();

      // Reset for clean state
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
        expect(attention.attentionField.values[1]).toBeLessThan(1.0);
      } else {
        expect(canExceedCapacity).toBe(false);
      }
    });
  });

  describe("Attention Decay", () => {
    test("Attention decays over time", () => {
      const attention = new AttentionMechanism({
        decayRate: 0.5, // High decay for testing
      });

      // Initialize
      attention.initialize({});

      // Focus fully on a dimension
      attention.focus(3, 1.0);

      // Record current value
      const initialValue = attention.attentionField.values[3];

      // Manipulate timestamp to simulate time passing
      attention._lastUpdateTime = Date.now() - 1000; // 1 second ago

      // Update to trigger decay
      attention.update({});

      expect(attention.attentionField.values[3]).toBeLessThan(initialValue);
    });
  });

  describe("Apply Attention", () => {
    test("Applying attention enhances corresponding dimensions", () => {
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
        temporalBinding: 0.5,
      };

      // Initialize
      attention.initialize(testState);

      // Focus strongly on one dimension
      attention.focus(2, 1.0); // High focus on coherence

      // Apply attention to state
      const modulatedState = attention.applyAttentionToState(testState);

      expect(modulatedState).not.toBeNull();
      expect(modulatedState).not.toBe(testState);
      expect(modulatedState.coherence).toBeGreaterThan(testState.coherence);
      expect(modulatedState._attention).toBeDefined();
    });
  });

  describe("Attention Mask", () => {
    test("Attention mask can filter attention allocation", () => {
      const attention = new AttentionMechanism();

      // Initialize
      attention.initialize({});

      // Apply focus to several dimensions
      attention.focus(0, 0.8);
      attention.focus(1, 0.7);
      attention.focus(2, 0.6);

      // Create a mask that blocks dimension 0
      const mask = [0, 1, 1, 1, 1, 1, 1];

      const result = attention.setAttentionMask(mask);
      expect(result).toBe(true);
      expect(attention.attentionField.values[0]).toBe(0);
      expect(attention.attentionField.values[1]).toBeGreaterThan(0);
    });
  });

  describe("Visualization Data", () => {
    test("Can generate visualization data", () => {
      const attention = new AttentionMechanism();

      // Initialize
      attention.initialize({});

      // Add some focus points
      attention.focus(1, 0.7);
      attention.focus(3, 0.8);

      // Get visualization data
      const visData = attention.getVisualizationData();

      expect(Array.isArray(visData.dimensions)).toBe(true);
      expect(Array.isArray(visData.dataset)).toBe(true);
      expect(visData.dimensions.length).toBe(attention.fieldDimension);
      expect(visData.dataset.length).toBe(attention.fieldDimension);
      expect(typeof visData.globalAttention).toBe("number");
      expect(Array.isArray(visData.focusPoints)).toBe(true);
    });
  });
});
