/**
 * Tests for PrimeOS Consciousness Module Integration
 *
 * These tests verify that the integrated ConsciousnessModule works correctly,
 * combining all the components into a coherent whole.
 */

// Import Prime with the Consciousness module
const Prime = require("../src");

describe("Consciousness Module Integration Tests", () => {
  describe("Module Initialization", () => {
    test("ConsciousnessModule can be instantiated", () => {
      const module = new Prime.Consciousness.Module({
        dimension: 7,
        coherenceThreshold: 0.7,
        timeStep: 0.1,
      });

      expect(module instanceof Prime.Consciousness.Module).toBe(true);
      expect(module.dimension).toBe(7);
      expect(module.coherenceThreshold).toBe(0.7);
      expect(module.timeStep).toBe(0.1);

      expect(module.isInitialized).toBe(false);
      expect(module.isActive).toBe(false);
      expect(module.currentState).toBe(null);
    });

    test("Module properly initializes", () => {
      const module = new Prime.Consciousness.Module({
        dimension: 5,
        coherenceThreshold: 0.6,
      });

      const initialState = module.initialize();

      expect(module.isInitialized).toBe(true);
      expect(module.isActive).toBe(true);
      expect(module.currentState).not.toBe(null);

      // Verify that all components are initialized
      expect(module.operator).not.toBe(null);
      expect(module.selfReference).not.toBe(null);
      expect(module.temporalIntegration).not.toBe(null);
      expect(module.memoryStructure).not.toBe(null);
      expect(module.decisionMaking).not.toBe(null);
      expect(module.thresholdManager).not.toBe(null);

      // Verify initial state properties
      expect(Array.isArray(initialState.vector)).toBe(true);
      expect(initialState.vector.length).toBe(5);
      expect(typeof initialState.coherence).toBe("number");
    });
  });

  describe("State Updates", () => {
    test("Basic state updates work correctly", () => {
      const module = new Prime.Consciousness.Module({
        dimension: 7,
        timeStep: 0.1,
      });

      module.initialize();
      const firstState = { ...module.currentState };

      // Run update cycle
      const updatedState = module.update();

      expect(updatedState).not.toBe(firstState);
      // Since we're using deep copy for previousState now, use deep equality instead of reference equality
      expect(JSON.stringify(module.previousState)).toBe(
        JSON.stringify(firstState),
      );

      // Run multiple updates
      module.run(5);

      expect(module._cycleCount).toBeGreaterThanOrEqual(6);
    });

    test("State updates with inputs", () => {
      // Create module with a neutral attention starting point
      const module = new Prime.Consciousness.Module({
        dimension: 5,
      });

      // Initialize with a neutral state so attention is consistently around 0.5
      module.initialize();

      // Get the initial state for reference
      const initialState = module.currentState;

      // Create a reference/control module with the same configuration
      const controlModule = new Prime.Consciousness.Module({
        dimension: 5,
      });
      controlModule.initialize();

      // Update both modules - one with attention input, one without
      const controlState = controlModule.update({}, 0.1); // No inputs, fixed deltaTime
      const updatedState = module.update(
        {
          attention: 0.9, // High attention input
          novelty: 0.8, // High novelty input
        },
        0.1,
      ); // Same deltaTime as control

      // The test should verify that external inputs create a DIFFERENCE
      // between the two module states, rather than testing absolute values
      // The module with attention input should have higher attention than the control
      expect(updatedState.attention).toBeGreaterThan(controlState.attention);

      // Also verify that inputs have effects on related dimensions
      // Novelty should influence differentiation
      expect(updatedState.differentiation).toBeGreaterThan(
        controlState.differentiation,
      );
    });

    test("Event listeners work correctly", () => {
      const module = new Prime.Consciousness.Module();
      module.initialize();

      let updateFired = false;
      let transitionFired = false;

      // Register event listeners
      const unsubscribeUpdate = module.on("update", (data) => {
        updateFired = true;
        expect(data.state).not.toBe(null);
        expect(data.previousState).not.toBe(null);
      });

      module.on("stateTransition", (data) => {
        transitionFired = true;
        expect(data.transition).not.toBe(null);
      });

      // Run updates to trigger events
      module.run(5);

      expect(updateFired).toBe(true);

      // Clean up listener
      unsubscribeUpdate();

      // Verify unsubscribe works
      updateFired = false;
      module.update();
      expect(updateFired).toBe(false);
    });
  });

  describe("Integration Features", () => {
    test("Attention focus works correctly", () => {
      const module = new Prime.Consciousness.Module({
        dimension: 7,
      });

      module.initialize();

      // Focus attention on a specific dimension
      const result = module.focusAttention(2, 0.9);
      expect(result).toBe(true);

      // Update state
      module.update();

      // Get attention field
      const attentionField = module.attentionMechanism.getAttentionField();

      // Log for debugging
      console.log("Attention field:", attentionField);
      console.log("Value at dimension 2:", attentionField[2]);

      // Verify that dimension 2 has high attention, since we focused on it
      expect(attentionField[2]).toBeGreaterThan(0.7);
    });

    test("Decision making works correctly", () => {
      const module = new Prime.Consciousness.Module();
      module.initialize();

      // Run a few cycles to develop state
      module.run(3);

      // Make a decision
      const alternatives = ["Option A", "Option B", "Option C"];
      const decision = module.decide(alternatives, { importance: 0.8 });

      expect(alternatives).toContain(decision.selected);
      expect(typeof decision.certainty).toBe("number");
      expect(typeof decision.coherence).toBe("number");
      expect(decision.alternatives.length).toBe(2);
    });

    test("Memory storage and retrieval works correctly", () => {
      const module = new Prime.Consciousness.Module();
      module.initialize();

      // Create different states by running updates
      for (let i = 0; i < 5; i++) {
        module.update({
          attention: 0.5 + i * 0.1,
          novelty: 0.3 + i * 0.1,
        });
      }

      // Query for similar states
      const query = {
        attention: 0.7,
        awareness: 0.6,
      };

      const memories = module.retrieveMemories(query);

      expect(Array.isArray(memories)).toBe(true);
      expect(memories.length).toBeGreaterThan(0);
      expect(typeof memories[0].similarity).toBe("number");
    });

    test("Consciousness level determination works", () => {
      const module = new Prime.Consciousness.Module();
      module.initialize();

      // Get initial consciousness level
      const level = module.getConsciousnessLevel();

      expect(typeof level.level).toBe("string");
      expect(typeof level.integrated).toBe("number");
      expect(typeof level.coherence).toBe("number");

      // Run updates to potentially change level
      module.run(5);

      // Get updated level
      const updatedLevel = module.getConsciousnessLevel();
      expect(updatedLevel).not.toBe(null);
    });

    test("Arousal level setting works correctly", () => {
      const module = new Prime.Consciousness.Module();
      module.initialize();

      // Set arousal to high level
      const result = module.setArousalLevel(0.9, { sustained: true });

      expect(result.previous).toBeLessThan(result.current);
      expect(result.current).toBeGreaterThan(0.8);

      // Should affect thresholds
      module.update();
      const thresholds = module.thresholdManager.getCurrentThresholds();

      // Higher arousal typically means higher thresholds
      expect(thresholds.adaptive.attention).toBeGreaterThan(
        module.thresholdManager.dimensionThresholds.attention,
      );
    });
  });

  describe("System Features", () => {
    test("System statistics work correctly", () => {
      const module = new Prime.Consciousness.Module();
      module.initialize();

      // Run several cycles
      module.run(10);

      // Get stats
      const stats = module.getStats();

      expect(stats.cycles).toBeGreaterThanOrEqual(10);
      expect(typeof stats.averageCycleTime).toBe("number");
      expect(typeof stats.operator).toBe("object");
      expect(typeof stats.attentionMechanism).toBe("object");
      expect(typeof stats.memoryStructure).toBe("object");
    });

    test("System snapshot works correctly", () => {
      const module = new Prime.Consciousness.Module();
      module.initialize();

      // Run a few cycles
      module.run(3);

      // Get snapshot
      const snapshot = module.getSnapshot();

      // Log snapshot for debugging
      console.log("Snapshot:", JSON.stringify(snapshot, null, 2));

      expect(typeof snapshot.timestamp).toBe("number");
      expect(snapshot.currentState).not.toBe(null);
      expect(typeof snapshot.consciousness).toBe("object");
      expect(typeof snapshot.arousal).toBe("object");

      // With our changes, attention is now an array
      expect(Array.isArray(snapshot.attention)).toBe(true);
    });

    test("Module lifecycle management works correctly", () => {
      const module = new Prime.Consciousness.Module();
      module.initialize();

      expect(module.isActive).toBe(true);

      // Pause module
      module.pause();
      expect(module.isActive).toBe(false);

      const stateBefore = module.currentState;

      // Update should not change state when paused
      module.update();
      expect(module.currentState).toBe(stateBefore);

      // Resume module
      module.resume();
      expect(module.isActive).toBe(true);

      // Update should change state when active
      module.update();
      expect(module.currentState).not.toBe(stateBefore);

      // Reset module
      module.reset();
      expect(module.isInitialized).toBe(false);
      expect(module.isActive).toBe(false);
      expect(module.currentState).toBe(null);
    });
  });
});
