/**
 * PrimeOS JavaScript Library - Consciousness Module Unit Tests
 * Tests for the primary ConsciousnessModule component
 */

const Prime = require("../../../src/core.js");
require("../../../src/math/index.js");
require("../../../src/consciousness/index.js");

// Import test utilities
const { assertThrows } = require("../../utils/assertions");

describe("Consciousness Module", () => {
  describe("Instantiation and Configuration", () => {
    test("should instantiate with default parameters", () => {
      const module = new Prime.Consciousness.Module();

      expect(module instanceof Prime.Consciousness.Module).toBe(true);
      expect(module.dimension).toBeGreaterThan(0);
      expect(module.coherenceThreshold).toBeGreaterThan(0);
      expect(module.timeStep).toBeGreaterThan(0);
      expect(module.isInitialized).toBe(false);
      expect(module.isActive).toBe(false);
      expect(module.currentState).toBe(null);
    });

    test("should accept custom configuration parameters", () => {
      const module = new Prime.Consciousness.Module({
        dimension: 7,
        coherenceThreshold: 0.7,
        timeStep: 0.1,
      });

      expect(module.dimension).toBe(7);
      expect(module.coherenceThreshold).toBe(0.7);
      expect(module.timeStep).toBe(0.1);
    });

    test("should apply valid range constraints to parameters", () => {
      // Create with invalid parameters
      const module = new Prime.Consciousness.Module({
        dimension: 0, // Invalid
        coherenceThreshold: 2.0, // Above 1.0
        timeStep: -0.1, // Negative
      });

      // Should have auto-corrected to valid values
      expect(module.dimension).toBeGreaterThan(0);
      expect(module.coherenceThreshold).toBeGreaterThan(0);
      expect(module.coherenceThreshold).toBeLessThanOrEqual(1.0);
      expect(module.timeStep).toBeGreaterThan(0);
    });
  });

  describe("Initialization", () => {
    test("should initialize all components", () => {
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
    });

    test("should initialize with provided initial state", () => {
      const module = new Prime.Consciousness.Module({
        dimension: 3,
      });

      const initialState = {
        id: "custom_initial",
        vector: [0.3, 0.4, 0.3],
        coherence: 0.8,
      };

      module.initialize(initialState);

      // Initial state should be used
      expect(module.currentState).not.toBe(null);
      expect(module.currentState.id).toBe("custom_initial");
      expect(module.currentState.coherence).toBe(0.8);
    });

    test("should create valid initial state when none provided", () => {
      const module = new Prime.Consciousness.Module({
        dimension: 4,
      });

      const initialState = module.initialize();

      // Should generate a valid state
      expect(initialState).not.toBe(null);
      expect(initialState.vector.length).toBe(4);
      expect(initialState.coherence).toBeGreaterThanOrEqual(0);
      expect(initialState.coherence).toBeLessThanOrEqual(1);
    });
  });

  describe("Control Methods", () => {
    let module;

    beforeEach(() => {
      module = new Prime.Consciousness.Module({
        dimension: 5,
      });
      module.initialize();
    });

    test("should activate and deactivate", () => {
      // Start active after initialization
      expect(module.isActive).toBe(true);

      // Deactivate
      module.deactivate();
      expect(module.isActive).toBe(false);

      // Activate again
      module.activate();
      expect(module.isActive).toBe(true);
    });

    test("should process inputs correctly", () => {
      const input = {
        value: [0.2, 0.3, 0.4, 0.5, 0.6],
        importance: 0.7,
      };

      // Get initial state
      const startState = module.currentState;

      // Process input
      const result = module.processInput(input);

      // Should return a result
      expect(result).not.toBe(null);

      // Should have updated state
      expect(module.currentState).not.toBe(startState);
    });

    test("should not process when inactive", () => {
      module.deactivate();

      const input = {
        value: [0.2, 0.3, 0.4, 0.5, 0.6],
        importance: 0.7,
      };

      // Get initial state
      const startState = module.currentState;

      // Process input
      const result = module.processInput(input);

      // Should not have processed
      expect(result).toBe(null);

      // State should not have changed
      expect(module.currentState).toBe(startState);
    });
  });

  describe("State Management", () => {
    let module;

    beforeEach(() => {
      module = new Prime.Consciousness.Module({
        dimension: 3,
      });
      module.initialize();
    });

    test("should update state", () => {
      const newState = {
        id: "updated_state",
        vector: [0.4, 0.3, 0.3],
        coherence: 0.75,
      };

      const previousState = module.currentState;

      // Update state
      module.updateState(newState);

      // State should be updated
      expect(module.currentState).not.toBe(previousState);
      expect(module.currentState.id).toBe("updated_state");
      expect(module.currentState.coherence).toBe(0.75);
    });

    test("should generate consistent state IDs", () => {
      // Generate some states
      const state1 = module._generateStateId();
      const state2 = module._generateStateId();
      const state3 = module._generateStateId();

      // IDs should be unique
      expect(state1).not.toBe(state2);
      expect(state2).not.toBe(state3);
      expect(state1).not.toBe(state3);

      // IDs should match expected format
      expect(typeof state1).toBe("string");
      expect(state1.length).toBeGreaterThan(0);
    });
  });
});
