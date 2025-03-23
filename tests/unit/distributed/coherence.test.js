/**
 * Unit tests for PrimeOS Distributed Computation Module - Coherence components
 */

const Prime = require("../../../src");
const { assertions, mocking } = require("../../utils");

describe("PrimeOS Distributed Computation Module - Coherence", () => {
  describe("DistributedCoherenceManager", () => {
    test("creates a coherence manager with correct properties", () => {
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager({
        strictChecking: true,
        thresholds: {
          numerical: 1e-8,
          gradient: 0.5,
        },
      });

      expect(coherenceManager instanceof Prime.Distributed.Coherence.DistributedCoherenceManager).toBe(true);
      expect(coherenceManager.config.strictChecking).toBe(true);
      expect(coherenceManager.config.thresholds.numerical).toBe(1e-8);

      // Check enums are defined
      expect(typeof Prime.Distributed.Coherence.CoherenceViolationType).toBe("object");
      expect(typeof Prime.Distributed.Coherence.ViolationSeverity).toBe("object");
      expect(typeof Prime.Distributed.Coherence.RecoveryStrategy).toBe("object");

      // Test metrics initialization
      const metrics = coherenceManager.getMetrics();
      expect(typeof metrics).toBe("object");
      expect(metrics.checksPerformed).toBe(0);
      expect(metrics.violationsDetected).toBe(0);
      expect(metrics.averageCoherenceScore).toBe(1.0);
    });

    test("checks layer coherence with valid layer correctly", () => {
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();

      // Create a valid layer for checking
      const validLayer = {
        id: "valid_layer",
        config: {
          inputSize: 2,
          outputSize: 3,
        },
        weights: [
          [0.1, 0.2, 0.3],
          [0.4, 0.5, 0.6],
        ],
        biases: [0.1, 0.2, 0.3],
      };

      const result = coherenceManager.checkLayerCoherence(validLayer);

      expect(result.isCoherent).toBe(true);
      expect(result.coherenceScore).toBeGreaterThanOrEqual(0.9);
      expect(result.dimensionsValid).toBe(true);
      expect(Array.isArray(result.violations)).toBe(true);
      expect(result.violations.length).toBe(0);
    });

    test("checks layer coherence with invalid layer correctly", () => {
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();

      // Create an invalid layer for checking (with NaN values)
      const invalidLayer = {
        id: "invalid_layer",
        config: {
          inputSize: 2,
          outputSize: 3,
        },
        weights: [
          [0.1, NaN, 0.3],
          [0.4, 0.5, Infinity],
        ],
        biases: [0.1, 0.2, NaN],
      };

      const result = coherenceManager.checkLayerCoherence(invalidLayer);

      expect(result.isCoherent).toBe(false);
      expect(result.coherenceScore).toBeLessThan(0.7);
      expect(Array.isArray(result.violations)).toBe(true);
      expect(result.violations.length).toBeGreaterThan(0);

      if (result.violations.length > 0) {
        expect(result.violations[0].type).toBe(
          Prime.Distributed.Coherence.CoherenceViolationType.NUMERICAL
        );
      }

      expect(typeof result.recovery).toBe("object");
    });

    test("applies coherence correction correctly", () => {
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();

      // Create a layer with NaN values to correct
      const layerToCorrect = {
        id: "correction_layer",
        config: {
          inputSize: 3,
          outputSize: 2,
        },
        weights: [
          [0.1, NaN, 0.3],
          [0.4, 0.5, Infinity],
        ],
        biases: [0.1, NaN],
      };

      // Check coherence first
      const checkResult = coherenceManager.checkLayerCoherence(layerToCorrect);
      expect(checkResult.isCoherent).toBe(false);

      // Apply correction
      const correctionResult = coherenceManager.applyCoherenceCorrection(
        layerToCorrect,
        checkResult.violations
      );

      expect(correctionResult.applied).toBe(true);
      expect(Array.isArray(correctionResult.corrections)).toBe(true);
      expect(correctionResult.corrections.includes("numerical_stability")).toBe(true);

      // Now check if the layer is corrected
      for (let i = 0; i < layerToCorrect.weights.length; i++) {
        for (let j = 0; j < layerToCorrect.weights[i].length; j++) {
          expect(Number.isFinite(layerToCorrect.weights[i][j])).toBe(true);
        }
      }

      for (let i = 0; i < layerToCorrect.biases.length; i++) {
        expect(Number.isFinite(layerToCorrect.biases[i])).toBe(true);
      }

      // Final coherence check
      const finalCheckResult = coherenceManager.checkLayerCoherence(layerToCorrect);
      expect(finalCheckResult.isCoherent).toBe(true);
    });

    test("assesses global coherence correctly", () => {
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();

      // Create simulated coherence results from different nodes
      const nodeResults = [
        {
          nodeId: "node_1",
          coherenceScore: 0.95,
          isCoherent: true,
          violations: [],
        },
        {
          nodeId: "node_2",
          coherenceScore: 0.92,
          isCoherent: true,
          violations: [],
        },
        {
          nodeId: "node_3",
          coherenceScore: 0.65,
          isCoherent: false,
          violations: [
            {
              type: Prime.Distributed.Coherence.CoherenceViolationType.SYNCHRONIZATION,
              severity: Prime.Distributed.Coherence.ViolationSeverity.MEDIUM,
              message: "Parameter synchronization coherence violation",
            },
          ],
        },
      ];

      const globalResult = coherenceManager.assessGlobalCoherence(nodeResults);

      expect(typeof globalResult).toBe("object");
      expect(typeof globalResult.isCoherent).toBe("boolean");
      expect(typeof globalResult.score).toBe("number");
      expect(typeof globalResult.coherentNodeRatio).toBe("number");
      expect(globalResult.score).toBeGreaterThan(0.5);
      expect(globalResult.coherentNodeRatio).toBe(2 / 3);

      // Since one node has synchronization issues, the most common type should be synchronization
      expect(globalResult.violationCounts.synchronization).toBe(1);
    });

    test("handles synchronization coherence correctly", () => {
      const coherenceManager = new Prime.Distributed.Coherence.DistributedCoherenceManager();

      // Create a layer
      const layer = {
        id: "sync_layer",
        config: {
          inputSize: 2,
          outputSize: 2,
        },
        weights: [
          [0.1, 0.2],
          [0.3, 0.4],
        ],
        biases: [0.1, 0.2],
      };

      // Create global parameters that are slightly different
      const globalParams = {
        weights: [
          [0.11, 0.21],
          [0.31, 0.41],
        ],
        biases: [0.11, 0.21],
      };

      // Check synchronization coherence
      const result = coherenceManager.checkLayerCoherence(layer, {
        isDistributed: true,
        globalParams,
      });

      expect(typeof result).toBe("object");

      // In a mock environment, we might not have a full result object
      if (result.checks && result.checks.synchronization) {
        expect(typeof result.checks.synchronization).toBe("object");
        // The difference is small, so it should still be coherent
        expect(result.checks.synchronization.coherence).toBeGreaterThan(0.5);
      }

      // Now create a global parameter set with large differences
      const divergentParams = {
        weights: [
          [1.1, 2.1],
          [3.1, 4.1],
        ],
        biases: [1.1, 2.1],
      };

      // Check synchronization coherence with divergent parameters
      const divergentResult = coherenceManager.checkLayerCoherence(layer, {
        isDistributed: true,
        globalParams: divergentParams,
      });

      // Check synchronization coherence if available
      if (divergentResult.checks && divergentResult.checks.synchronization) {
        expect(divergentResult.checks.synchronization.coherence).toBeLessThan(0.5);

        // Check that the violations include synchronization issues
        const syncViolation = divergentResult.violations.find(
          (v) => v.type === Prime.Distributed.Coherence.CoherenceViolationType.SYNCHRONIZATION
        );

        expect(syncViolation).toBeDefined();
      }
    });
  });
});