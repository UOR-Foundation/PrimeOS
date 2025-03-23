/**
 * PrimeOS JavaScript Library - Distributed Coherence Violations Module
 * Defines coherence violation types, severity levels, and detection logic
 */

// Import the Prime object from core
const Prime = require('../core');

/**
 * Coherence violation types for distributed systems
 * @enum {string}
 */
const CoherenceViolationType = {
  /** Numerical precision violations */
  NUMERICAL: 'numerical',
  /** Network split/partition violations */
  NETWORK: 'network',
  /** Parameter synchronization violations */
  SYNCHRONIZATION: 'synchronization',
  /** Mathematical property violations */
  MATHEMATICAL: 'mathematical',
  /** Gradient divergence violations */
  GRADIENT: 'gradient',
  /** Dimensionality violations */
  DIMENSIONAL: 'dimensional',
};

/**
 * Severity levels for coherence violations
 * @enum {string}
 */
const ViolationSeverity = {
  /** Minor issues that can be automatically corrected */
  LOW: 'low',
  /** Significant issues requiring attention */
  MEDIUM: 'medium',
  /** Critical issues requiring immediate action */
  HIGH: 'high',
  /** Fatal issues requiring system shutdown */
  CRITICAL: 'critical',
};

/**
 * Violation detection utilities for coherence checks
 */
const ViolationDetector = {
  /**
   * Detect numerical precision violations in tensor data
   * @param {Array|Array<Array>} tensor - Tensor to check
   * @param {number} threshold - Numerical precision threshold
   * @returns {Object} Detection result with violations
   */
  detectNumericalViolations: function (tensor, threshold = 1e-7) {
    if (!Array.isArray(tensor)) {
      return {
        hasViolations: false,
        message: 'Invalid tensor format',
      };
    }

    const violations = [];
    const isMatrix = Array.isArray(tensor[0]);

    if (isMatrix) {
      // Check 2D tensor/matrix
      for (let i = 0; i < tensor.length; i++) {
        const row = tensor[i];
        if (!Array.isArray(row)) continue;

        for (let j = 0; j < row.length; j++) {
          const value = row[j];
          if (!Number.isFinite(value)) {
            violations.push({
              type: CoherenceViolationType.NUMERICAL,
              severity: ViolationSeverity.HIGH,
              location: [i, j],
              value,
              message: `Non-finite value at position [${i}, ${j}]`,
            });
          } else if (Math.abs(value) > 0 && Math.abs(value) < threshold) {
            violations.push({
              type: CoherenceViolationType.NUMERICAL,
              severity: ViolationSeverity.LOW,
              location: [i, j],
              value,
              message: `Value below precision threshold at position [${i}, ${j}]`,
            });
          }
        }
      }
    } else {
      // Check 1D tensor/vector
      for (let i = 0; i < tensor.length; i++) {
        const value = tensor[i];
        if (!Number.isFinite(value)) {
          violations.push({
            type: CoherenceViolationType.NUMERICAL,
            severity: ViolationSeverity.HIGH,
            location: [i],
            value,
            message: `Non-finite value at position [${i}]`,
          });
        } else if (Math.abs(value) > 0 && Math.abs(value) < threshold) {
          violations.push({
            type: CoherenceViolationType.NUMERICAL,
            severity: ViolationSeverity.LOW,
            location: [i],
            value,
            message: `Value below precision threshold at position [${i}]`,
          });
        }
      }
    }

    return {
      hasViolations: violations.length > 0,
      violations,
      violationsCount: violations.length,
      message:
        violations.length > 0
          ? `Found ${violations.length} numerical violations`
          : 'No numerical violations detected',
    };
  },

  /**
   * Detect gradient explosion or vanishing in gradient data
   * @param {Array|Array<Array>} gradients - Gradient tensor to check
   * @param {Object} options - Detection options
   * @returns {Object} Detection result with violations
   */
  detectGradientViolations: function (gradients, options = {}) {
    const explodinThreshold = options.explodinThreshold || 1e4;
    const vanishingThreshold = options.vanishingThreshold || 1e-10;

    if (!Array.isArray(gradients)) {
      return {
        hasViolations: false,
        message: 'Invalid gradient format',
      };
    }

    let maxAbsGradient = 0;
    let minAbsNonZeroGradient = Infinity;
    let nonFiniteCount = 0;
    let totalElements = 0;

    // Process gradient values
    const processValue = (value) => {
      totalElements++;

      if (!Number.isFinite(value)) {
        nonFiniteCount++;
        return;
      }

      const absValue = Math.abs(value);
      if (absValue > 0) {
        maxAbsGradient = Math.max(maxAbsGradient, absValue);
        minAbsNonZeroGradient = Math.min(minAbsNonZeroGradient, absValue);
      }
    };

    // Traverse gradients structure
    const isMatrix = Array.isArray(gradients[0]);
    if (isMatrix) {
      for (const row of gradients) {
        if (!Array.isArray(row)) continue;
        for (const value of row) {
          processValue(value);
        }
      }
    } else {
      for (const value of gradients) {
        processValue(value);
      }
    }

    // Detect violations
    const violations = [];

    // Check for non-finite values
    if (nonFiniteCount > 0) {
      violations.push({
        type: CoherenceViolationType.GRADIENT,
        severity: ViolationSeverity.CRITICAL,
        nonFiniteCount,
        message: `Found ${nonFiniteCount} non-finite gradient values`,
      });
    }

    // Check for exploding gradients
    if (maxAbsGradient > explodinThreshold) {
      violations.push({
        type: CoherenceViolationType.GRADIENT,
        severity: ViolationSeverity.HIGH,
        maxAbsGradient,
        message: `Exploding gradient detected: max absolute value ${maxAbsGradient}`,
      });
    }

    // Check for vanishing gradients
    if (
      minAbsNonZeroGradient < Infinity &&
      minAbsNonZeroGradient < vanishingThreshold
    ) {
      violations.push({
        type: CoherenceViolationType.GRADIENT,
        severity: ViolationSeverity.MEDIUM,
        minAbsNonZeroGradient,
        message: `Vanishing gradient detected: min non-zero absolute value ${minAbsNonZeroGradient}`,
      });
    }

    return {
      hasViolations: violations.length > 0,
      violations,
      violationsCount: violations.length,
      isExploding: maxAbsGradient > explodinThreshold,
      isVanishing: minAbsNonZeroGradient < vanishingThreshold,
      stats: {
        maxAbsGradient,
        minAbsNonZeroGradient,
        nonFiniteCount,
        totalElements,
      },
      message:
        violations.length > 0
          ? `Found ${violations.length} gradient violations`
          : 'No gradient violations detected',
    };
  },

  /**
   * Detect dimensional coherence violations in neural network layers
   * @param {Object} layer - Layer to check
   * @returns {Object} Detection result with violations
   */
  detectDimensionalViolations: function (layer) {
    if (!layer || !layer.config) {
      return {
        hasViolations: true,
        violations: [
          {
            type: CoherenceViolationType.DIMENSIONAL,
            severity: ViolationSeverity.HIGH,
            message: 'Missing layer configuration',
          },
        ],
        message: 'Missing layer configuration',
      };
    }

    const violations = [];

    // Check weight matrix dimensions
    if (layer.weights) {
      // Check weights are an array
      if (!Array.isArray(layer.weights)) {
        violations.push({
          type: CoherenceViolationType.DIMENSIONAL,
          severity: ViolationSeverity.HIGH,
          message: 'Weights must be an array',
        });
      } else {
        // Check rows match input size
        if (layer.weights.length !== layer.config.inputSize) {
          violations.push({
            type: CoherenceViolationType.DIMENSIONAL,
            severity: ViolationSeverity.HIGH,
            actual: layer.weights.length,
            expected: layer.config.inputSize,
            message: `Weight rows (${layer.weights.length}) don't match input size (${layer.config.inputSize})`,
          });
        }

        // Check each row is an array
        const nonArrayRows = layer.weights.filter(
          (row) => !Array.isArray(row),
        ).length;
        if (nonArrayRows > 0) {
          violations.push({
            type: CoherenceViolationType.DIMENSIONAL,
            severity: ViolationSeverity.HIGH,
            count: nonArrayRows,
            message: `Found ${nonArrayRows} non-array rows in weights`,
          });
        } else if (layer.weights.length > 0) {
          // Check columns match output size
          if (layer.weights[0].length !== layer.config.outputSize) {
            violations.push({
              type: CoherenceViolationType.DIMENSIONAL,
              severity: ViolationSeverity.HIGH,
              actual: layer.weights[0].length,
              expected: layer.config.outputSize,
              message: `Weight columns (${layer.weights[0].length}) don't match output size (${layer.config.outputSize})`,
            });
          }

          // Check all rows have same length
          const inconsistentRows = layer.weights.filter(
            (row) => row.length !== layer.weights[0].length,
          ).length;
          if (inconsistentRows > 0) {
            violations.push({
              type: CoherenceViolationType.DIMENSIONAL,
              severity: ViolationSeverity.HIGH,
              count: inconsistentRows,
              message: `Found ${inconsistentRows} rows with inconsistent length`,
            });
          }
        }
      }
    }

    // Check bias vector dimensions
    if (layer.biases) {
      // Check biases are an array
      if (!Array.isArray(layer.biases)) {
        violations.push({
          type: CoherenceViolationType.DIMENSIONAL,
          severity: ViolationSeverity.HIGH,
          message: 'Biases must be an array',
        });
      } else if (layer.biases.length !== layer.config.outputSize) {
        violations.push({
          type: CoherenceViolationType.DIMENSIONAL,
          severity: ViolationSeverity.HIGH,
          actual: layer.biases.length,
          expected: layer.config.outputSize,
          message: `Bias length (${layer.biases.length}) doesn't match output size (${layer.config.outputSize})`,
        });
      }
    }

    return {
      hasViolations: violations.length > 0,
      violations,
      violationsCount: violations.length,
      message:
        violations.length > 0
          ? `Found ${violations.length} dimensional violations`
          : 'No dimensional violations detected',
    };
  },
};

// Add to Prime namespace
Prime.Distributed = Prime.Distributed || {};
Prime.Distributed.Coherence = Prime.Distributed.Coherence || {};
Prime.Distributed.Coherence.Violations = {
  Types: CoherenceViolationType,
  Severity: ViolationSeverity,
  Detector: ViolationDetector,
};

module.exports = Prime;
