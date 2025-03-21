/**
 * PrimeOS JavaScript Library - Framework
 * Base 0: Coherence Validator
 * Enhanced validation primitives for system coherence
 */

// Import core
const Prime = require("../../core.js");
const Coherence = require("../../coherence.js");

// Import manifold implementation
const { Manifold, ManifoldSpace } = require("./manifold.js");

/**
 * CoherenceValidator - Enhanced validation system for mathematical coherence
 * Provides validation primitives for ensuring system-wide coherence
 */
class CoherenceValidator {
  /**
   * Create a new coherence validator
   * @param {Object} options - Configuration options
   * @param {number} options.defaultThreshold - Default coherence threshold (0-1)
   * @param {boolean} options.strictValidation - Whether to use strict validation
   * @param {Object} options.coherenceEngine - Reference to system coherence engine
   */
  constructor(options = {}) {
    this.defaultThreshold = options.defaultThreshold || 0.8;
    this.strictValidation = options.strictValidation || false;
    this.coherenceEngine =
      options.coherenceEngine ||
      (Prime.coherence ? Prime.coherence.systemCoherence : null);

    // Track validation results
    this._validationResults = [];
    this._validationStats = {
      validationsRun: 0,
      validationsPassed: 0,
      validationsFailed: 0,
      averageCoherence: 1.0,
    };

    // Validation rules registry
    this._validationRules = new Map();

    // Register built-in validation rules
    this._registerBuiltInRules();
  }

  /**
   * Register a validation rule
   * @param {string} ruleName - Unique rule identifier
   * @param {Function} ruleFn - Validation function
   * @param {string} description - Rule description
   * @returns {CoherenceValidator} This validator for chaining
   */
  registerRule(ruleName, ruleFn, description = "") {
    if (typeof ruleFn !== "function") {
      throw new Prime.ValidationError("Rule must be a function");
    }

    this._validationRules.set(ruleName, {
      name: ruleName,
      fn: ruleFn,
      description,
      usageCount: 0,
      passRate: 1.0,
    });

    return this;
  }

  /**
   * Validate a manifold for coherence
   * @param {Manifold} manifold - Manifold to validate
   * @param {Object} options - Validation options
   * @param {number} options.threshold - Coherence threshold
   * @param {Array} options.rules - Specific rules to apply
   * @returns {Object} Validation result
   */
  validateManifold(manifold, options = {}) {
    if (!(manifold instanceof Manifold)) {
      throw new Prime.ValidationError("Expected a Manifold instance");
    }

    const threshold = options.threshold || this.defaultThreshold;
    const rulesToApply =
      options.rules ||
      Array.from(this._validationRules.keys()).filter((rule) =>
        rule.startsWith("manifold:"),
      );

    // Initialize validation result
    const validationResult = {
      valid: true,
      coherence: 1.0,
      threshold,
      errors: [],
      warnings: [],
      ruleResults: [],
    };

    // Apply each rule
    for (const ruleName of rulesToApply) {
      const rule = this._validationRules.get(ruleName);

      if (!rule) {
        validationResult.warnings.push(`Rule '${ruleName}' not found`);
        continue;
      }

      try {
        // Apply the rule
        const ruleResult = rule.fn(manifold, options);
        rule.usageCount++;

        // Record rule result
        validationResult.ruleResults.push({
          rule: ruleName,
          passed: ruleResult.valid,
          score: ruleResult.score,
          message: ruleResult.message,
        });

        // Update rule pass rate
        const passCount = rule.passRate * rule.usageCount;
        rule.passRate =
          (passCount + (ruleResult.valid ? 1 : 0)) / (rule.usageCount + 1);

        // Check if rule failed
        if (!ruleResult.valid) {
          validationResult.valid = false;
          validationResult.errors.push({
            rule: ruleName,
            message: ruleResult.message,
            context: ruleResult.context,
          });
        }

        // Add warnings
        if (ruleResult.warnings && ruleResult.warnings.length > 0) {
          validationResult.warnings.push(
            ...ruleResult.warnings.map((w) => ({
              rule: ruleName,
              message: w.message,
              context: w.context,
            })),
          );
        }
      } catch (error) {
        validationResult.valid = false;
        validationResult.errors.push({
          rule: ruleName,
          message: `Rule execution error: ${error.message}`,
          error,
        });
      }
    }

    // Calculate overall coherence score
    if (validationResult.ruleResults.length > 0) {
      const totalScore = validationResult.ruleResults.reduce(
        (sum, result) => sum + (result.score || 0),
        0,
      );
      validationResult.coherence =
        totalScore / validationResult.ruleResults.length;
    }

    // Check against threshold
    validationResult.valid =
      validationResult.valid && validationResult.coherence >= threshold;

    // Update validation stats
    this._validationStats.validationsRun++;
    if (validationResult.valid) {
      this._validationStats.validationsPassed++;
    } else {
      this._validationStats.validationsFailed++;
    }

    // Update average coherence
    const totalCoherence =
      this._validationStats.averageCoherence *
        (this._validationStats.validationsRun - 1) +
      validationResult.coherence;
    this._validationStats.averageCoherence =
      totalCoherence / this._validationStats.validationsRun;

    // Store result
    this._validationResults.push({
      type: "manifold",
      target: manifold.getId(),
      result: validationResult,
      timestamp: new Date().toISOString(),
    });

    // Limit history size
    if (this._validationResults.length > 100) {
      this._validationResults.shift();
    }

    return validationResult;
  }

  /**
   * Validate a relationship between manifolds
   * @param {Manifold} source - Source manifold
   * @param {Manifold} target - Target manifold
   * @param {string} relationType - Type of relationship
   * @param {Object} options - Validation options
   * @returns {Object} Validation result
   */
  validateRelationship(source, target, relationType, options = {}) {
    if (!(source instanceof Manifold) || !(target instanceof Manifold)) {
      throw new Prime.ValidationError(
        "Source and target must be Manifold instances",
      );
    }

    if (!relationType) {
      throw new Prime.ValidationError("Relationship type is required");
    }

    const threshold = options.threshold || this.defaultThreshold;
    const rulesToApply =
      options.rules ||
      Array.from(this._validationRules.keys()).filter((rule) =>
        rule.startsWith("relation:"),
      );

    // Initialize validation result
    const validationResult = {
      valid: true,
      coherence: 1.0,
      threshold,
      errors: [],
      warnings: [],
      ruleResults: [],
    };

    // Apply each rule
    for (const ruleName of rulesToApply) {
      const rule = this._validationRules.get(ruleName);

      if (!rule) {
        validationResult.warnings.push(`Rule '${ruleName}' not found`);
        continue;
      }

      try {
        // Apply the rule
        const ruleResult = rule.fn(source, target, relationType, options);
        rule.usageCount++;

        // Record rule result
        validationResult.ruleResults.push({
          rule: ruleName,
          passed: ruleResult.valid,
          score: ruleResult.score,
          message: ruleResult.message,
        });

        // Update rule pass rate
        const passCount = rule.passRate * rule.usageCount;
        rule.passRate =
          (passCount + (ruleResult.valid ? 1 : 0)) / (rule.usageCount + 1);

        // Check if rule failed
        if (!ruleResult.valid) {
          validationResult.valid = false;
          validationResult.errors.push({
            rule: ruleName,
            message: ruleResult.message,
            context: ruleResult.context,
          });
        }

        // Add warnings
        if (ruleResult.warnings && ruleResult.warnings.length > 0) {
          validationResult.warnings.push(
            ...ruleResult.warnings.map((w) => ({
              rule: ruleName,
              message: w.message,
              context: w.context,
            })),
          );
        }
      } catch (error) {
        validationResult.valid = false;
        validationResult.errors.push({
          rule: ruleName,
          message: `Rule execution error: ${error.message}`,
          error,
        });
      }
    }

    // Calculate overall coherence score
    if (validationResult.ruleResults.length > 0) {
      const totalScore = validationResult.ruleResults.reduce(
        (sum, result) => sum + (result.score || 0),
        0,
      );
      validationResult.coherence =
        totalScore / validationResult.ruleResults.length;
    }

    // Check against threshold
    validationResult.valid =
      validationResult.valid && validationResult.coherence >= threshold;

    // Update validation stats
    this._validationStats.validationsRun++;
    if (validationResult.valid) {
      this._validationStats.validationsPassed++;
    } else {
      this._validationStats.validationsFailed++;
    }

    // Update average coherence
    const totalCoherence =
      this._validationStats.averageCoherence *
        (this._validationStats.validationsRun - 1) +
      validationResult.coherence;
    this._validationStats.averageCoherence =
      totalCoherence / this._validationStats.validationsRun;

    // Store result
    this._validationResults.push({
      type: "relationship",
      source: source.getId(),
      target: target.getId(),
      relationType,
      result: validationResult,
      timestamp: new Date().toISOString(),
    });

    return validationResult;
  }

  /**
   * Validate a manifold space
   * @param {ManifoldSpace} space - Space to validate
   * @param {Object} options - Validation options
   * @returns {Object} Validation result
   */
  validateSpace(space, options = {}) {
    if (!(space instanceof ManifoldSpace)) {
      throw new Prime.ValidationError("Expected a ManifoldSpace instance");
    }

    const threshold = options.threshold || this.defaultThreshold;
    const rulesToApply =
      options.rules ||
      Array.from(this._validationRules.keys()).filter((rule) =>
        rule.startsWith("space:"),
      );

    // Initialize validation result
    const validationResult = {
      valid: true,
      coherence: 1.0,
      threshold,
      errors: [],
      warnings: [],
      ruleResults: [],
    };

    // Apply each rule
    for (const ruleName of rulesToApply) {
      const rule = this._validationRules.get(ruleName);

      if (!rule) {
        validationResult.warnings.push(`Rule '${ruleName}' not found`);
        continue;
      }

      try {
        // Apply the rule
        const ruleResult = rule.fn(space, options);
        rule.usageCount++;

        // Record rule result
        validationResult.ruleResults.push({
          rule: ruleName,
          passed: ruleResult.valid,
          score: ruleResult.score,
          message: ruleResult.message,
        });

        // Update rule pass rate
        const passCount = rule.passRate * rule.usageCount;
        rule.passRate =
          (passCount + (ruleResult.valid ? 1 : 0)) / (rule.usageCount + 1);

        // Check if rule failed
        if (!ruleResult.valid) {
          validationResult.valid = false;
          validationResult.errors.push({
            rule: ruleName,
            message: ruleResult.message,
            context: ruleResult.context,
          });
        }

        // Add warnings
        if (ruleResult.warnings && ruleResult.warnings.length > 0) {
          validationResult.warnings.push(
            ...ruleResult.warnings.map((w) => ({
              rule: ruleName,
              message: w.message,
              context: w.context,
            })),
          );
        }
      } catch (error) {
        validationResult.valid = false;
        validationResult.errors.push({
          rule: ruleName,
          message: `Rule execution error: ${error.message}`,
          error,
        });
      }
    }

    // Calculate overall coherence score
    if (validationResult.ruleResults.length > 0) {
      const totalScore = validationResult.ruleResults.reduce(
        (sum, result) => sum + (result.score || 0),
        0,
      );
      validationResult.coherence =
        totalScore / validationResult.ruleResults.length;
    }

    // Check against threshold
    validationResult.valid =
      validationResult.valid && validationResult.coherence >= threshold;

    // Update validation stats
    this._validationStats.validationsRun++;
    if (validationResult.valid) {
      this._validationStats.validationsPassed++;
    } else {
      this._validationStats.validationsFailed++;
    }

    // Update average coherence
    const totalCoherence =
      this._validationStats.averageCoherence *
        (this._validationStats.validationsRun - 1) +
      validationResult.coherence;
    this._validationStats.averageCoherence =
      totalCoherence / this._validationStats.validationsRun;

    // Store result
    this._validationResults.push({
      type: "space",
      target: space.id,
      result: validationResult,
      timestamp: new Date().toISOString(),
    });

    return validationResult;
  }

  /**
   * Validate a complex system of manifolds and spaces
   * @param {Object} system - System to validate
   * @param {Array} system.manifolds - Manifolds in the system
   * @param {Array} system.spaces - Spaces in the system
   * @param {Array} system.relationships - Relationships in the system
   * @param {Object} options - Validation options
   * @returns {Object} Validation result
   */
  validateSystem(system, options = {}) {
    if (!system || !system.manifolds) {
      throw new Prime.ValidationError("System must contain manifolds");
    }

    const threshold = options.threshold || this.defaultThreshold;

    // Initialize validation result
    const validationResult = {
      valid: true,
      coherence: 1.0,
      threshold,
      errors: [],
      warnings: [],
      manifoldResults: [],
      spaceResults: [],
      relationshipResults: [],
    };

    // Validate manifolds
    for (const manifold of system.manifolds) {
      const manifoldResult = this.validateManifold(manifold, options);
      validationResult.manifoldResults.push({
        manifold: manifold.getId(),
        result: manifoldResult,
      });

      if (!manifoldResult.valid) {
        validationResult.valid = false;
        validationResult.errors.push({
          type: "manifold",
          target: manifold.getId(),
          errors: manifoldResult.errors,
        });
      }

      if (manifoldResult.warnings && manifoldResult.warnings.length > 0) {
        validationResult.warnings.push({
          type: "manifold",
          target: manifold.getId(),
          warnings: manifoldResult.warnings,
        });
      }
    }

    // Validate spaces
    if (system.spaces) {
      for (const space of system.spaces) {
        const spaceResult = this.validateSpace(space, options);
        validationResult.spaceResults.push({
          space: space.id,
          result: spaceResult,
        });

        if (!spaceResult.valid) {
          validationResult.valid = false;
          validationResult.errors.push({
            type: "space",
            target: space.id,
            errors: spaceResult.errors,
          });
        }

        if (spaceResult.warnings && spaceResult.warnings.length > 0) {
          validationResult.warnings.push({
            type: "space",
            target: space.id,
            warnings: spaceResult.warnings,
          });
        }
      }
    }

    // Validate relationships
    if (system.relationships) {
      for (const relationship of system.relationships) {
        const { source, target, type } = relationship;

        const relationshipResult = this.validateRelationship(
          source,
          target,
          type,
          options,
        );

        validationResult.relationshipResults.push({
          source: source.getId(),
          target: target.getId(),
          type,
          result: relationshipResult,
        });

        if (!relationshipResult.valid) {
          validationResult.valid = false;
          validationResult.errors.push({
            type: "relationship",
            source: source.getId(),
            target: target.getId(),
            relationType: type,
            errors: relationshipResult.errors,
          });
        }

        if (
          relationshipResult.warnings &&
          relationshipResult.warnings.length > 0
        ) {
          validationResult.warnings.push({
            type: "relationship",
            source: source.getId(),
            target: target.getId(),
            relationType: type,
            warnings: relationshipResult.warnings,
          });
        }
      }
    }

    // Calculate system coherence
    const manifoldCoherences = validationResult.manifoldResults.map(
      (r) => r.result.coherence,
    );
    const spaceCoherences = validationResult.spaceResults.map(
      (r) => r.result.coherence,
    );
    const relationshipCoherences = validationResult.relationshipResults.map(
      (r) => r.result.coherence,
    );

    const allCoherences = [
      ...manifoldCoherences,
      ...spaceCoherences,
      ...relationshipCoherences,
    ];

    if (allCoherences.length > 0) {
      const totalCoherence = allCoherences.reduce(
        (sum, score) => sum + score,
        0,
      );
      validationResult.coherence = totalCoherence / allCoherences.length;
    }

    // Check against threshold
    validationResult.valid =
      validationResult.valid && validationResult.coherence >= threshold;

    return validationResult;
  }

  /**
   * Get validation statistics
   * @returns {Object} Validation statistics
   */
  getValidationStats() {
    return { ...this._validationStats };
  }

  /**
   * Get recent validation results
   * @param {number} limit - Maximum number of results to return
   * @returns {Array} Recent validation results
   */
  getRecentValidations(limit = 10) {
    return this._validationResults.slice(-limit);
  }

  /**
   * Get information about registered rules
   * @returns {Array} Rule information
   */
  getRuleInfo() {
    return Array.from(this._validationRules.entries()).map(([name, rule]) => ({
      name,
      description: rule.description,
      usageCount: rule.usageCount,
      passRate: rule.passRate,
    }));
  }

  /**
   * Register built-in validation rules
   * @private
   */
  _registerBuiltInRules() {
    // Manifold structure validation
    this.registerRule(
      "manifold:structure",
      (manifold) => {
        const hasMeta = manifold.meta && Object.keys(manifold.meta).length > 0;
        const hasInvariant =
          manifold.invariant && Object.keys(manifold.invariant).length > 0;

        const valid = hasMeta;
        const warnings = [];

        if (!hasInvariant) {
          warnings.push({
            message: "Manifold has no invariant properties",
            context: { manifoldId: manifold.getId() },
          });
        }

        return {
          valid,
          score: valid ? 1.0 : 0.5,
          message: valid
            ? "Manifold has valid structure"
            : "Manifold missing required structure",
          warnings,
          context: {
            hasMeta,
            hasInvariant,
          },
        };
      },
      "Validates the basic structure of a manifold (meta, invariant, variant)",
    );

    // Manifold depth validation
    this.registerRule(
      "manifold:depth",
      (manifold) => {
        const valid = typeof manifold.depth === "number" && manifold.depth >= 0;

        return {
          valid,
          score: valid ? 1.0 : 0.7,
          message: valid
            ? "Manifold has valid depth"
            : "Manifold has invalid depth",
          context: { depth: manifold.depth },
        };
      },
      "Validates that a manifold has a valid depth value",
    );

    // Manifold coherence validation
    this.registerRule(
      "manifold:coherence",
      (manifold) => {
        const coherenceScore = manifold.getCoherenceScore();
        const valid = coherenceScore >= manifold._coherenceThreshold;

        return {
          valid,
          score: coherenceScore,
          message: valid
            ? `Manifold coherence score (${coherenceScore.toFixed(2)}) is above threshold`
            : `Manifold coherence score (${coherenceScore.toFixed(2)}) is below threshold`,
          context: {
            coherenceScore,
            threshold: manifold._coherenceThreshold,
          },
        };
      },
      "Validates that a manifold meets its coherence threshold",
    );

    // Relationship depth validation
    this.registerRule(
      "relation:depth",
      (source, target, relationType) => {
        // Validate based on relationship type and depth
        const sourceDepth = source.getDepth();
        const targetDepth = target.getDepth();

        let valid = true;
        let message = "Relationship depths are valid";

        // For parent-child relationships, child should have higher depth
        if (relationType === "parent" && sourceDepth >= targetDepth) {
          valid = false;
          message = "Parent manifold should have lower depth than child";
        }

        // For peer relationships, depths should be similar
        if (
          relationType === "peer" &&
          Math.abs(sourceDepth - targetDepth) > 1
        ) {
          valid = false;
          message = "Peer manifolds should have similar depths";
        }

        return {
          valid,
          score: valid ? 1.0 : 0.5,
          message,
          context: {
            sourceDepth,
            targetDepth,
            relationType,
          },
        };
      },
      "Validates the depth relationship between connected manifolds",
    );

    // Space dimensionality validation
    this.registerRule(
      "space:dimension",
      (space) => {
        const valid =
          typeof space.dimension === "number" && space.dimension >= 0;

        return {
          valid,
          score: valid ? 1.0 : 0.8,
          message: valid
            ? "Space has valid dimension"
            : "Space has invalid dimension",
          context: { dimension: space.dimension },
        };
      },
      "Validates that a space has a valid dimension",
    );

    // Space coherence validation
    this.registerRule(
      "space:coherence",
      (space) => {
        const manifolds = space.getManifolds();

        // Empty space is valid
        if (manifolds.length === 0) {
          return {
            valid: true,
            score: 1.0,
            message: "Space is empty and coherent",
            context: { manifoldCount: 0 },
          };
        }

        // Check coherence between all manifolds in the space
        let totalCoherence = 0;
        let pairCount = 0;

        for (let i = 0; i < manifolds.length; i++) {
          for (let j = i + 1; j < manifolds.length; j++) {
            const coherence = manifolds[i].checkCoherenceWith(manifolds[j]);
            totalCoherence += coherence.score;
            pairCount++;
          }
        }

        const averageCoherence =
          pairCount > 0 ? totalCoherence / pairCount : 1.0;
        const valid = averageCoherence >= 0.7; // 0.7 is threshold for space coherence

        return {
          valid,
          score: averageCoherence,
          message: valid
            ? `Space manifolds are coherent (${averageCoherence.toFixed(2)})`
            : `Space manifolds lack coherence (${averageCoherence.toFixed(2)})`,
          context: {
            manifoldCount: manifolds.length,
            averageCoherence,
            threshold: 0.7,
          },
        };
      },
      "Validates the coherence of manifolds within a space",
    );
  }
}

module.exports = CoherenceValidator;
