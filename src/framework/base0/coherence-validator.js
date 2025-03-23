/**
 * Coherence Validator for the Prime Framework
 * Enhanced version with formal UOR (Universal Object Reference) constraints
 * Includes specialized validation for manifolds and cross-manifold coherence
 *
 * This file serves as the main entry point for coherence validation
 * and re-exports functionality from modular components
 */

// Import the Prime object for namespace handling
const Prime = require("../../core");

// Ensure the Prime.Framework.Base0 namespace exists
Prime.Framework = Prime.Framework || {};
Prime.Framework.Base0 = Prime.Framework.Base0 || {};

// Import required modules directly
const {
  CoherenceConstraints,
  CoherenceNorms,
} = require("./coherence-constraints.js");
const { CoherenceValidator } = require("./coherence-validation.js");
const { MathematicalCoherenceValidator } = require("./manifold-validator.js");

// Add components to the Prime namespace with proper circular dependency handling
// For CoherenceValidator
if (
  Object.getOwnPropertyDescriptor(
    Prime.Framework.Base0,
    "CoherenceValidator",
  ) &&
  Object.getOwnPropertyDescriptor(Prime.Framework.Base0, "CoherenceValidator")
    .get
) {
  const descriptor = Object.getOwnPropertyDescriptor(
    Prime.Framework.Base0,
    "CoherenceValidator",
  );
  const originalGetter = descriptor.get;

  Object.defineProperty(Prime.Framework.Base0, "CoherenceValidator", {
    get: function () {
      const result = originalGetter.call(this);
      if (!result || Object.keys(result).length === 0) {
        return CoherenceValidator;
      }
      return result;
    },
    configurable: true,
  });
} else {
  Prime.Framework.Base0.CoherenceValidator = CoherenceValidator;
}

// For MathematicalCoherenceValidator
if (
  Object.getOwnPropertyDescriptor(
    Prime.Framework.Base0,
    "MathematicalCoherenceValidator",
  ) &&
  Object.getOwnPropertyDescriptor(
    Prime.Framework.Base0,
    "MathematicalCoherenceValidator",
  ).get
) {
  const descriptor = Object.getOwnPropertyDescriptor(
    Prime.Framework.Base0,
    "MathematicalCoherenceValidator",
  );
  const originalGetter = descriptor.get;

  Object.defineProperty(
    Prime.Framework.Base0,
    "MathematicalCoherenceValidator",
    {
      get: function () {
        const result = originalGetter.call(this);
        if (!result || Object.keys(result).length === 0) {
          return MathematicalCoherenceValidator;
        }
        return result;
      },
      configurable: true,
    },
  );
} else {
  Prime.Framework.Base0.MathematicalCoherenceValidator =
    MathematicalCoherenceValidator;
}

// For CoherenceConstraints
if (
  Object.getOwnPropertyDescriptor(
    Prime.Framework.Base0,
    "CoherenceConstraints",
  ) &&
  Object.getOwnPropertyDescriptor(Prime.Framework.Base0, "CoherenceConstraints")
    .get
) {
  const descriptor = Object.getOwnPropertyDescriptor(
    Prime.Framework.Base0,
    "CoherenceConstraints",
  );
  const originalGetter = descriptor.get;

  Object.defineProperty(Prime.Framework.Base0, "CoherenceConstraints", {
    get: function () {
      const result = originalGetter.call(this);
      if (!result || Object.keys(result).length === 0) {
        return CoherenceConstraints;
      }
      return result;
    },
    configurable: true,
  });
} else {
  Prime.Framework.Base0.CoherenceConstraints = CoherenceConstraints;
}

// For CoherenceNorms
if (
  Object.getOwnPropertyDescriptor(Prime.Framework.Base0, "CoherenceNorms") &&
  Object.getOwnPropertyDescriptor(Prime.Framework.Base0, "CoherenceNorms").get
) {
  const descriptor = Object.getOwnPropertyDescriptor(
    Prime.Framework.Base0,
    "CoherenceNorms",
  );
  const originalGetter = descriptor.get;

  Object.defineProperty(Prime.Framework.Base0, "CoherenceNorms", {
    get: function () {
      const result = originalGetter.call(this);
      if (!result || Object.keys(result).length === 0) {
        return CoherenceNorms;
      }
      return result;
    },
    configurable: true,
  });
} else {
  Prime.Framework.Base0.CoherenceNorms = CoherenceNorms;
}

// Export all components with the Prime object for global usage
module.exports = {
  CoherenceValidator,
  MathematicalCoherenceValidator,
  CoherenceConstraints,
  CoherenceNorms,
  Prime,
};
