/**
 * PrimeOS Veneer - Coherence Boundaries
 * Defines and validates coherence boundaries for PrimeApps
 */

const Prime = require("../core");
const { PrimeError } = require("../core/error");

/**
 * Coherence Boundary Error class
 */
class CoherenceBoundaryError extends PrimeError {
  constructor(message, details = {}, code = "BOUNDARY_ERROR") {
    super(message, details, code);
    this.name = "CoherenceBoundaryError";
  }
}

/**
 * Boundary Type enum
 */
const BoundaryType = {
  HARD: "hard", // Strict boundary that cannot be violated
  SOFT: "soft", // Flexible boundary with degraded performance
  WARNING: "warning", // Advisory boundary for notifications only
};

/**
 * Domain Type enum
 */
const DomainType = {
  RESOURCE: "resource", // Resource usage boundaries
  NUMERICAL: "numerical", // Numerical stability boundaries
  LOGICAL: "logical", // Logical consistency boundaries
  CROSS_APP: "cross_app", // Cross-application interaction boundaries
  INTERFACE: "interface", // Interface compatibility boundaries
  LIFECYCLE: "lifecycle", // Application lifecycle boundaries
  PERMISSION: "permission", // Permission and security boundaries
};

/**
 * Coherence Boundary class
 * Defines and validates a coherence boundary for an application
 */
class CoherenceBoundary {
  /**
   * Create a new coherence boundary
   * @param {string} domain - Domain of the boundary
   * @param {string} type - Type of boundary
   * @param {Function} validator - Validation function
   * @param {Object} metadata - Additional boundary metadata
   */
  constructor(domain, type, validator, metadata = {}) {
    this.domain = domain;
    this.type = type;
    this.validator = validator;
    this.metadata = {
      name: metadata.name || `${domain}_boundary`,
      description: metadata.description || `${domain} coherence boundary`,
      priority: metadata.priority || 1,
      threshold: metadata.threshold !== undefined ? metadata.threshold : 0.8,
      ...metadata,
    };

    this.id = `boundary_${domain}_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
  }

  /**
   * Validate a value against this boundary
   * @param {*} value - Value to validate
   * @param {Object} context - Additional context
   * @returns {Object} Validation result
   */
  validate(value, context = {}) {
    const startTime = performance.now();
    let valid = false;
    let coherence = 0;
    let details = {};

    try {
      // Call the validator function
      const result = this.validator(value, context);

      // Handle different result formats
      if (result === true || result === false) {
        valid = result;
        coherence = result ? 1.0 : 0.0;
      } else if (typeof result === "number") {
        coherence = Math.max(0, Math.min(1, result));
        valid = coherence >= this.metadata.threshold;
      } else if (typeof result === "object") {
        valid = result.valid !== false;
        coherence =
          typeof result.coherence === "number"
            ? Math.max(0, Math.min(1, result.coherence))
            : valid
              ? 1.0
              : 0.0;
        details = result.details || {};
      }
    } catch (error) {
      valid = false;
      coherence = 0;
      details = { error: error.message };
    }

    const endTime = performance.now();

    return {
      valid,
      coherence,
      domain: this.domain,
      type: this.type,
      threshold: this.metadata.threshold,
      satisfied: valid,
      details,
      duration: endTime - startTime,
    };
  }

  /**
   * Convert the boundary to a JSON representation
   * @returns {Object} JSON representation
   */
  toJSON() {
    return {
      id: this.id,
      domain: this.domain,
      type: this.type,
      metadata: this.metadata,
    };
  }
}

/**
 * Default boundary validators by domain
 */
const DefaultBoundaryValidators = {
  // Resource boundaries
  [DomainType.RESOURCE]: {
    memory: (value, context = {}) => {
      const { limit = Infinity, current = 0 } = context;
      // Return coherence as (limit - current) / limit
      if (limit === Infinity || limit <= 0) return 1.0;
      return Math.max(0, Math.min(1, (limit - current) / limit));
    },

    storage: (value, context = {}) => {
      const { quota = Infinity, used = 0 } = context;
      // Return coherence as (quota - used) / quota
      if (quota === Infinity || quota <= 0) return 1.0;
      return Math.max(0, Math.min(1, (quota - used) / quota));
    },

    compute: (value, context = {}) => {
      const { maxConcurrency = Infinity, currentTasks = 0 } = context;
      // Return coherence as (maxConcurrency - currentTasks) / maxConcurrency
      if (maxConcurrency === Infinity || maxConcurrency <= 0) return 1.0;
      return Math.max(
        0,
        Math.min(1, (maxConcurrency - currentTasks) / maxConcurrency),
      );
    },
  },

  // Numerical boundaries
  [DomainType.NUMERICAL]: {
    finiteness: (value) => {
      // Check if all values are finite numbers
      const check = (v) => {
        if (typeof v === "number") return Number.isFinite(v);
        if (Array.isArray(v)) return v.every(check);
        if (v && typeof v === "object") return Object.values(v).every(check);
        return true;
      };

      return check(value);
    },

    precision: (value, context = {}) => {
      const { tolerance = 1e-10 } = context;

      // Check numerical precision
      const check = (v) => {
        if (typeof v !== "number") return true;
        return Math.abs(v - Math.round(v / tolerance) * tolerance) < tolerance;
      };

      if (typeof value === "number") return check(value);
      if (Array.isArray(value)) return value.every(check);
      return true;
    },
  },

  // Logical boundaries
  [DomainType.LOGICAL]: {
    consistency: (value, context = {}) => {
      // Simple state consistency check
      if (!value || typeof value !== "object") return false;

      const { constraints = [] } = context;

      // If no constraints specified, assume consistent
      if (constraints.length === 0) return true;

      // Check each constraint
      for (const constraint of constraints) {
        if (typeof constraint === "function") {
          if (!constraint(value)) return false;
        } else if (typeof constraint === "object" && constraint.check) {
          if (!constraint.check(value)) return false;
        }
      }

      return true;
    },
  },

  // Lifecycle boundaries
  [DomainType.LIFECYCLE]: {
    stateValidity: (value, context = {}) => {
      // Check if app state is valid
      const { validStates = [] } = context;
      return validStates.length === 0 || validStates.includes(value);
    },

    transitionValidity: (value, context = {}) => {
      // Check if state transition is valid
      const { from, to, validTransitions = [] } = context;

      if (!validTransitions.length) return true;

      for (const transition of validTransitions) {
        if (
          (transition.from === from || transition.from === "*") &&
          (transition.to === to || transition.to === "*")
        ) {
          return true;
        }
      }

      return false;
    },
  },
};

/**
 * Coherence boundary registry
 * Manages coherence boundaries for the system
 */
class CoherenceBoundaryRegistry {
  /**
   * Create a new coherence boundary registry
   * @param {Object} options - Registry options
   */
  constructor(options = {}) {
    this.options = {
      enableStrictValidation: options.enableStrictValidation || false,
      defaultThreshold: options.defaultThreshold || 0.8,
      registerDefaults: options.registerDefaults !== false, // Default to true unless explicitly set to false
      ...options,
    };

    // Domain registries
    this.boundaries = new Map();

    // Register default boundaries if not disabled
    if (this.options.registerDefaults) {
      this._registerDefaultBoundaries();
    }
  }

  /**
   * Clear all registered boundaries
   * Useful for testing
   */
  clearAllBoundaries() {
    this.boundaries = new Map();
    return this;
  }

  /**
   * Register a coherence boundary
   * @param {string} domain - Domain of the boundary
   * @param {string} name - Name of the boundary
   * @param {Function} validator - Validation function
   * @param {Object} metadata - Additional boundary metadata
   * @returns {CoherenceBoundary} Registered boundary
   */
  registerBoundary(domain, name, validator, metadata = {}) {
    if (typeof validator !== "function") {
      throw new CoherenceBoundaryError("Validator must be a function", {
        domain,
        name,
      });
    }

    // Ensure domain exists in registry
    if (!this.boundaries.has(domain)) {
      this.boundaries.set(domain, new Map());
    }

    // Create boundary instance
    const boundaryType = metadata.type || BoundaryType.SOFT;
    const boundary = new CoherenceBoundary(domain, boundaryType, validator, {
      name,
      threshold: this.options.defaultThreshold,
      ...metadata,
    });

    // Add to registry
    this.boundaries.get(domain).set(boundary.id, boundary);

    return boundary;
  }

  /**
   * Unregister a coherence boundary
   * @param {string} boundaryId - ID of the boundary to remove
   * @returns {boolean} Whether the boundary was removed
   */
  unregisterBoundary(boundaryId) {
    for (const [domain, boundaryMap] of this.boundaries.entries()) {
      if (boundaryMap.has(boundaryId)) {
        boundaryMap.delete(boundaryId);
        return true;
      }
    }

    return false;
  }

  /**
   * Get a coherence boundary by ID
   * @param {string} boundaryId - Boundary ID
   * @returns {CoherenceBoundary|null} Found boundary or null
   */
  getBoundary(boundaryId) {
    for (const [domain, boundaryMap] of this.boundaries.entries()) {
      if (boundaryMap.has(boundaryId)) {
        return boundaryMap.get(boundaryId);
      }
    }

    return null;
  }

  /**
   * Get all boundaries for a domain
   * @param {string} domain - Domain to get boundaries for
   * @returns {Array<CoherenceBoundary>} Domain boundaries
   */
  getDomainBoundaries(domain) {
    if (!this.boundaries.has(domain)) {
      return [];
    }

    return Array.from(this.boundaries.get(domain).values());
  }

  /**
   * Get all registered boundaries
   * @returns {Array<CoherenceBoundary>} All boundaries
   */
  getAllBoundaries() {
    const allBoundaries = [];

    for (const [domain, boundaryMap] of this.boundaries.entries()) {
      allBoundaries.push(...boundaryMap.values());
    }

    return allBoundaries;
  }

  /**
   * Validate a value against all boundaries in a domain
   * @param {string} domain - Domain to validate against
   * @param {*} value - Value to validate
   * @param {Object} context - Additional context
   * @returns {Object} Validation results
   */
  validateDomain(domain, value, context = {}) {
    const results = {
      domain,
      valid: true,
      coherence: 1.0,
      boundaryResults: [],
      hardViolations: [],
      softViolations: [],
    };

    if (!this.boundaries.has(domain)) {
      return results;
    }

    const domainBoundaries = Array.from(this.boundaries.get(domain).values());

    // Validate against each boundary
    for (const boundary of domainBoundaries) {
      const boundaryResult = boundary.validate(value, context);
      results.boundaryResults.push({
        boundary: boundary.id,
        name: boundary.metadata.name,
        ...boundaryResult,
      });

      // Track violations
      if (!boundaryResult.valid) {
        if (boundary.type === BoundaryType.HARD) {
          results.hardViolations.push({
            boundary: boundary.id,
            name: boundary.metadata.name,
            domain: boundary.domain,
            coherence: boundaryResult.coherence,
            details: boundaryResult.details,
          });
        } else {
          results.softViolations.push({
            boundary: boundary.id,
            name: boundary.metadata.name,
            domain: boundary.domain,
            coherence: boundaryResult.coherence,
            details: boundaryResult.details,
          });
        }
      }
    }

    // Hard violations make the overall result invalid
    if (results.hardViolations.length > 0) {
      results.valid = false;
    }

    // Calculate overall coherence
    if (results.boundaryResults.length > 0) {
      // Weighted average by boundary priority
      let totalWeight = 0;
      let weightedCoherence = 0;

      for (const result of results.boundaryResults) {
        const boundary = this.getBoundary(result.boundary);
        const weight = boundary ? boundary.metadata.priority : 1;

        totalWeight += weight;
        weightedCoherence += result.coherence * weight;
      }

      results.coherence =
        totalWeight > 0 ? weightedCoherence / totalWeight : 1.0;
    }

    return results;
  }

  /**
   * Validate a value against boundaries from multiple domains
   * @param {Array<string>} domains - Domains to validate against
   * @param {*} value - Value to validate
   * @param {Object} context - Additional context
   * @returns {Object} Validation results
   */
  validateMultipleDomains(domains, value, context = {}) {
    const results = {
      domains,
      valid: true,
      coherence: 1.0,
      domainResults: {},
      hardViolations: [],
      softViolations: [],
    };

    // Validate against each domain
    for (const domain of domains) {
      const domainResult = this.validateDomain(domain, value, context);
      results.domainResults[domain] = domainResult;

      // Track violations
      if (domainResult.hardViolations.length > 0) {
        results.hardViolations.push(...domainResult.hardViolations);
        results.valid = false;
      }

      if (domainResult.softViolations.length > 0) {
        results.softViolations.push(...domainResult.softViolations);
      }
    }

    // Calculate overall coherence (average of domain coherence)
    const domainCoherenceValues = Object.values(results.domainResults).map(
      (r) => r.coherence,
    );

    if (domainCoherenceValues.length > 0) {
      const sum = domainCoherenceValues.reduce((acc, val) => acc + val, 0);
      results.coherence = sum / domainCoherenceValues.length;
    }

    return results;
  }

  /**
   * Register default coherence boundaries
   * @private
   */
  _registerDefaultBoundaries() {
    // Register resource boundaries
    for (const [name, validator] of Object.entries(
      DefaultBoundaryValidators[DomainType.RESOURCE],
    )) {
      this.registerBoundary(DomainType.RESOURCE, name, validator, {
        description: `Resource ${name} coherence boundary`,
        type: name === "memory" ? BoundaryType.HARD : BoundaryType.SOFT,
        priority: name === "memory" ? 10 : 5,
      });
    }

    // Register numerical boundaries
    for (const [name, validator] of Object.entries(
      DefaultBoundaryValidators[DomainType.NUMERICAL],
    )) {
      this.registerBoundary(DomainType.NUMERICAL, name, validator, {
        description: `Numerical ${name} coherence boundary`,
        type: name === "finiteness" ? BoundaryType.HARD : BoundaryType.SOFT,
        priority: name === "finiteness" ? 10 : 5,
      });
    }

    // Register logical boundaries
    for (const [name, validator] of Object.entries(
      DefaultBoundaryValidators[DomainType.LOGICAL],
    )) {
      this.registerBoundary(DomainType.LOGICAL, name, validator, {
        description: `Logical ${name} coherence boundary`,
        type: BoundaryType.SOFT,
        priority: 8,
      });
    }

    // Register lifecycle boundaries
    for (const [name, validator] of Object.entries(
      DefaultBoundaryValidators[DomainType.LIFECYCLE],
    )) {
      this.registerBoundary(DomainType.LIFECYCLE, name, validator, {
        description: `Lifecycle ${name} coherence boundary`,
        type: name === "stateValidity" ? BoundaryType.HARD : BoundaryType.SOFT,
        priority: name === "stateValidity" ? 10 : 5,
      });
    }
  }
}

// Add to Prime namespace
Prime.Veneer = Prime.Veneer || {};
Prime.Veneer.CoherenceBoundary = CoherenceBoundary;
Prime.Veneer.CoherenceBoundaryRegistry = CoherenceBoundaryRegistry;
Prime.Veneer.BoundaryType = BoundaryType;
Prime.Veneer.DomainType = DomainType;
Prime.Veneer.CoherenceBoundaryError = CoherenceBoundaryError;

module.exports = {
  CoherenceBoundary,
  CoherenceBoundaryRegistry,
  BoundaryType,
  DomainType,
  CoherenceBoundaryError,
  DefaultBoundaryValidators,
};
