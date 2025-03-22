/**
 * PrimeOS JavaScript Library - Framework
 * Base 0: Neural Network Specification
 * Abstract mathematical foundation for the entire system
 */

// Import core
const Prime = require("../../core.js");
const MathUtils = require("../math");

/**
 * Base 0: Neural Network Specification
 * Abstract mathematical foundation for the entire system
 */
const Base0 = {
  /**
   * Create an embedding model
   * @param {Object} config - Configuration object
   * @returns {Object} Embedding model
   */
  createEmbeddingModel: function (config = {}) {
    return {
      type: "embedding",
      dimensions: config.dimensions || 128,
      metric: config.metric || "euclidean",
      name: config.name || "EmbeddingModel",

      /**
       * Embed data into the vector space
       * @param {*} data - Data to embed
       * @returns {Array} Embedding vector
       */
      embed: function (data) {
        if (
          config.embedFunction &&
          typeof config.embedFunction === "function"
        ) {
          return config.embedFunction(data);
        }

        // Default implementation using multi-dimensional projection
        return MathUtils.vector.embedData(data, this.dimensions);
      },

      /**
       * Calculate distance between embeddings
       * @param {Array} a - First embedding
       * @param {Array} b - Second embedding
       * @returns {number} Distance
       */
      distance: function (a, b) {
        // Validate inputs
        if (!Prime.Utils.isArray(a) || !Prime.Utils.isArray(b)) {
          throw new Prime.ValidationError("Embeddings must be arrays", {
            context: {
              aType: typeof a,
              bType: typeof b,
              aIsArray: Prime.Utils.isArray(a),
              bIsArray: Prime.Utils.isArray(b),
            },
          });
        }

        // Check for NaN or Infinity values in input vectors
        const hasInvalidValue = (arr) => {
          return arr.some((val) => !Number.isFinite(val));
        };

        if (hasInvalidValue(a) || hasInvalidValue(b)) {
          throw new Prime.ValidationError(
            "Embeddings contain NaN or Infinity values",
            {
              context: {
                hasNaN: a.some(Number.isNaN) || b.some(Number.isNaN),
                hasInfinity:
                  a.some((val) => val === Infinity || val === -Infinity) ||
                  b.some((val) => val === Infinity || val === -Infinity),
              },
            },
          );
        }

        // Use the appropriate distance calculation based on the metric
        let distanceResult;

        switch (this.metric) {
          case "euclidean":
            distanceResult = MathUtils.vector.distance(a, b);
            return distanceResult.distance;

          case "cosine":
            distanceResult = MathUtils.vector.cosineSimilarity(a, b);
            return distanceResult.distance;

          case "manhattan":
            distanceResult = MathUtils.vector.manhattanDistance(a, b);
            return distanceResult.distance;

          case "chebyshev":
            distanceResult = MathUtils.vector.chebyshevDistance(a, b);
            return distanceResult.distance;

          default:
            throw new Prime.InvalidOperationError(
              `Metric ${this.metric} not implemented`,
              {
                context: {
                  availableMetrics: [
                    "euclidean",
                    "cosine",
                    "manhattan",
                    "chebyshev",
                  ],
                  providedMetric: this.metric,
                },
              },
            );
        }
      },

      /**
       * Convert to UOR object
       * @param {Object} reference - UOR reference
       * @returns {Object} UOR object
       */
      toUOR: function (reference) {
        if (!Prime.UOR || !Prime.UOR.isReference(reference)) {
          throw new Prime.ValidationError("Invalid UOR reference");
        }

        return reference.createObject(this);
      },

      /**
       * Connect to other Base 0 components
       * @param {Object} components - Other Base 0 components
       * @returns {Object} Connected embedding model
       */
      connectToComponents: function (components) {
        this._components = components;
        return this;
      },
    };
  },

  /**
   * Create a logic model (fiber)
   * @param {Object} config - Configuration object
   * @returns {Object} Logic model
   */
  createLogicModel: function (config = {}) {
    return {
      type: "logic",
      rules: config.rules || [],
      constraints: config.constraints || [],
      name: config.name || "LogicModel",

      /**
       * Apply logic rules to data
       * @param {*} data - Data to process
       * @returns {*} Processed data
       */
      apply: function (data) {
        let result = data;

        // Apply each rule in sequence
        for (const rule of this.rules) {
          if (typeof rule === "function") {
            result = rule(result);
          } else if (rule && typeof rule.apply === "function") {
            result = rule.apply(result);
          }
        }

        return result;
      },

      /**
       * Validate data against constraints
       * @param {*} data - Data to validate
       * @returns {boolean} True if data is valid
       */
      validate: function (data) {
        // Check all constraints
        for (const constraint of this.constraints) {
          if (typeof constraint === "function") {
            if (!constraint(data)) {
              return false;
            }
          } else if (constraint && typeof constraint.check === "function") {
            if (!constraint.check(data)) {
              return false;
            }
          }
        }

        return true;
      },

      /**
       * Add a rule to the model
       * @param {Function|Object} rule - Rule to add
       * @returns {Object} Updated logic model
       */
      addRule: function (rule) {
        this.rules.push(rule);
        return this;
      },

      /**
       * Add a constraint to the model
       * @param {Function|Object} constraint - Constraint to add
       * @returns {Object} Updated logic model
       */
      addConstraint: function (constraint) {
        this.constraints.push(constraint);
        return this;
      },

      /**
       * Convert to UOR object
       * @param {Object} reference - UOR reference
       * @returns {Object} UOR object
       */
      toUOR: function (reference) {
        if (!Prime.UOR || !Prime.UOR.isReference(reference)) {
          throw new Prime.ValidationError("Invalid UOR reference");
        }

        return reference.createObject(this);
      },

      /**
       * Connect to other Base 0 components
       * @param {Object} components - Other Base 0 components
       * @returns {Object} Connected logic model
       */
      connectToComponents: function (components) {
        this._components = components;
        return this;
      },
    };
  },

  /**
   * Create a representation model (symmetry)
   * @param {Object} config - Configuration object
   * @returns {Object} Representation model
   */
  createRepresentationModel: function (config = {}) {
    return {
      type: "representation",
      transformations: config.transformations || [],
      formats: config.formats || {},
      name: config.name || "RepresentationModel",

      /**
       * Apply a transformation to data
       * @param {*} data - Data to transform
       * @param {string} transformation - Transformation name
       * @returns {*} Transformed data
       */
      transform: function (data, transformation) {
        const transform = this.transformations.find(
          (t) => t.name === transformation,
        );

        if (!transform) {
          throw new Prime.InvalidOperationError(
            `Transformation ${transformation} not found`,
            {
              context: {
                availableTransformations: this.transformations.map(
                  (t) => t.name,
                ),
              },
            },
          );
        }

        if (typeof transform.apply === "function") {
          return transform.apply(data);
        } else if (typeof transform === "function") {
          return transform(data);
        }

        throw new Prime.InvalidOperationError(
          `Invalid transformation ${transformation}`,
        );
      },

      /**
       * Convert data to the specified format
       * @param {*} data - Data to convert
       * @param {string} format - Target format
       * @returns {*} Converted data
       */
      represent: function (data, format) {
        if (!this.formats[format]) {
          throw new Prime.InvalidOperationError(`Format ${format} not found`, {
            context: { availableFormats: Object.keys(this.formats) },
          });
        }

        const formatter = this.formats[format];

        if (typeof formatter === "function") {
          return formatter(data);
        } else if (formatter && typeof formatter.format === "function") {
          return formatter.format(data);
        }

        throw new Prime.InvalidOperationError(`Invalid format ${format}`);
      },

      /**
       * Add a transformation to the model
       * @param {Object|Function} transformation - Transformation to add
       * @returns {Object} Updated representation model
       */
      addTransformation: function (transformation) {
        if (!transformation.name && typeof transformation !== "function") {
          throw new Prime.ValidationError(
            "Transformation must have a name property or be a function",
          );
        }

        this.transformations.push(transformation);
        return this;
      },

      /**
       * Add a format to the model
       * @param {string} name - Format name
       * @param {Function|Object} formatter - Format handler
       * @returns {Object} Updated representation model
       */
      addFormat: function (name, formatter) {
        this.formats[name] = formatter;
        return this;
      },

      /**
       * Convert to UOR object
       * @param {Object} reference - UOR reference
       * @returns {Object} UOR object
       */
      toUOR: function (reference) {
        if (!Prime.UOR || !Prime.UOR.isReference(reference)) {
          throw new Prime.ValidationError("Invalid UOR reference");
        }

        return reference.createObject(this);
      },

      /**
       * Connect to other Base 0 components
       * @param {Object} components - Other Base 0 components
       * @returns {Object} Connected representation model
       */
      connectToComponents: function (components) {
        this._components = components;
        return this;
      },
    };
  },

  /**
   * Create a processor (spectral operator)
   * @param {Object} config - Configuration object
   * @returns {Object} Processor
   */
  createProcessor: function (config = {}) {
    return {
      type: "processor",
      operations: config.operations || [],
      name: config.name || "Processor",

      /**
       * Process data with an operation
       * @param {*} data - Data to process
       * @param {string} operation - Operation name
       * @returns {*} Processed data
       */
      process: function (data, operation) {
        const op = this.operations.find((o) => o.name === operation);

        if (!op) {
          throw new Prime.InvalidOperationError(
            `Operation ${operation} not found`,
            {
              context: {
                availableOperations: this.operations.map((o) => o.name),
              },
            },
          );
        }

        if (typeof op.apply === "function") {
          return op.apply(data);
        } else if (typeof op === "function") {
          return op(data);
        }

        throw new Prime.InvalidOperationError(`Invalid operation ${operation}`);
      },

      /**
       * Compose two operations
       * @param {string} op1 - First operation
       * @param {string} op2 - Second operation
       * @returns {Function} Composed operation
       */
      compose: function (op1, op2) {
        return (data) => this.process(this.process(data, op1), op2);
      },

      /**
       * Add an operation to the processor
       * @param {Object|Function} operation - Operation to add
       * @returns {Object} Updated processor
       */
      addOperation: function (operation) {
        if (!operation.name && typeof operation !== "function") {
          throw new Prime.ValidationError(
            "Operation must have a name property or be a function",
          );
        }

        this.operations.push(operation);
        return this;
      },

      /**
       * Convert to UOR object
       * @param {Object} reference - UOR reference
       * @returns {Object} UOR object
       */
      toUOR: function (reference) {
        if (!Prime.UOR || !Prime.UOR.isReference(reference)) {
          throw new Prime.ValidationError("Invalid UOR reference");
        }

        return reference.createObject(this);
      },

      /**
       * Connect to other Base 0 components
       * @param {Object} components - Other Base 0 components
       * @returns {Object} Connected processor
       */
      connectToComponents: function (components) {
        this._components = components;
        return this;
      },
    };
  },

  /**
   * Create all Base 0 components
   * @param {Object} config - Configuration object
   * @returns {Object} Base 0 components
   */
  createBase0Components: function (config = {}) {
    // Create components
    const embedding = this.createEmbeddingModel(config.embedding || {});
    const logic = this.createLogicModel(config.logic || {});
    const representation = this.createRepresentationModel(
      config.representation || {},
    );
    const processor = this.createProcessor(config.processor || {});

    // Connect components to each other
    const components = { embedding, logic, representation, processor };

    embedding.connectToComponents(components);
    logic.connectToComponents(components);
    representation.connectToComponents(components);
    processor.connectToComponents(components);

    return components;
  },

  /**
   * Connect to coherence system
   * @param {Object} components - Base 0 components
   * @returns {Object} Connected components
   */
  connectToCoherence: function (components) {
    if (!Prime.coherence) {
      Prime.Logger.warn("Coherence system not available");
      return components;
    }

    // Register components with system-wide coherence tracking
    for (const key in components) {
      Prime.coherence.systemCoherence.register(components[key]);
    }

    return components;
  },
};

module.exports = Base0;
