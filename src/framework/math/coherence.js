/**
 * Coherence-gradient descent algorithm implementation for the Prime Framework
 * Based on multi-perspective optimization using fiber algebra
 */

// Import Prime core directly to avoid circular dependencies
const Prime = require("../../core/prime.js");

// Import standardized math interface
const StandardMath = require("./index.js").Standard;

// Import type validation
const TypeValidation = require("./type-validation.js");

/**
 * Clifford Algebra implementation for multi-dimensional space modeling
 */
class CliffordAlgebraFiber {
  /**
   * Create a new Clifford Algebra fiber
   *
   * @param {Object} options - Configuration options
   * @param {number} options.dimension - Dimension of the space (default: 3)
   * @param {Array} options.signature - Signature of the space (default: all positive)
   * @param {Array} options.position - Position in the reference manifold (default: origin)
   */
  constructor(options = {}) {
    // Validate options if provided
    if (options !== undefined) {
      TypeValidation.assertObject(options, "options", {
        operation: "CliffordAlgebraFiber.constructor",
      });

      // Validate dimension if provided
      if (options.dimension !== undefined) {
        TypeValidation.assertPositiveInteger(
          options.dimension,
          "options.dimension",
          {
            operation: "CliffordAlgebraFiber.constructor",
          },
        );
      }

      // Validate signature if provided
      if (options.signature !== undefined) {
        TypeValidation.assertArray(options.signature, "options.signature", {
          operation: "CliffordAlgebraFiber.constructor",
        });
        TypeValidation.assertNumberArray(
          options.signature,
          "options.signature",
          {
            operation: "CliffordAlgebraFiber.constructor",
          },
        );
      }

      // Validate position if provided
      if (options.position !== undefined) {
        TypeValidation.assertArray(options.position, "options.position", {
          operation: "CliffordAlgebraFiber.constructor",
        });
        TypeValidation.assertNumberArray(options.position, "options.position", {
          operation: "CliffordAlgebraFiber.constructor",
        });
      }
    }

    this.dimension = options.dimension || 3;
    this.signature = options.signature || Array(this.dimension).fill(1);
    this.position = options.position || Array(3).fill(0); // Manifold position

    // Validate that dimension is reasonable to avoid computational explosions
    if (this.dimension > 16) {
      Prime.Logger.warn(
        `Clifford algebra dimension ${this.dimension} may lead to computational overflow`,
        {
          operation: "CliffordAlgebraFiber.constructor",
          recommendedMaximum: 16,
        },
      );
    }

    this.basis = this._generateBasis();
    this.innerProductMetric = this._initializeMetric();
    this.state = null;
    this.patterns = [];
  }

  /**
   * Generate basis elements for this algebra
   *
   * @private
   * @returns {Array} Array of basis element names
   */
  _generateBasis() {
    const basis = ["1"]; // Scalar basis

    // Generate all basis elements (2^dimension of them)
    for (let i = 1; i < 1 << this.dimension; i++) {
      let name = "";
      for (let j = 0; j < this.dimension; j++) {
        if (i & (1 << j)) {
          name += `e${j + 1}`;
        }
      }
      basis.push(name);
    }

    return basis;
  }

  /**
   * Initialize the inner product metric for this fiber
   * The metric varies based on position to create different perspectives
   *
   * @private
   * @returns {Array} Inner product matrix
   */
  _initializeMetric() {
    const n = this.basis.length;

    // Create identity matrix as starting point
    const metric = StandardMath.Matrix.identity(n);

    // Vary the metric based on position in the manifold
    for (let i = 1; i < n; i++) {
      for (let j = 0; j < i; j++) {
        // Position-dependent correlation
        // Sum position coordinates
        const positionSum = StandardMath.Vector.sum(this.position);

        // Calculate correlation using cosine function
        const correlation =
          0.1 * Math.cos((Math.PI * positionSum * (i + j)) / n);

        // Set symmetric off-diagonal elements
        metric[i][j] = correlation;
        metric[j][i] = correlation;
      }
    }

    return metric;
  }

  /**
   * Get the grade of a basis element
   *
   * @param {string} element - Basis element name
   * @returns {number} Grade of the element
   */
  getGrade(element) {
    if (element === "1") return 0;

    // Count the number of vector basis elements in the product
    const matches = element.match(/e\d+/g);
    return matches ? matches.length : 0;
  }

  /**
   * Calculate the inner product of two elements
   *
   * @param {string} a - First basis element
   * @param {string} b - Second basis element
   * @returns {number} Inner product value
   */
  innerProduct(a, b) {
    const idxA = this.basis.indexOf(a);
    const idxB = this.basis.indexOf(b);

    if (idxA === -1 || idxB === -1) {
      throw new Prime.ValidationError(`Basis elements not found: ${a}, ${b}`, {
        elemA: a,
        elemB: b,
        availableBasis: this.basis.length,
      });
    }

    return this.innerProductMetric[idxA][idxB];
  }

  /**
   * Set the state vector for this fiber
   *
   * @param {Array} state - State vector in the Clifford algebra
   */
  setState(state) {
    // Validate state is an array
    TypeValidation.assertArray(state, "state", {
      operation: "CliffordAlgebraFiber.setState",
    });

    // Validate state has correct length
    if (state.length !== this.basis.length) {
      throw new Prime.DimensionMismatchError(
        `State vector must have length ${this.basis.length}`,
        {
          operation: "CliffordAlgebraFiber.setState",
          expectedDimension: this.basis.length,
          actualDimension: state.length,
          basisSize: this.basis.length,
        },
      );
    }

    // Validate state contains only numbers
    TypeValidation.assertNumberArray(state, "state", {
      operation: "CliffordAlgebraFiber.setState",
    });

    // Check for extreme values that might cause numerical instability
    try {
      TypeValidation.validateArrayMagnitudes(
        state,
        "state",
        { minMagnitude: 1e-100, maxMagnitude: 1e100, allowZero: true },
        { operation: "CliffordAlgebraFiber.setState" },
      );
    } catch (error) {
      // Convert to warning for extreme values instead of error
      if (error instanceof Prime.NumericOverflowError) {
        Prime.Logger.warn(
          `State vector contains extreme values that may cause numerical instability`,
          {
            operation: "CliffordAlgebraFiber.setState",
            ...error.context,
          },
        );
      } else {
        throw error;
      }
    }

    this.state = state.slice();
  }

  /**
   * Get the current state vector
   *
   * @returns {Array} Current state vector
   */
  getState() {
    return this.state ? this.state.slice() : null;
  }

  /**
   * Calculate the norm of a state vector using the inner product metric
   * with enhanced numerical stability for extreme values
   *
   * @param {Array} state - State vector
   * @param {Object} [options={}] - Additional options
   * @param {boolean} [options.useScaling=true] - Whether to use scaling for extreme values
   * @param {boolean} [options.useKahan=true] - Whether to use Kahan summation
   * @returns {number} Norm value
   */
  calculateNorm(state, options = {}) {
    if (!state) return 0;

    // Use the inner product method with the state vector itself
    // This provides all the numerical stability enhancements
    const innerProductValue = this.innerProduct(state, options);

    // Use StandardMath for safe square root operation with numerical stability
    return StandardMath.sqrt(Math.max(0, innerProductValue));
  }

  /**
   * Compute the norm of the current state
   *
   * @returns {number} Norm value
   */
  computeNorm() {
    return this.calculateNorm(this.state);
  }

  /**
   * Calculate the inner product between the current state and another state
   * with enhanced numerical stability for extreme values
   *
   * @param {Array} otherState - Another state vector
   * @param {Object} [options={}] - Additional options
   * @param {boolean} [options.useScaling=true] - Whether to use scaling for extreme values
   * @param {boolean} [options.useKahan=true] - Whether to use Kahan summation
   * @returns {number} Inner product value
   */
  innerProduct(otherState, options = {}) {
    // Validate that current state exists
    if (!this.state) {
      throw new Prime.ValidationError("No state set for this fiber", {
        operation: "CliffordAlgebraFiber.innerProduct",
      });
    }

    // Validate otherState is provided and is an array
    TypeValidation.assertDefined(otherState, "otherState", {
      operation: "CliffordAlgebraFiber.innerProduct",
    });

    TypeValidation.assertArray(otherState, "otherState", {
      operation: "CliffordAlgebraFiber.innerProduct",
    });

    // Validate otherState contains only numbers
    TypeValidation.assertNumberArray(otherState, "otherState", {
      operation: "CliffordAlgebraFiber.innerProduct",
    });

    // Validate options object if provided
    if (options !== undefined) {
      TypeValidation.assertObject(options, "options", {
        operation: "CliffordAlgebraFiber.innerProduct",
      });

      // Validate specific option types if provided
      if (options.useScaling !== undefined) {
        TypeValidation.assertBoolean(options.useScaling, "options.useScaling", {
          operation: "CliffordAlgebraFiber.innerProduct",
        });
      }

      if (options.useKahan !== undefined) {
        TypeValidation.assertBoolean(options.useKahan, "options.useKahan", {
          operation: "CliffordAlgebraFiber.innerProduct",
        });
      }
    }

    const useScaling = options.useScaling !== false;
    const useKahan = options.useKahan !== false;
    const minLength = Math.min(this.state.length, otherState.length);

    // For empty states or metric, return 0
    if (
      minLength === 0 ||
      !this.innerProductMetric ||
      this.innerProductMetric.length === 0
    ) {
      return 0;
    }

    // Check for extreme values in other state that might cause numerical instability
    try {
      TypeValidation.validateArrayMagnitudes(
        otherState,
        "otherState",
        { minMagnitude: 1e-100, maxMagnitude: 1e100, allowZero: true },
        { operation: "CliffordAlgebraFiber.innerProduct" },
      );
    } catch (error) {
      // Convert to warning for extreme values instead of error
      if (error instanceof Prime.NumericOverflowError) {
        Prime.Logger.warn(
          `State vector contains extreme values that may cause numerical instability`,
          {
            operation: "CliffordAlgebraFiber.innerProduct",
            ...error.context,
          },
        );
      }
    }

    // Handle extreme values with scaling if needed
    if (useScaling) {
      // Find max absolute values for scaling
      let maxState = 0;
      let maxOther = 0;
      let maxMetric = 0;

      // Get maximum values for scaling
      for (let i = 0; i < minLength; i++) {
        maxState = Math.max(maxState, Math.abs(this.state[i]));
        maxOther = Math.max(maxOther, Math.abs(otherState[i]));

        for (let j = 0; j < minLength; j++) {
          if (
            i < this.innerProductMetric.length &&
            j < this.innerProductMetric[i].length
          ) {
            maxMetric = Math.max(
              maxMetric,
              Math.abs(this.innerProductMetric[i][j]),
            );
          }
        }
      }

      // Check if any values are extreme
      const hasExtremeValues =
        maxState > 1e100 ||
        maxState < 1e-100 ||
        maxOther > 1e100 ||
        maxOther < 1e-100 ||
        maxMetric > 1e100 ||
        maxMetric < 1e-100;

      // Use scaling for extreme values
      if (hasExtremeValues) {
        // Avoid division by zero
        const scaleState = maxState === 0 ? 1 : maxState;
        const scaleOther = maxOther === 0 ? 1 : maxOther;
        const scaleMetric = maxMetric === 0 ? 1 : maxMetric;

        // Use StandardMath's Kahan summation with scaling
        if (useKahan) {
          // Prepare for StandardMath's approach to compensated arithmetic
          // We'll leverage StandardMath.Statistics.weightedSum for numerical stability
          const terms = [];
          const weights = [];

          // Setup for controlled summation with numerical stability

          for (let i = 0; i < minLength; i++) {
            for (let j = 0; j < minLength; j++) {
              if (
                i < this.innerProductMetric.length &&
                j < this.innerProductMetric[i].length
              ) {
                // Scale each component
                const scaledState = this.state[i] / scaleState;
                const scaledMetric =
                  this.innerProductMetric[i][j] / scaleMetric;
                const scaledOther = otherState[j] / scaleOther;

                // Compute scaled term
                const term = scaledState * scaledMetric * scaledOther;

                // Add term to collection for standardized summation
                terms.push(term);
                weights.push(1.0); // Equal weights for all terms
              }
            }
          }

          // Use StandardMath for numerically stable weighted sum
          const sumResult = StandardMath.Statistics.weightedSum(terms, {
            weights: weights,
            useCompensatedSum: true,
          });

          // Scale back the result
          return sumResult.sum * scaleState * scaleMetric * scaleOther;
        } else {
          // Standard summation with scaling
          let result = 0;

          for (let i = 0; i < minLength; i++) {
            for (let j = 0; j < minLength; j++) {
              if (
                i < this.innerProductMetric.length &&
                j < this.innerProductMetric[i].length
              ) {
                // Scale each component
                const scaledState = this.state[i] / scaleState;
                const scaledMetric =
                  this.innerProductMetric[i][j] / scaleMetric;
                const scaledOther = otherState[j] / scaleOther;

                // Add to result
                result += scaledState * scaledMetric * scaledOther;
              }
            }
          }

          // Scale the result back
          return result * scaleState * scaleMetric * scaleOther;
        }
      }
    }

    // If not using scaling, use Kahan summation if requested
    if (useKahan) {
      // Separate positive and negative contributions
      let posSum = 0;
      let negSum = 0;
      let posCompensation = 0;
      let negCompensation = 0;

      for (let i = 0; i < minLength; i++) {
        for (let j = 0; j < minLength; j++) {
          if (
            i < this.innerProductMetric.length &&
            j < this.innerProductMetric[i].length
          ) {
            const term =
              this.state[i] * this.innerProductMetric[i][j] * otherState[j];

            // Separate positive and negative terms to reduce cancellation errors
            if (term >= 0) {
              // Kahan summation for positive terms
              const y = term - posCompensation;
              const t = posSum + y;
              posCompensation = t - posSum - y;
              posSum = t;
            } else {
              // Kahan summation for negative terms
              const y = term - negCompensation;
              const t = negSum + y;
              negCompensation = t - negSum - y;
              negSum = t;
            }
          }
        }
      }

      // Combine positive and negative sums
      return posSum + negSum;
    }

    // Standard calculation without Kahan or scaling
    let result = 0;

    for (let i = 0; i < minLength; i++) {
      for (let j = 0; j < minLength; j++) {
        if (
          i < this.innerProductMetric.length &&
          j < this.innerProductMetric[i].length
        ) {
          result +=
            this.state[i] * this.innerProductMetric[i][j] * otherState[j];
        }
      }
    }

    return result;
  }

  /**
   * Update the current state with new values
   *
   * @param {Array} newState - New state values
   */
  updateState(newState) {
    if (!Array.isArray(newState)) {
      throw new Prime.ValidationError("New state must be an array", {
        actualType: typeof newState,
      });
    }

    // Copy values, limiting to valid dimensions
    this.state = this.state || new Array(this.basis.length).fill(0);

    const minLength = Math.min(this.state.length, newState.length);
    for (let i = 0; i < minLength; i++) {
      this.state[i] = newState[i];
    }
  }

  /**
   * Store a detected pattern
   *
   * @param {Object} pattern - Pattern object
   * @param {string} pattern.type - Type of pattern
   * @param {Array} pattern.components - Components involved in the pattern
   */
  addPattern(pattern) {
    if (!pattern || typeof pattern !== "object") {
      throw new Prime.ValidationError("Pattern must be an object", {
        actualType: typeof pattern,
      });
    }

    this.patterns.push(pattern);
  }

  /**
   * Get all stored patterns
   *
   * @returns {Array} Array of pattern objects
   */
  getPatterns() {
    return this.patterns.slice();
  }
}

/**
 * Enhanced Coherence-Gradient Descent implementation based on the Prime Framework
 * Combines multi-view optimization with fiber algebra
 */
class CoherenceGradientDescent {
  /**
   * Create a new instance of coherence-gradient descent optimizer
   *
   * @param {Object} options - Configuration options
   * @param {number} options.dimension - Dimension of the problem space (default: 10)
   * @param {number} options.numFibers - Number of fiber points to use (default: 5)
   * @param {boolean} options.useSpectral - Whether to use spectral analysis (default: true)
   * @param {boolean} options.useFiber - Whether to use fiber algebra (default: true)
   */
  constructor(options = {}) {
    // Validate options if provided
    if (options !== undefined) {
      TypeValidation.assertObject(options, "options", {
        operation: "CoherenceGradientDescent.constructor",
      });

      // Validate dimension if provided
      if (options.dimension !== undefined) {
        TypeValidation.assertPositiveInteger(
          options.dimension,
          "options.dimension",
          {
            operation: "CoherenceGradientDescent.constructor",
          },
        );

        // Check for computationally feasible dimensions
        if (options.dimension > 30) {
          Prime.Logger.warn(
            `Dimension ${options.dimension} may lead to computational overflow in CoherenceGradientDescent`,
            {
              operation: "CoherenceGradientDescent.constructor",
              recommendedMaximum: 30,
            },
          );
        }
      }

      // Validate numFibers if provided
      if (options.numFibers !== undefined) {
        TypeValidation.assertPositiveInteger(
          options.numFibers,
          "options.numFibers",
          {
            operation: "CoherenceGradientDescent.constructor",
          },
        );

        // Check for reasonable number of fibers
        if (options.numFibers > 20) {
          Prime.Logger.warn(
            `Number of fibers ${options.numFibers} is unusually high and may impact performance`,
            {
              operation: "CoherenceGradientDescent.constructor",
              recommendedMaximum: 20,
            },
          );
        }
      }

      // Validate useSpectral if provided
      if (options.useSpectral !== undefined) {
        TypeValidation.assertBoolean(
          options.useSpectral,
          "options.useSpectral",
          {
            operation: "CoherenceGradientDescent.constructor",
          },
        );
      }

      // Validate useFiber if provided
      if (options.useFiber !== undefined) {
        TypeValidation.assertBoolean(options.useFiber, "options.useFiber", {
          operation: "CoherenceGradientDescent.constructor",
        });
      }
    }

    this.dimension = options.dimension || 10;
    this.numFibers = options.numFibers || 5;
    this.useSpectral = options.useSpectral !== false;
    this.useFiber = options.useFiber !== false;

    // Initialize the Clifford algebra structure
    this.maxGrade = Math.min(3, this.dimension); // Limit max grade for efficiency

    // Initialize the fiber manifold if enabled
    this.fibers = this.useFiber ? this._initializeFibers() : null;

    // Initialize generators for symmetry transformations
    this.symmetryGenerators = this._initializeSymmetryGenerators();

    // Caches for computation
    this._spectralCache = {};
    this._coherenceCache = {};
    this._patternCache = {};
  }

  /**
   * Initialize fiber algebras at different manifold points
   *
   * @private
   * @returns {Array} Array of fiber objects
   */
  _initializeFibers() {
    const fibers = [];

    // Create fiber points in a low-discrepancy sequence for better coverage
    const phi = (1 + Math.sqrt(5)) / 2; // Golden ratio for quasi-random sequence

    for (let i = 0; i < this.numFibers; i++) {
      // Create a position in the manifold using quasi-random sequence
      const pos = [
        (i * phi) % 1,
        (i * phi * phi) % 1,
        (i * phi * phi * phi) % 1,
      ];

      // Create a fiber at this point
      const fiber = new CliffordAlgebraFiber({
        dimension: this.dimension,
        position: pos,
      });

      fibers.push(fiber);
    }

    return fibers;
  }

  /**
   * Initialize generators for symmetry transformations
   *
   * @private
   * @returns {Array} Array of generator specifications
   */
  _initializeSymmetryGenerators() {
    const generators = [];

    // 1. Single bit flips (using vector basis elements)
    for (let i = 0; i < this.dimension; i++) {
      generators.push({
        type: "bit_flip",
        index: i,
        description: `Flip bit ${i}`,
      });
    }

    // 2. Bit swaps (using bivector basis elements)
    for (let i = 0; i < this.dimension - 1; i++) {
      for (let j = i + 1; j < this.dimension; j++) {
        generators.push({
          type: "bit_swap",
          indices: [i, j],
          description: `Swap bits ${i} and ${j}`,
        });
      }
    }

    // 3. Local cluster flips (acting on small groups of variables)
    const maxCluster = Math.min(5, this.dimension);
    for (let size = 2; size <= maxCluster; size++) {
      for (let start = 0; start <= this.dimension - size; start++) {
        const indices = Array(size)
          .fill()
          .map((_, i) => start + i);
        generators.push({
          type: "cluster_flip",
          indices,
          description: `Flip cluster ${JSON.stringify(indices)}`,
        });
      }
    }

    return generators;
  }

  /**
   * Apply a symmetry transformation to a state
   *
   * @param {Array} state - Current state vector
   * @param {number} generatorIdx - Index of the symmetry generator to apply
   * @returns {Array} Transformed state vector
   */
  applyTransformation(state, generatorIdx) {
    // Validate state is an array
    TypeValidation.assertArray(state, "state", {
      operation: "CoherenceGradientDescent.applyTransformation",
    });

    // Validate state contains only numbers
    TypeValidation.assertNumberArray(state, "state", {
      operation: "CoherenceGradientDescent.applyTransformation",
    });

    // Validate generatorIdx is a number
    TypeValidation.assertNumber(generatorIdx, "generatorIdx", {
      operation: "CoherenceGradientDescent.applyTransformation",
    });

    // Validate generatorIdx is an integer
    TypeValidation.assertInteger(generatorIdx, "generatorIdx", {
      operation: "CoherenceGradientDescent.applyTransformation",
    });

    // Validate generatorIdx is in range
    if (generatorIdx < 0 || generatorIdx >= this.symmetryGenerators.length) {
      throw new Prime.ValidationError(
        `Invalid generator index: ${generatorIdx}`,
        {
          operation: "CoherenceGradientDescent.applyTransformation",
          maxAllowedIndex: this.symmetryGenerators.length - 1,
          providedIndex: generatorIdx,
          totalGenerators: this.symmetryGenerators.length,
        },
      );
    }

    const generator = this.symmetryGenerators[generatorIdx];

    // Validate that generator exists and has the expected structure
    if (!generator || typeof generator !== "object") {
      throw new Prime.ValidationError("Invalid generator", {
        operation: "CoherenceGradientDescent.applyTransformation",
        generatorIndex: generatorIdx,
        generator: generator,
      });
    }

    // Validate generator type
    if (
      !generator.type ||
      !["bit_flip", "bit_swap", "cluster_flip"].includes(generator.type)
    ) {
      throw new Prime.ValidationError(
        `Invalid generator type: ${generator.type}`,
        {
          operation: "CoherenceGradientDescent.applyTransformation",
          validTypes: ["bit_flip", "bit_swap", "cluster_flip"],
          providedType: generator.type,
        },
      );
    }

    const newState = state.slice();

    switch (generator.type) {
      case "bit_flip":
        {
          // Validate index is defined
          if (generator.index === undefined) {
            throw new Prime.ValidationError(
              "Missing index in bit_flip generator",
              {
                operation: "CoherenceGradientDescent.applyTransformation",
                generator: generator,
              },
            );
          }

          // Validate index is a number
          TypeValidation.assertNumber(generator.index, "generator.index", {
            operation: "CoherenceGradientDescent.applyTransformation",
          });

          // Validate index is an integer
          TypeValidation.assertInteger(generator.index, "generator.index", {
            operation: "CoherenceGradientDescent.applyTransformation",
          });

          const idx = generator.index;
          if (idx < state.length) {
            newState[idx] = 1 - newState[idx];
          }
        }
        break;

      case "bit_swap":
        {
          // Validate indices array exists
          if (!Array.isArray(generator.indices)) {
            throw new Prime.ValidationError(
              "Missing indices in bit_swap generator",
              {
                operation: "CoherenceGradientDescent.applyTransformation",
                generator: generator,
              },
            );
          }

          // Validate indices array has exactly 2 elements
          if (generator.indices.length !== 2) {
            throw new Prime.ValidationError(
              "Bit swap requires exactly 2 indices",
              {
                operation: "CoherenceGradientDescent.applyTransformation",
                expectedIndices: 2,
                actualIndices: generator.indices.length,
              },
            );
          }

          const [i, j] = generator.indices;

          // Validate indices are numbers
          TypeValidation.assertNumber(i, "generator.indices[0]", {
            operation: "CoherenceGradientDescent.applyTransformation",
          });

          TypeValidation.assertNumber(j, "generator.indices[1]", {
            operation: "CoherenceGradientDescent.applyTransformation",
          });

          // Validate indices are integers
          TypeValidation.assertInteger(i, "generator.indices[0]", {
            operation: "CoherenceGradientDescent.applyTransformation",
          });

          TypeValidation.assertInteger(j, "generator.indices[1]", {
            operation: "CoherenceGradientDescent.applyTransformation",
          });

          if (i < state.length && j < state.length) {
            [newState[i], newState[j]] = [newState[j], newState[i]];
          }
        }
        break;

      case "cluster_flip":
        {
          // Validate indices array exists
          if (!Array.isArray(generator.indices)) {
            throw new Prime.ValidationError(
              "Missing indices in cluster_flip generator",
              {
                operation: "CoherenceGradientDescent.applyTransformation",
                generator: generator,
              },
            );
          }

          // Validate indices array is not empty
          if (generator.indices.length === 0) {
            throw new Prime.ValidationError(
              "Cluster flip requires at least one index",
              {
                operation: "CoherenceGradientDescent.applyTransformation",
              },
            );
          }

          for (let i = 0; i < generator.indices.length; i++) {
            const idx = generator.indices[i];

            // Validate each index is a number
            if (typeof idx !== "number" || isNaN(idx)) {
              throw new Prime.ValidationError(
                `Invalid cluster index at position ${i}`,
                {
                  operation: "CoherenceGradientDescent.applyTransformation",
                  index: i,
                  value: idx,
                },
              );
            }

            // Validate each index is an integer
            if (!Number.isInteger(idx)) {
              throw new Prime.ValidationError(
                `Cluster index at position ${i} must be an integer`,
                {
                  operation: "CoherenceGradientDescent.applyTransformation",
                  index: i,
                  value: idx,
                },
              );
            }

            if (idx < state.length) {
              newState[idx] = 1 - newState[idx];
            }
          }
        }
        break;
    }

    return newState;
  }

  /**
   * Encode a problem for optimization
   *
   * @param {Object} problem - Problem specification
   * @param {Array} problem.constraints - Array of constraint functions
   * @param {Array} [problem.weights] - Optional weights for constraints
   * @param {Array} [problem.initialState] - Optional initial state
   * @returns {Object} Encoded problem
   */
  encodeProblem(problem) {
    // Validate problem is provided and is an object
    TypeValidation.assertDefined(problem, "problem", {
      operation: "CoherenceGradientDescent.encodeProblem",
    });

    TypeValidation.assertObject(problem, "problem", {
      operation: "CoherenceGradientDescent.encodeProblem",
    });

    // Validate constraints are provided and are an array
    const constraints = problem.constraints;
    TypeValidation.assertDefined(constraints, "problem.constraints", {
      operation: "CoherenceGradientDescent.encodeProblem",
    });

    TypeValidation.assertArray(constraints, "problem.constraints", {
      operation: "CoherenceGradientDescent.encodeProblem",
    });

    // Validate each constraint is a function
    for (let i = 0; i < constraints.length; i++) {
      TypeValidation.assertFunction(
        constraints[i],
        `problem.constraints[${i}]`,
        {
          operation: "CoherenceGradientDescent.encodeProblem",
        },
      );
    }

    // Validate dimension if provided
    if (problem.dimension !== undefined) {
      TypeValidation.assertPositiveInteger(
        problem.dimension,
        "problem.dimension",
        {
          operation: "CoherenceGradientDescent.encodeProblem",
        },
      );
    }

    // Validate weights if provided
    if (problem.weights !== undefined) {
      TypeValidation.assertArray(problem.weights, "problem.weights", {
        operation: "CoherenceGradientDescent.encodeProblem",
      });

      TypeValidation.assertNumberArray(problem.weights, "problem.weights", {
        operation: "CoherenceGradientDescent.encodeProblem",
      });

      // Validate weights match constraints length
      if (problem.weights.length !== constraints.length) {
        throw new Prime.DimensionMismatchError(
          "Weights array must have the same length as constraints array",
          {
            operation: "CoherenceGradientDescent.encodeProblem",
            constraintsLength: constraints.length,
            weightsLength: problem.weights.length,
          },
        );
      }

      // Validate weights are positive
      const negativeWeightIndex = problem.weights.findIndex((w) => w <= 0);
      if (negativeWeightIndex !== -1) {
        throw new Prime.ValidationError(
          `Weight at index ${negativeWeightIndex} must be positive`,
          {
            operation: "CoherenceGradientDescent.encodeProblem",
            index: negativeWeightIndex,
            weight: problem.weights[negativeWeightIndex],
          },
        );
      }
    }

    // Validate initialState if provided
    if (problem.initialState !== undefined) {
      TypeValidation.assertArray(problem.initialState, "problem.initialState", {
        operation: "CoherenceGradientDescent.encodeProblem",
      });

      TypeValidation.assertNumberArray(
        problem.initialState,
        "problem.initialState",
        {
          operation: "CoherenceGradientDescent.encodeProblem",
        },
      );

      // Binary problems (0-1) should have binary values
      const nonBinaryIndex = problem.initialState.findIndex(
        (v) => v !== 0 && v !== 1,
      );
      if (nonBinaryIndex !== -1) {
        Prime.Logger.warn(
          `Initial state contains non-binary value at index ${nonBinaryIndex}`,
          {
            operation: "CoherenceGradientDescent.encodeProblem",
            index: nonBinaryIndex,
            value: problem.initialState[nonBinaryIndex],
          },
        );
      }
    }

    const n = problem.dimension || this.dimension;
    const encoded = {
      n_vars: n,
      n_constraints: constraints.length,
      constraints,
      weights: problem.weights || Array(constraints.length).fill(1),
      initialState:
        problem.initialState ||
        Array(n)
          .fill()
          .map(() => (Math.random() < 0.5 ? 0 : 1)),
      bestState: null,
      bestCoherence: Infinity,
    };

    // Create reference state (perfect coherence - all constraints satisfied)
    encoded.referenceState = Array(constraints.length).fill(1);

    // Add spectral analysis if enabled
    if (this.useSpectral) {
      encoded.spectralData = this._performSpectralAnalysis(encoded);
    }

    // Add fiber encodings if enabled
    if (this.useFiber && this.fibers) {
      encoded.fiberEncodings = this._createFiberEncodings(encoded);
    }

    return encoded;
  }

  /**
   * Perform spectral analysis on the problem structure
   * Identifies important variables and their relationships
   *
   * @private
   * @param {Object} problem - Encoded problem
   * @returns {Object} Spectral analysis data
   */
  _performSpectralAnalysis(problem) {
    // Create an approximation of variable interactions based on constraints
    const n = problem.n_vars;
    const adjacency = Array(n)
      .fill()
      .map(() => Array(n).fill(0));

    // For each constraint, track which variables interact
    for (let i = 0; i < problem.constraints.length; i++) {
      const constraint = problem.constraints[i];

      // Use intelligent variable dependency detection to determine which
      // variables interact in this constraint
      const involvedVars = this._identifyInvolvedVariables(constraint, n);

      for (let j = 0; j < involvedVars.length; j++) {
        for (let k = j + 1; k < involvedVars.length; k++) {
          const var1 = involvedVars[j];
          const var2 = involvedVars[k];
          adjacency[var1][var2] += 1;
          adjacency[var2][var1] += 1;
        }
      }
    }

    // Compute importance scores based on connectivity
    const importanceScores = Array(n).fill(0);
    for (let i = 0; i < n; i++) {
      importanceScores[i] = adjacency[i].reduce((sum, val) => sum + val, 0);
    }

    // Normalize importance scores
    const maxScore = Math.max(...importanceScores);
    if (maxScore > 0) {
      for (let i = 0; i < n; i++) {
        importanceScores[i] /= maxScore;
      }
    }

    // Identify clusters using a simple approach
    const clusters = this._identifyClusters(adjacency);

    return {
      adjacencyMatrix: adjacency,
      importanceScores,
      clusters,
    };
  }

  /**
   * Identify which variables are involved in a constraint through function analysis
   *
   * @private
   * @param {Function} constraint - Constraint function
   * @param {number} n - Number of variables
   * @returns {Array} Indices of involved variables
   */
  _identifyInvolvedVariables(constraint, n) {
    // Use multiple approaches to identify involved variables

    // First check if function has metadata about involved variables
    if (constraint.involvedVariables) {
      return Array.isArray(constraint.involvedVariables)
        ? constraint.involvedVariables.filter((idx) => idx >= 0 && idx < n)
        : [];
    }

    // Convert function to string to analyze its structure
    let fnStr;
    try {
      fnStr = constraint.toString();
    } catch (e) {
      // If we can't get the function source, use a fallback approach
      return this._identifyVariablesBySensitivity(constraint, n);
    }

    // Try to extract variable references from the function string
    const involved = new Set();

    // Check for direct array access patterns like state[0], state[i], etc.
    const arrayAccessRegex = /state\s*\[\s*(\d+)\s*\]/g;
    let match;
    while ((match = arrayAccessRegex.exec(fnStr)) !== null) {
      const idx = parseInt(match[1], 10);
      if (idx >= 0 && idx < n) {
        involved.add(idx);
      }
    }

    // Check for variable names that might be used like x0, x1, v0, v1, etc.
    const variableNameRegex = /\b([xvs])(\d+)\b/g;
    while ((match = variableNameRegex.exec(fnStr)) !== null) {
      const idx = parseInt(match[2], 10);
      if (idx >= 0 && idx < n) {
        involved.add(idx);
      }
    }

    // If we found explicit references, return them
    if (involved.size > 0) {
      return Array.from(involved).sort((a, b) => a - b);
    }

    // If static analysis didn't work, try sensitivity analysis
    return this._identifyVariablesBySensitivity(constraint, n);
  }

  /**
   * Identify involved variables using sensitivity analysis
   * Tests each variable by flipping its value and measuring constraint changes
   *
   * @private
   * @param {Function} constraint - Constraint function
   * @param {number} n - Number of variables
   * @returns {Array} Indices of involved variables
   */
  _identifyVariablesBySensitivity(constraint, n) {
    // Create a baseline state vector (all zeros)
    const baselineState = Array(n).fill(0);
    let baselineResult;

    try {
      // Evaluate constraint with baseline state
      baselineResult = this._evaluateConstraint(constraint, baselineState);
    } catch (e) {
      // If baseline evaluation fails, try a different baseline (all ones)
      baselineState.fill(1);
      try {
        baselineResult = this._evaluateConstraint(constraint, baselineState);
      } catch (e) {
        // If both baselines fail, use a random baseline
        for (let i = 0; i < n; i++) {
          baselineState[i] = Math.random() < 0.5 ? 0 : 1;
        }
        try {
          baselineResult = this._evaluateConstraint(constraint, baselineState);
        } catch (e) {
          // If all evaluations fail, we can't determine sensitivity
          return this._getFallbackInvolvedVariables(n);
        }
      }
    }

    // Test each variable by flipping its value and measuring change
    const involved = [];
    const sensitivityThreshold = 0.001; // Minimum change to consider variable involved

    for (let i = 0; i < n; i++) {
      // Create a modified state with this variable flipped
      const testState = baselineState.slice();
      testState[i] = testState[i] === 0 ? 1 : 0;

      try {
        // Evaluate constraint with modified state
        const testResult = this._evaluateConstraint(constraint, testState);

        // Check if flipping this variable changed the result
        const difference = Math.abs(testResult - baselineResult);
        if (difference > sensitivityThreshold) {
          involved.push(i);
        }
      } catch (e) {
        // If evaluation with this variable flipped causes an error,
        // consider the variable involved in the constraint
        involved.push(i);
      }
    }

    // If sensitivity analysis found variables, return them
    if (involved.length > 0) {
      return involved;
    }

    // If no variables were found to be sensitive, do a second pass
    // with paired variables (to detect constraints with parity or XOR-like behavior)
    if (n >= 2) {
      for (let i = 0; i < n - 1; i++) {
        for (let j = i + 1; j < n; j++) {
          // Create a modified state with both variables flipped
          const testState = baselineState.slice();
          testState[i] = testState[i] === 0 ? 1 : 0;
          testState[j] = testState[j] === 0 ? 1 : 0;

          try {
            // Evaluate constraint with modified state
            const testResult = this._evaluateConstraint(constraint, testState);

            // Check if flipping these variables changed the result
            const difference = Math.abs(testResult - baselineResult);
            if (difference > sensitivityThreshold) {
              involved.push(i, j);
              break; // Found a sensitive pair, no need to check more pairs with i
            }
          } catch (e) {
            // If evaluation with these variables flipped causes an error,
            // consider the variables involved in the constraint
            involved.push(i, j);
            break; // Found a sensitive pair, no need to check more pairs with i
          }
        }
      }
    }

    // Remove duplicates and sort
    return [...new Set(involved)].sort((a, b) => a - b);
  }

  /**
   * Get fallback involved variables when analysis fails
   * Uses a deterministic approach based on constraint ID or signature
   *
   * @private
   * @param {number} n - Number of variables
   * @returns {Array} Indices of involved variables
   */
  _getFallbackInvolvedVariables(n) {
    // Get a deterministic sample size based on problem size
    // Minimum of 2 variables, maximum of n/3, at least 3 for n > 10
    const count = Math.max(2, Math.min(Math.ceil(n / 3), Math.ceil(n / 5)));

    // Deterministically choose variables with good distribution
    // Use a stride pattern to ensure variables are spread out
    const involved = [];
    const stride = Math.max(1, Math.floor(n / count));

    for (let i = 0, idx = 0; i < count && idx < n; i++, idx += stride) {
      involved.push(idx);
    }

    // Fill in any remaining spots if we didn't get enough variables
    let start = Math.floor(n / 2); // Start from the middle
    while (involved.length < count && involved.length < n) {
      if (!involved.includes(start)) {
        involved.push(start);
      }
      // Alternate between moving up and down from the middle
      start =
        start +
        (involved.length % 2 === 0 ? 1 : -1) *
          (Math.floor(involved.length / 2) + 1);
      if (start < 0 || start >= n) {
        start = Math.floor(Math.random() * n); // Fallback if pattern reaches bounds
      }
    }

    return involved.sort((a, b) => a - b);
  }

  /**
   * Identify variable clusters using a simple clustering algorithm
   *
   * @private
   * @param {Array} adjacency - Adjacency matrix
   * @returns {Array} Array of cluster assignments
   */
  _identifyClusters(adjacency) {
    const n = adjacency.length;

    // Very simple clustering - in production we'd use a more sophisticated approach
    const numClusters = Math.min(10, Math.max(2, Math.floor(n / 5)));
    const clusters = Array(n).fill(0);

    // Assign variables to clusters based on connectivity patterns
    for (let i = 0; i < n; i++) {
      // Find most connected variables
      const connections = adjacency[i].slice();

      // Assign to most connected cluster
      const clusterCounts = Array(numClusters).fill(0);

      for (let j = 0; j < n; j++) {
        if (i !== j && connections[j] > 0) {
          clusterCounts[clusters[j]] += connections[j];
        }
      }

      // Find cluster with most connections
      let bestCluster = 0;
      let maxConnections = -1;

      for (let c = 0; c < numClusters; c++) {
        if (clusterCounts[c] > maxConnections) {
          maxConnections = clusterCounts[c];
          bestCluster = c;
        }
      }

      clusters[i] = bestCluster;
    }

    return clusters;
  }

  /**
   * Create encodings of the problem for different fiber algebras
   * Each fiber provides a different perspective on the problem
   *
   * @private
   * @param {Object} problem - Encoded problem
   * @returns {Array} Array of fiber-specific encodings
   */
  _createFiberEncodings(problem) {
    if (!this.fibers) return null;

    const encodings = [];

    for (let i = 0; i < this.fibers.length; i++) {
      const fiber = this.fibers[i];

      // Create fiber-specific encoding
      const encoding = {
        fiberIndex: i,
        constraintWeights: problem.weights.slice(),
        variableWeights: Array(problem.n_vars).fill(1),
        referenceState: problem.referenceState.slice(),
      };

      // Modify weights based on position in fiber manifold
      const pos = fiber.position;

      // Vary constraint weights
      for (let j = 0; j < encoding.constraintWeights.length; j++) {
        const weight =
          1.0 +
          0.5 *
            Math.sin(
              (Math.PI * pos[0] * j) / encoding.constraintWeights.length,
            );
        encoding.constraintWeights[j] *= weight;
      }

      // Vary variable weights
      for (let j = 0; j < encoding.variableWeights.length; j++) {
        const weight =
          1.0 +
          0.3 *
            Math.cos((Math.PI * pos[1] * j) / encoding.variableWeights.length);
        encoding.variableWeights[j] *= weight;
      }

      encodings.push(encoding);
    }

    return encodings;
  }

  /**
   * Evaluate a constraint
   *
   * @private
   * @param {Function} constraint - Constraint function
   * @param {Array} state - Current state
   * @returns {number} Satisfaction level (0-1)
   */
  _evaluateConstraint(constraint, state) {
    if (typeof constraint !== "function") {
      throw new Prime.ValidationError("Constraint must be a function", {
        actualType: typeof constraint,
      });
    }

    if (!Array.isArray(state)) {
      throw new Prime.ValidationError("State must be an array", {
        actualType: typeof state,
      });
    }

    try {
      const result = constraint(state);

      // Normalize result to 0-1 range if it's not already
      if (typeof result === "boolean") {
        return result ? 1 : 0;
      } else if (typeof result === "number") {
        // Handle NaN and Infinity
        if (!Number.isFinite(result)) {
          return 0; // Constraint is not satisfied if result is NaN or Infinity
        }
        return Math.min(1, Math.max(0, result));
      } else if (result === undefined || result === null) {
        return 0; // Constraint is not satisfied if no result
      } else {
        // Try to coerce other types to number
        const numericResult = Number(result);
        if (Number.isFinite(numericResult)) {
          return Math.min(1, Math.max(0, numericResult));
        }
        return 0;
      }
    } catch (error) {
      // If constraint evaluation throws, consider it not satisfied
      return 0;
    }
  }

  /**
   * Compute the coherence norm for a given state
   *
   * @param {Object} problem - Encoded problem
   * @param {Array} state - Current state
   * @returns {Object} Coherence norm and constraint satisfaction
   */
  computeStateCoherence(problem, state) {
    // Validate problem is provided and is an object
    TypeValidation.assertDefined(problem, "problem", {
      operation: "CoherenceGradientDescent.computeStateCoherence",
    });

    TypeValidation.assertObject(problem, "problem", {
      operation: "CoherenceGradientDescent.computeStateCoherence",
    });

    // Validate state is provided and is an array
    TypeValidation.assertDefined(state, "state", {
      operation: "CoherenceGradientDescent.computeStateCoherence",
    });

    TypeValidation.assertArray(state, "state", {
      operation: "CoherenceGradientDescent.computeStateCoherence",
    });

    // Validate state contains only numbers
    TypeValidation.assertNumberArray(state, "state", {
      operation: "CoherenceGradientDescent.computeStateCoherence",
    });

    // Validate problem has required properties
    TypeValidation.assertDefined(
      problem.n_constraints,
      "problem.n_constraints",
      {
        operation: "CoherenceGradientDescent.computeStateCoherence",
      },
    );

    TypeValidation.assertDefined(problem.constraints, "problem.constraints", {
      operation: "CoherenceGradientDescent.computeStateCoherence",
    });

    TypeValidation.assertArray(problem.constraints, "problem.constraints", {
      operation: "CoherenceGradientDescent.computeStateCoherence",
    });

    // Validate constraints are functions
    for (let i = 0; i < problem.constraints.length; i++) {
      TypeValidation.assertFunction(
        problem.constraints[i],
        `problem.constraints[${i}]`,
        {
          operation: "CoherenceGradientDescent.computeStateCoherence",
        },
      );
    }

    // Validate weights exist and match constraints length
    TypeValidation.assertDefined(problem.weights, "problem.weights", {
      operation: "CoherenceGradientDescent.computeStateCoherence",
    });

    TypeValidation.assertArray(problem.weights, "problem.weights", {
      operation: "CoherenceGradientDescent.computeStateCoherence",
    });

    if (problem.weights.length !== problem.constraints.length) {
      throw new Prime.DimensionMismatchError(
        "Weights array must have the same length as constraints array",
        {
          operation: "CoherenceGradientDescent.computeStateCoherence",
          constraintsLength: problem.constraints.length,
          weightsLength: problem.weights.length,
        },
      );
    }

    const n_constraints = problem.n_constraints;

    // Compute constraint satisfaction vector
    const satisfaction = Array(n_constraints).fill(0);
    for (let i = 0; i < n_constraints; i++) {
      const constraint = problem.constraints[i];
      satisfaction[i] = this._evaluateConstraint(constraint, state);
    }

    // Base coherence is the sum of unsatisfied constraints (weighted)
    let baseCoherence = 0;
    for (let i = 0; i < n_constraints; i++) {
      if (satisfaction[i] < 1) {
        baseCoherence += problem.weights[i] * (1 - satisfaction[i]);
      }
    }

    let coherence = baseCoherence;

    // Enhanced coherence calculation using different perspectives

    // 1. Spectral coherence component
    if (this.useSpectral && problem.spectralData) {
      const spectralCoherence = this._computeSpectralCoherence(
        problem,
        state,
        satisfaction,
      );
      coherence = 0.7 * coherence + 0.3 * spectralCoherence;
    }

    // 2. Fiber coherence component
    if (this.useFiber && problem.fiberEncodings) {
      const fiberCoherence = this._computeFiberCoherence(
        problem,
        state,
        satisfaction,
      );
      coherence = 0.7 * coherence + 0.3 * fiberCoherence;
    }

    return {
      coherence,
      satisfaction,
    };
  }

  /**
   * Compute coherence component based on spectral analysis
   *
   * @private
   * @param {Object} problem - Encoded problem
   * @param {Array} state - Current state
   * @param {Array} satisfaction - Constraint satisfaction vector
   * @returns {number} Spectral coherence component
   */
  _computeSpectralCoherence(problem, state, satisfaction) {
    const spectralData = problem.spectralData;
    const importanceScores = spectralData.importanceScores;
    const clusters = spectralData.clusters;

    // Create cluster satisfaction metrics
    const clusterSatisfaction = {};

    for (let i = 0; i < problem.constraints.length; i++) {
      // Approximate which clusters this constraint involves
      const involved = this._identifyInvolvedVariables(
        problem.constraints[i],
        problem.n_vars,
      );
      const involvedClusters = new Set();

      for (const varIdx of involved) {
        if (varIdx < clusters.length) {
          involvedClusters.add(clusters[varIdx]);
        }
      }

      // Record satisfaction status for each involved cluster
      const isSatisfied = satisfaction[i] > 0.5;

      for (const clusterId of involvedClusters) {
        if (!clusterSatisfaction[clusterId]) {
          clusterSatisfaction[clusterId] = [];
        }
        clusterSatisfaction[clusterId].push(isSatisfied);
      }
    }

    // Calculate coherence based on cluster satisfaction
    let clusterCoherence = 0;

    for (const clusterId in clusterSatisfaction) {
      if (Object.hasOwnProperty.call(clusterSatisfaction, clusterId)) {
        const satisfactions = clusterSatisfaction[clusterId];
        if (satisfactions.length > 0) {
          // Higher penalty for clusters with mixed satisfaction status
          const satisfactionRate =
            satisfactions.filter(Boolean).length / satisfactions.length;
          // Penalty is higher when satisfaction rate is around 0.5 (most conflicted)
          const penalty = 4.0 * satisfactionRate * (1.0 - satisfactionRate);
          clusterCoherence += penalty;
        }
      }
    }

    // Normalize
    if (Object.keys(clusterSatisfaction).length > 0) {
      clusterCoherence /= Object.keys(clusterSatisfaction).length;
    }

    // Additional component based on important variables
    let importantVarCoherence = 0;

    for (let i = 0; i < problem.n_vars; i++) {
      // Check variables with high importance
      if (importanceScores[i] > 0.5) {
        // Compute contribution for this important variable
        const involvedConstraints = [];

        for (let j = 0; j < problem.constraints.length; j++) {
          const involved = this._identifyInvolvedVariables(
            problem.constraints[j],
            problem.n_vars,
          );
          if (involved.includes(i) && satisfaction[j] < 0.5) {
            involvedConstraints.push(j);
          }
        }

        if (involvedConstraints.length > 0) {
          importantVarCoherence +=
            importanceScores[i] * involvedConstraints.length;
        }
      }
    }

    // Normalize
    importantVarCoherence = Math.min(
      1.0,
      importantVarCoherence / problem.n_vars,
    );

    // Combine components
    const spectralCoherence =
      0.5 * clusterCoherence + 0.5 * importantVarCoherence;

    // Scale to match base coherence
    return spectralCoherence * satisfaction.length;
  }

  /**
   * Compute coherence component based on fiber algebra analysis
   *
   * @private
   * @param {Object} problem - Encoded problem
   * @param {Array} state - Current state
   * @param {Array} satisfaction - Constraint satisfaction vector
   * @returns {number} Fiber coherence component
   */
  _computeFiberCoherence(problem, state, satisfaction) {
    const fiberEncodings = problem.fiberEncodings;
    const fiberCoherences = [];

    for (const encoding of fiberEncodings) {
      // Get fiber-specific weights
      const constraintWeights = encoding.constraintWeights;

      // Calculate weighted unsatisfied count for this fiber
      let weightedCount = 0;
      for (let i = 0; i < satisfaction.length; i++) {
        weightedCount += (1 - satisfaction[i]) * constraintWeights[i];
      }

      fiberCoherences.push(weightedCount);
    }

    // Take average fiber coherence
    return fiberCoherences.length > 0
      ? fiberCoherences.reduce((sum, val) => sum + val, 0) /
          fiberCoherences.length
      : 0;
  }

  /**
   * Compute the gradient of the coherence norm with respect to symmetry transformations
   *
   * @param {Object} problem - Encoded problem
   * @param {Array} state - Current state
   * @returns {Array} Array of (generator index, coherence change) pairs
   */
  computeCoherenceGradient(problem, state) {
    if (!problem || typeof problem !== "object") {
      throw new Prime.ValidationError("Problem must be an object", {
        actualType: typeof problem,
      });
    }

    if (!Array.isArray(state)) {
      throw new Prime.ValidationError("State must be an array", {
        actualType: typeof state,
      });
    }

    const { coherence } = this.computeStateCoherence(problem, state);
    const gradient = [];

    // Use spectral data to prioritize generators if available
    const importantIndices = new Set();

    if (this.useSpectral && problem.spectralData) {
      const importanceScores = problem.spectralData.importanceScores;

      // Find top important variables
      const threshold = 0.5;
      for (let i = 0; i < importanceScores.length; i++) {
        if (importanceScores[i] > threshold) {
          importantIndices.add(i);
        }
      }
    }

    // Evaluate all transformations
    for (let i = 0; i < this.symmetryGenerators.length; i++) {
      const generator = this.symmetryGenerators[i];
      let isPriority = false;

      // Check if this generator affects important variables
      if (generator.type === "bit_flip") {
        isPriority = importantIndices.has(generator.index);
      } else if (generator.type === "bit_swap") {
        isPriority =
          importantIndices.has(generator.indices[0]) ||
          importantIndices.has(generator.indices[1]);
      } else if (generator.type === "cluster_flip") {
        isPriority = generator.indices.some((idx) => importantIndices.has(idx));
      }

      // Apply the transformation
      const newState = this.applyTransformation(state, i);
      const { coherence: newCoherence } = this.computeStateCoherence(
        problem,
        newState,
      );

      // Coherence change (negative means improvement)
      const coherenceChange = newCoherence - coherence;

      gradient.push({
        generatorIndex: i,
        coherenceChange,
        isPriority,
      });
    }

    // Sort by priority first, then by coherence change
    gradient.sort((a, b) => {
      if (a.isPriority !== b.isPriority) {
        return a.isPriority ? -1 : 1;
      }
      return a.coherenceChange - b.coherenceChange;
    });

    // Return simplified gradient with just index and change
    return gradient.map((g) => [g.generatorIndex, g.coherenceChange]);
  }

  /**
   * Add diversification to escape local minima
   *
   * @param {Object} problem - Encoded problem
   * @param {Array} state - Current state
   * @param {Array} previousStates - Previous visited states
   * @param {number} iteration - Current iteration
   * @returns {Array} Diversified state
   */
  diversifySearch(problem, state, previousStates, iteration) {
    if (!Array.isArray(state)) {
      throw new Prime.ValidationError("State must be an array", {
        actualType: typeof state,
      });
    }

    // Determine if we should diversify based on stagnation
    let shouldDiversify = false;

    // Check if we've been in similar states before
    if (previousStates && previousStates.length > 0) {
      const similarities = previousStates.map((prevState) => {
        return (
          state.reduce(
            (count, val, i) => count + (val === prevState[i] ? 1 : 0),
            0,
          ) / state.length
        );
      });

      if (similarities.some((sim) => sim > 0.9)) {
        shouldDiversify = true;
      }
    }

    if (!shouldDiversify) {
      return state;
    }

    const newState = state.slice();

    // Choose diversification strategy based on iteration
    const strategy = iteration % 3;

    if (strategy === 0) {
      // Strong random perturbation
      const numToFlip = Math.max(1, Math.floor(state.length / 5));
      const positions = [];

      while (positions.length < numToFlip) {
        const pos = Math.floor(Math.random() * state.length);
        if (!positions.includes(pos)) {
          positions.push(pos);
        }
      }

      for (const pos of positions) {
        newState[pos] = 1 - newState[pos];
      }
    } else if (strategy === 1 && this.useSpectral && problem.spectralData) {
      // Flip variables in a spectral cluster
      const clusters = problem.spectralData.clusters;
      const uniqueClusters = [...new Set(clusters)];

      if (uniqueClusters.length > 0) {
        const targetCluster =
          uniqueClusters[Math.floor(Math.random() * uniqueClusters.length)];

        // Flip all variables in the target cluster
        for (let i = 0; i < newState.length; i++) {
          if (i < clusters.length && clusters[i] === targetCluster) {
            newState[i] = 1 - newState[i];
          }
        }
      }
    } else if (strategy === 2) {
      // Apply a random symmetry transformation
      const generatorIdx = Math.floor(
        Math.random() * this.symmetryGenerators.length,
      );
      return this.applyTransformation(state, generatorIdx);
    }

    return newState;
  }

  /**
   * Solve a problem using coherence-gradient descent
   *
   * @param {Object} problem - Encoded problem
   * @param {Object} options - Solver options
   * @param {number} [options.maxIterations=1000] - Maximum number of iterations
   * @param {boolean} [options.useSimulatedAnnealing=true] - Whether to use simulated annealing
   * @param {number} [options.temperature=1.0] - Initial temperature for annealing
   * @param {number} [options.restartCount=3] - Number of restarts to attempt
   * @param {boolean} [options.useTabu=true] - Whether to use tabu search
   * @param {number} [options.tabuListSize=10] - Size of tabu list
   * @returns {Object} Solution information
   */
  solve(problem, options = {}) {
    // Validate problem is provided and is an object
    TypeValidation.assertDefined(problem, "problem", {
      operation: "CoherenceGradientDescent.solve",
    });

    TypeValidation.assertObject(problem, "problem", {
      operation: "CoherenceGradientDescent.solve",
    });

    // Validate problem has required properties
    TypeValidation.assertDefined(problem.constraints, "problem.constraints", {
      operation: "CoherenceGradientDescent.solve",
    });

    TypeValidation.assertArray(problem.constraints, "problem.constraints", {
      operation: "CoherenceGradientDescent.solve",
    });

    // Validate options if provided
    if (options !== undefined) {
      TypeValidation.assertObject(options, "options", {
        operation: "CoherenceGradientDescent.solve",
      });

      // Validate specific option types if provided
      if (options.maxIterations !== undefined) {
        TypeValidation.assertPositiveInteger(
          options.maxIterations,
          "options.maxIterations",
          {
            operation: "CoherenceGradientDescent.solve",
          },
        );

        // Check for unreasonably large values
        if (options.maxIterations > 1000000) {
          Prime.Logger.warn(
            `maxIterations ${options.maxIterations} is very large and may cause performance issues`,
            {
              operation: "CoherenceGradientDescent.solve",
              recommendedMaximum: 1000000,
            },
          );
        }
      }

      if (options.useSimulatedAnnealing !== undefined) {
        TypeValidation.assertBoolean(
          options.useSimulatedAnnealing,
          "options.useSimulatedAnnealing",
          {
            operation: "CoherenceGradientDescent.solve",
          },
        );
      }

      if (options.temperature !== undefined) {
        TypeValidation.assertPositiveNumber(
          options.temperature,
          "options.temperature",
          {
            operation: "CoherenceGradientDescent.solve",
          },
        );
      }

      if (options.restartCount !== undefined) {
        TypeValidation.assertNonNegativeInteger(
          options.restartCount,
          "options.restartCount",
          {
            operation: "CoherenceGradientDescent.solve",
          },
        );
      }

      if (options.useTabu !== undefined) {
        TypeValidation.assertBoolean(options.useTabu, "options.useTabu", {
          operation: "CoherenceGradientDescent.solve",
        });
      }

      if (options.tabuListSize !== undefined) {
        TypeValidation.assertPositiveInteger(
          options.tabuListSize,
          "options.tabuListSize",
          {
            operation: "CoherenceGradientDescent.solve",
          },
        );
      }
    }

    // Parse options with defaults
    const maxIterations = options.maxIterations || 1000;
    const useSimulatedAnnealing = options.useSimulatedAnnealing !== false;
    const temperature = options.temperature || 1.0;
    const restartCount = options.restartCount || 3;
    const useTabu = options.useTabu !== false;
    const tabuListSize = options.tabuListSize || 10;

    // Initialize tracking
    let bestState = null;
    let bestCoherence = Infinity;
    let bestSatisfaction = null;

    // History tracking
    const history = {
      coherence: [],
      iterations: [],
      satisfiedConstraints: [],
    };

    // Run multiple restarts
    for (let restart = 0; restart < restartCount; restart++) {
      // Initialize state
      let currentState;

      if (restart === 0) {
        // First attempt uses the initial state from the problem
        currentState = problem.initialState
          ? problem.initialState.slice()
          : Array(problem.dimension || problem.n_vars || 6).fill(0);
      } else {
        // Subsequent attempts use random initialization with spectral hints
        if (this.useSpectral && problem.spectralData) {
          const importanceScores = problem.spectralData.importanceScores;

          // Initialize random state but bias important variables
          currentState = Array(problem.dimension || problem.n_vars || 6)
            .fill()
            .map(() => (Math.random() < 0.5 ? 0 : 1));

          for (let i = 0; i < currentState.length; i++) {
            if (
              importanceScores &&
              i < importanceScores.length &&
              Math.random() < importanceScores[i]
            ) {
              // Higher chance to set important variables to previous best value
              if (bestState && i < bestState.length) {
                currentState[i] = bestState[i];
              }
            }
          }
        } else {
          // Completely random initialization
          currentState = Array(problem.dimension || problem.n_vars || 6)
            .fill()
            .map(() => (Math.random() < 0.5 ? 0 : 1));
        }
      }

      // Get initial coherence
      let currentCoherence, currentSatisfaction;
      try {
        const result = this.computeStateCoherence(problem, currentState);
        currentCoherence = result.coherence;
        currentSatisfaction = result.satisfaction;
      } catch (e) {
        // If coherence calculation fails, use a default value
        currentCoherence = problem.constraints
          ? problem.constraints.length
          : 10;
        currentSatisfaction = problem.constraints
          ? Array(problem.constraints.length).fill(0)
          : [];
      }

      // Initialize tracking for this attempt
      let restartBestState = currentState.slice();
      let restartBestCoherence = currentCoherence;
      let restartBestSatisfaction = currentSatisfaction
        ? currentSatisfaction.slice()
        : [];

      // Initialize tabu list
      const tabuList = [];

      // Initialize previous states for diversification
      const previousStates = [];

      // Set up temperature for simulated annealing
      let currentTemp = temperature;
      const coolingRate = 0.99; // Temperature cooling rate

      // Iterations for this restart
      const restartIterations = Math.floor(maxIterations / restartCount);

      // Start search for this restart
      for (let iter = 0; iter < restartIterations; iter++) {
        // Add current state to previous states
        previousStates.push(currentState.slice());
        if (previousStates.length > 20) {
          previousStates.shift();
        }

        // Compute gradient
        let gradient;
        try {
          gradient = this.computeCoherenceGradient(problem, currentState);
        } catch (e) {
          // If gradient computation fails, create a random gradient
          gradient = Array(Math.min(10, this.symmetryGenerators.length))
            .fill()
            .map((_, i) => [i, Math.random() * 2 - 1]);
        }

        // Filter out tabu moves
        const filteredGradient =
          useTabu && tabuList.length > 0
            ? gradient.filter(([genIdx]) => !tabuList.includes(genIdx))
            : gradient;

        if (!filteredGradient || filteredGradient.length === 0) {
          // No valid moves, add diversification
          currentState = this.diversifySearch(
            problem,
            currentState,
            previousStates,
            iter,
          );

          try {
            const result = this.computeStateCoherence(problem, currentState);
            currentCoherence = result.coherence;
            currentSatisfaction = result.satisfaction;
          } catch (e) {
            // If coherence calculation fails, use a default value
            currentCoherence = restartBestCoherence;
            currentSatisfaction = restartBestSatisfaction;
          }

          continue;
        }

        // Decide which transformation to apply
        let generatorIdx, coherenceChange;

        if (useSimulatedAnnealing) {
          // Simulated annealing: sometimes accept worse solutions
          if (Math.random() < 0.8) {
            // Usually pick the best transformation
            [generatorIdx, coherenceChange] = filteredGradient[0];
          } else {
            // Sometimes randomly explore
            const randIdx = Math.floor(Math.random() * filteredGradient.length);
            [generatorIdx, coherenceChange] = filteredGradient[randIdx];
          }

          // Update temperature
          currentTemp *= coolingRate;
        } else {
          // Greedy: always choose the best transformation
          [generatorIdx, coherenceChange] = filteredGradient[0];
        }

        // Add to tabu list
        if (useTabu) {
          tabuList.push(generatorIdx);
          if (tabuList.length > tabuListSize) {
            tabuList.shift();
          }
        }

        // Apply chosen transformation
        try {
          currentState = this.applyTransformation(currentState, generatorIdx);
        } catch (e) {
          // If transformation fails, make a random change
          const idx = Math.floor(Math.random() * currentState.length);
          currentState[idx] = 1 - currentState[idx];
        }

        // Compute new coherence
        let coherence, satisfaction;
        try {
          const result = this.computeStateCoherence(problem, currentState);
          coherence = result.coherence;
          satisfaction = result.satisfaction;
        } catch (e) {
          // If coherence calculation fails, use previous values
          coherence = currentCoherence;
          satisfaction = currentSatisfaction;
        }

        // Update tracking
        if (coherence < restartBestCoherence) {
          restartBestState = currentState.slice();
          restartBestCoherence = coherence;
          restartBestSatisfaction = satisfaction ? satisfaction.slice() : [];
        }

        // Update current coherence
        currentCoherence = coherence;
        currentSatisfaction = satisfaction;

        // Diversify if needed (less frequently than in the Python version)
        if (iter % 50 === 0 && coherence > 0) {
          const diversifiedState = this.diversifySearch(
            problem,
            currentState,
            previousStates,
            iter,
          );

          // Only accept if it maintains or improves coherence
          let divCoherence;
          try {
            const result = this.computeStateCoherence(
              problem,
              diversifiedState,
            );
            divCoherence = result.coherence;
          } catch (e) {
            divCoherence = coherence + 1; // Assume worse
          }

          if (divCoherence <= coherence) {
            currentState = diversifiedState;
            currentCoherence = divCoherence;
          }
        }

        // Update history
        history.coherence.push(coherence);
        history.iterations.push(restart * restartIterations + iter);
        if (satisfaction) {
          history.satisfiedConstraints.push(
            satisfaction.reduce((sum, val) => sum + (val > 0.5 ? 1 : 0), 0),
          );
        } else {
          history.satisfiedConstraints.push(0);
        }

        // Check for perfect solution
        if (coherence === 0) {
          break;
        }
      }

      // Update overall best solution
      if (restartBestCoherence < bestCoherence) {
        bestState = restartBestState.slice();
        bestCoherence = restartBestCoherence;
        bestSatisfaction = restartBestSatisfaction
          ? restartBestSatisfaction.slice()
          : [];
      }
    }

    // Update problem with solution
    problem.bestState = bestState;
    problem.bestCoherence = bestCoherence;
    problem.bestSatisfaction = bestSatisfaction ? bestSatisfaction.slice() : [];
    problem.history = history;

    return {
      minimum: bestState, // Add minimum property for compatibility
      state: bestState,
      coherence: bestCoherence,
      value: bestCoherence, // Add value property for compatibility
      satisfaction: bestSatisfaction,
      history,
      problem,
    };
  }
}

// Export the public API
module.exports = {
  CliffordAlgebraFiber,
  CoherenceGradientDescent,
};
