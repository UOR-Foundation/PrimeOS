/**
 * Fiber Algebra Pattern Recognition for the Prime Framework
 * Implements pattern detection using Clifford algebra fiber structures
 */

// Import Prime core directly to avoid circular dependencies
const Prime = require("../../core/prime.js");

// Import standardized math utilities and coherence module
const StandardMath = require("./index.js").Standard;
const coherenceModule = require("./coherence.js");

// Import type validation
const TypeValidation = require("./type-validation.js");

/**
 * FiberAlgebraPatternRecognition implementation based on the Prime Framework
 * Uses Clifford algebra fibers over a reference manifold to detect patterns
 */
class FiberAlgebraPatternRecognition {
  /**
   * Create a new Fiber Algebra Pattern Recognition system
   *
   * @param {Object} options - Configuration options
   * @param {number} options.dimension - Dimension of the Clifford algebra at each fiber point (default: 8)
   * @param {number} options.manifoldDim - Dimension of the reference manifold (default: 3)
   * @param {number} options.manifoldPoints - Number of points in the reference manifold (default: 5)
   */
  constructor(options = {}) {
    // Validate options if provided
    if (options !== undefined) {
      TypeValidation.assertObject(options, "options", {
        operation: "FiberAlgebraPatternRecognition.constructor",
      });

      // Validate dimension if provided
      if (options.dimension !== undefined) {
        TypeValidation.assertPositiveInteger(
          options.dimension,
          "options.dimension",
          {
            operation: "FiberAlgebraPatternRecognition.constructor",
          },
        );

        // Check for computationally feasible dimensions
        if (options.dimension > 12) {
          Prime.Logger.warn(
            `Dimension ${options.dimension} may lead to computational overflow`,
            {
              operation: "FiberAlgebraPatternRecognition.constructor",
              recommendedMaximum: 12,
            },
          );
        }
      }

      // Validate manifoldDim if provided
      if (options.manifoldDim !== undefined) {
        TypeValidation.assertPositiveInteger(
          options.manifoldDim,
          "options.manifoldDim",
          {
            operation: "FiberAlgebraPatternRecognition.constructor",
          },
        );

        if (options.manifoldDim > 10) {
          Prime.Logger.warn(
            `Manifold dimension ${options.manifoldDim} is unusually high`,
            {
              operation: "FiberAlgebraPatternRecognition.constructor",
              recommendedMaximum: 10,
            },
          );
        }
      }

      // Validate manifoldPoints if provided
      if (options.manifoldPoints !== undefined) {
        TypeValidation.assertPositiveInteger(
          options.manifoldPoints,
          "options.manifoldPoints",
          {
            operation: "FiberAlgebraPatternRecognition.constructor",
          },
        );

        if (options.manifoldPoints > 20) {
          Prime.Logger.warn(
            `Number of manifold points ${options.manifoldPoints} is unusually high`,
            {
              operation: "FiberAlgebraPatternRecognition.constructor",
              recommendedMaximum: 20,
            },
          );
        }
      }
    }

    this.dimension = options.dimension || 8;
    this.manifoldDim = options.manifoldDim || 3;
    this.manifoldPoints = options.manifoldPoints || 5;

    // Initialize reference manifold and fiber algebras
    this.manifold = this._createReferenceManifold();
    this.fibers = this._initializeFibers();

    // Initialize Lie group generators for transformations
    this.lieGenerators = this._createLieGenerators();

    // Cache for computed patterns and coherence
    this._patternCache = {};
    this._coherenceCache = {};
  }

  /**
   * Create a reference manifold as a set of points in a space
   *
   * @private
   * @returns {Array} Array of manifold points
   */
  _createReferenceManifold() {
    // Create manifold points using low-discrepancy sampling for better coverage
    const points = [];
    const phi = (1 + Math.sqrt(5)) / 2; // Golden ratio for quasi-random sequence

    for (let i = 0; i < this.manifoldPoints; i++) {
      // Create quasi-random points in the manifold
      const point = Array(this.manifoldDim).fill(0);

      // Use golden ratio sequence for better distribution
      for (let d = 0; d < this.manifoldDim; d++) {
        point[d] = (i * Math.pow(phi, d + 1)) % 1;
      }

      points.push(point);
    }

    return points;
  }

  /**
   * Initialize the Clifford algebra fibers at each manifold point
   *
   * @private
   * @returns {Object} Dictionary mapping point indices to fiber algebras
   */
  _initializeFibers() {
    const fibers = {};
    const CliffordAlgebraFiber = coherenceModule.CliffordAlgebraFiber;

    if (!CliffordAlgebraFiber) {
      throw new Prime.MathematicalError(
        "CliffordAlgebraFiber implementation is required for pattern recognition",
        { context: { module: "patternRecognition" } },
      );
    }

    // For each point in the manifold
    for (let i = 0; i < this.manifold.length; i++) {
      // Create a proper fiber at this point
      fibers[i] = new CliffordAlgebraFiber({
        dimension: this.dimension,
        position: this.manifold[i],
      });
    }

    return fibers;
  }

  /**
   * Create generators for the Lie group of transformations
   * These will be used to apply symmetry transformations to patterns
   *
   * @private
   * @returns {Array} List of Lie group generators
   */
  _createLieGenerators() {
    // Define safe dimension limits with validation
    const maxSafeDimension = 10;
    if (this.dimension > maxSafeDimension) {
      Prime.Logger.warn(
        `Dimension ${this.dimension} exceeds safe limit, capping at ${maxSafeDimension}`,
        { context: { module: "patternRecognition" } },
      );
    }

    const effectiveDimension = Math.min(maxSafeDimension, this.dimension);
    const maxBasisSize = 1000; // Safe maximum array size
    const nBasis = Math.min(maxBasisSize, Math.pow(2, effectiveDimension));

    // Create antisymmetric matrices as Lie algebra generators
    const generators = [];

    // Create simple rotation generators (antisymmetric matrices)
    for (let i = 0; i < Math.min(10, nBasis); i++) {
      for (let j = 0; j < i; j++) {
        // Create a rotation in the i-j plane - use smaller dimension for extreme cases
        const safeSize = Math.min(100, nBasis);
        const generator = Array(safeSize)
          .fill()
          .map(() => Array(safeSize).fill(0));

        generator[i][j] = 1.0;
        generator[j][i] = -1.0;
        generators.push(generator);

        // Limit the number of generators to avoid excessive computation
        if (generators.length >= 10) {
          break;
        }
      }
      if (generators.length >= 10) {
        break;
      }
    }

    return generators;
  }

  /**
   * Apply a Lie group transformation to a state
   *
   * @private
   * @param {Array} state - State vector
   * @param {Array} generator - Lie algebra generator
   * @param {number} amount - Amount of transformation to apply
   * @returns {Array} Transformed state vector
   */
  _applyLieTransformation(state, generator, amount) {
    // Apply the transformation exp(amount * generator) to the state
    // For small amounts, approximate exp(tG) ≈ I + tG
    const nBasis = state.length;

    // Ensure generator dimensions are compatible with state
    // Check if generator is null or undefined
    if (!generator) {
      // Return a copy of the original state if the generator is invalid
      return state.slice();
    }

    // Get safe dimensions
    const safeGenRows = generator.length || 0;
    const safeGenCols =
      safeGenRows > 0 && Array.isArray(generator[0]) ? generator[0].length : 0;

    // Use the minimum of these dimensions to avoid accessing undefined elements
    const safeDim = Math.min(nBasis, safeGenRows, safeGenCols);

    // Create identity matrix + scaled generator for transformation
    const identity = StandardMath.Matrix.identity(nBasis);
    const generatorMatrix = Array(nBasis)
      .fill()
      .map((_, i) => {
        return Array(nBasis)
          .fill()
          .map((_, j) => {
            // Only access generator elements if within safe bounds
            return i < safeDim && j < safeDim ? generator[i][j] || 0 : 0;
          });
      });

    // Scale generator by amount
    const scaledGenerator = StandardMath.Matrix.scale(generatorMatrix, amount);

    // Add identity and scaled generator
    const transformation = StandardMath.Matrix.add(identity, scaledGenerator);

    // Apply transformation matrix to state (matrix-vector multiplication)
    const transformed = StandardMath.Matrix.multiplyVector(
      transformation,
      state,
    );

    // Normalize the result
    return StandardMath.Vector.normalize(transformed);
  }

  /**
   * Encode data into the fiber algebras across the manifold
   *
   * @param {Array} data - Data to encode (samples × features)
   * @returns {Object} Dictionary mapping fiber indices to encoded states
   */
  encodeData(data) {
    // Validate data is provided and is an array
    TypeValidation.assertDefined(data, "data", {
      operation: "FiberAlgebraPatternRecognition.encodeData",
    });

    TypeValidation.assertArray(data, "data", {
      operation: "FiberAlgebraPatternRecognition.encodeData",
    });

    // Check if data array is empty
    if (data.length === 0) {
      Prime.Logger.warn("Empty data array provided to encodeData", {
        operation: "FiberAlgebraPatternRecognition.encodeData",
      });

      // Return empty encoding for empty data
      return {};
    }

    // Ensure data is 2D array
    let processedData = data;
    if (!Array.isArray(data[0])) {
      // If 1D array, reshape to 2D with a single sample
      processedData = [data];

      Prime.Logger.info(
        "Reshaped 1D data array to 2D array with a single sample",
        {
          operation: "FiberAlgebraPatternRecognition.encodeData",
          originalShape: [data.length],
          newShape: [1, data.length],
        },
      );
    }

    // Validate each sample contains only numbers
    for (let i = 0; i < processedData.length; i++) {
      const sample = processedData[i];

      // Validate sample is an array
      TypeValidation.assertArray(sample, `data[${i}]`, {
        operation: "FiberAlgebraPatternRecognition.encodeData",
      });

      // Validate sample contains only numbers
      try {
        TypeValidation.assertNumberArray(sample, `data[${i}]`, {
          operation: "FiberAlgebraPatternRecognition.encodeData",
        });
      } catch (error) {
        // Handle error, maybe clean the data or ignore non-numeric values
        Prime.Logger.warn(
          `Sample at index ${i} contains non-numeric values. Attempting to convert to numbers.`,
          {
            operation: "FiberAlgebraPatternRecognition.encodeData",
            sampleIndex: i,
            ...error.context,
          },
        );

        // Try to convert non-numeric values to numbers
        for (let j = 0; j < sample.length; j++) {
          if (typeof sample[j] !== "number" || isNaN(sample[j])) {
            const numValue = Number(sample[j]);
            if (!isNaN(numValue)) {
              sample[j] = numValue;
            } else {
              sample[j] = 0; // Replace invalid values with 0
            }
          }
        }
      }
    }

    // Ensure data dimensions are compatible with fiber dimension
    const numSamples = processedData.length;
    const numFeatures = processedData[0].length;

    let normalizedData;
    if (numFeatures > this.dimension) {
      // Truncate if too many features
      normalizedData = processedData.map((sample) =>
        sample.slice(0, this.dimension),
      );
    } else if (numFeatures < this.dimension) {
      // Pad if too few features
      normalizedData = processedData.map((sample) => {
        const padded = sample.slice();
        while (padded.length < this.dimension) {
          padded.push(0);
        }
        return padded;
      });
    } else {
      normalizedData = processedData;
    }

    // Normalize data vectors using standardized math
    normalizedData = normalizedData.map((sample) => {
      return StandardMath.Vector.normalize(sample).values || sample;
    });

    const encodedStates = {};

    // Encode data into each fiber
    for (const idx in this.fibers) {
      const fiber = this.fibers[idx];

      // Define safe dimension limits with validation
      const maxSafeDimension = 10;
      const effectiveDimension = Math.min(maxSafeDimension, this.dimension);
      const maxBasisSize = 1000000; // Safe maximum array size
      const nBasis = Math.min(maxBasisSize, Math.pow(2, effectiveDimension));
      const state = new Array(nBasis).fill(0);

      // Embed data into the vector part (grade-1) of the algebra
      for (let i = 0; i < this.dimension; i++) {
        // The basis index for ei is i+1 (because index 0 is the scalar part)
        const basisIdx = i + 1;
        if (basisIdx < nBasis) {
          for (
            let sampleIdx = 0;
            sampleIdx < normalizedData.length;
            sampleIdx++
          ) {
            // Add the feature value to the corresponding basis element
            state[basisIdx] += normalizedData[sampleIdx][i];
          }
        }
      }

      // Add a contribution to the scalar part
      state[0] = 1.0;

      // Normalize the state using standardized math
      const normalizedState = StandardMath.Vector.normalize(state);
      // Copy normalized values back to the original state array
      for (let i = 0; i < state.length; i++) {
        state[i] = normalizedState[i];
      }

      // Store the encoded state in the fiber
      encodedStates[idx] = state.slice();

      // Set the state on the fiber
      if (typeof fiber.setState === "function") {
        fiber.setState(state);
      } else {
        throw new Prime.ValidationError(
          "Fiber is missing required setState method",
          { context: { fiberId: idx } },
        );
      }
    }

    return encodedStates;
  }

  /**
   * Compute the coherence measure across all fibers for the encoded states
   * This measures how well the pattern is recognized across the manifold
   *
   * @param {Object} encodedStates - Dictionary mapping fiber indices to encoded states
   * @returns {number} Coherence measure (0 to 1, higher is more coherent)
   */
  computeCoherence(encodedStates) {
    // Validate encodedStates is provided and is an object
    TypeValidation.assertDefined(encodedStates, "encodedStates", {
      operation: "FiberAlgebraPatternRecognition.computeCoherence",
    });

    TypeValidation.assertObject(encodedStates, "encodedStates", {
      operation: "FiberAlgebraPatternRecognition.computeCoherence",
    });

    // Check if object is empty
    const keys = Object.keys(encodedStates);
    if (keys.length === 0) {
      Prime.Logger.warn(
        "Empty encodedStates object provided to computeCoherence",
        {
          operation: "FiberAlgebraPatternRecognition.computeCoherence",
        },
      );

      return 0; // Return minimum coherence for empty states
    }

    // Validate each encoded state is an array of numbers
    for (const key in encodedStates) {
      const state = encodedStates[key];

      // Validate state is an array
      TypeValidation.assertArray(state, `encodedStates[${key}]`, {
        operation: "FiberAlgebraPatternRecognition.computeCoherence",
      });

      // Validate state contains only numbers
      TypeValidation.assertNumberArray(state, `encodedStates[${key}]`, {
        operation: "FiberAlgebraPatternRecognition.computeCoherence",
      });

      // Check for extreme values that might cause numerical instability
      try {
        TypeValidation.validateArrayMagnitudes(
          state,
          `encodedStates[${key}]`,
          { minMagnitude: 1e-100, maxMagnitude: 1e100, allowZero: true },
          { operation: "FiberAlgebraPatternRecognition.computeCoherence" },
        );
      } catch (error) {
        // Convert to warning for extreme values instead of error
        if (error instanceof Prime.NumericOverflowError) {
          Prime.Logger.warn(
            `State vector contains extreme values that may cause numerical instability`,
            {
              operation: "FiberAlgebraPatternRecognition.computeCoherence",
              fiberIndex: key,
              ...error.context,
            },
          );
        }
      }
    }

    // Hash the encoded states for caching
    const stateHash = Object.values(encodedStates).reduce(
      (acc, state) => acc + state.reduce((sum, val) => sum + val, 0),
      0,
    );

    const cacheKey = stateHash.toFixed(6);
    if (this._coherenceCache[cacheKey]) {
      return this._coherenceCache[cacheKey];
    }

    // Compute coherence across fibers using inner products
    const coherenceValues = [];

    // Compare each pair of fibers
    const fiberIndices = Object.keys(encodedStates);
    for (let idx = 0; idx < fiberIndices.length; idx++) {
      for (let jdx = idx + 1; jdx < fiberIndices.length; jdx++) {
        const i = fiberIndices[idx];
        const j = fiberIndices[jdx];

        if (encodedStates[i] && encodedStates[j]) {
          // Get the states
          const stateI = encodedStates[i];
          const stateJ = encodedStates[j];

          // Compute coherence as inner product using standardized math
          const innerProduct = StandardMath.Vector.dot(stateI, stateJ);

          // Take absolute value for coherence measure
          coherenceValues.push(Math.abs(innerProduct));
        }
      }
    }

    // Compute average coherence across all pairs
    let avgCoherence =
      coherenceValues.length > 0
        ? coherenceValues.reduce((sum, val) => sum + val, 0) /
          coherenceValues.length
        : 0;

    // Normalize coherence to [0,1] range
    // If the coherence is greater than 1, we scale it down
    if (avgCoherence > 1.0) {
      avgCoherence = 1.0;
    } else if (avgCoherence < 0.0) {
      avgCoherence = 0.0;
    }

    // Cache the result
    this._coherenceCache[cacheKey] = avgCoherence;

    return avgCoherence;
  }

  /**
   * Apply Lie group transformations to find invariant structures
   * This helps identify symmetries and transformational patterns
   *
   * @param {Object} encodedStates - Dictionary mapping fiber indices to encoded states
   * @returns {Array} List of transformed state dictionaries
   */
  applyTransformations(encodedStates) {
    // Validate input
    if (!encodedStates || typeof encodedStates !== "object") {
      throw new Prime.ValidationError("Encoded states must be a valid object", {
        context: { actual: typeof encodedStates },
      });
    }

    const transformedStatesList = [];

    // Apply each generator with different amounts
    for (let genIdx = 0; genIdx < this.lieGenerators.length; genIdx++) {
      const generator = this.lieGenerators[genIdx];

      // Apply with different strengths
      for (const amount of [0.05, 0.1, 0.2]) {
        const transformedStates = {};

        // Apply transformation to each fiber
        for (const idx in encodedStates) {
          const state = encodedStates[idx];
          const transformed = this._applyLieTransformation(
            state,
            generator,
            amount,
          );
          transformedStates[idx] = transformed;
        }

        transformedStatesList.push(transformedStates);
      }
    }

    return transformedStatesList;
  }

  /**
   * Find patterns in the data using fiber algebra analysis
   *
   * @param {Array} data - Data array (samples × features)
   * @param {number} nPatterns - Number of patterns to find (default: 3)
   * @returns {Array} List of extracted patterns with metadata
   */
  findPatterns(data, nPatterns = 3) {
    // Validate data is provided and is an array
    TypeValidation.assertDefined(data, "data", {
      operation: "FiberAlgebraPatternRecognition.findPatterns",
    });

    TypeValidation.assertArray(data, "data", {
      operation: "FiberAlgebraPatternRecognition.findPatterns",
    });

    // Validate nPatterns is a positive integer
    if (nPatterns !== undefined) {
      TypeValidation.assertPositiveInteger(nPatterns, "nPatterns", {
        operation: "FiberAlgebraPatternRecognition.findPatterns",
      });

      // Check for unreasonably large value
      if (nPatterns > 100) {
        Prime.Logger.warn(
          `Requested ${nPatterns} patterns, which is unusually high`,
          {
            operation: "FiberAlgebraPatternRecognition.findPatterns",
            recommendedMaximum: 100,
          },
        );

        // Cap at a reasonable number to avoid excessive computation
        nPatterns = 100;
      }
    }

    // Ensure data is 2D
    let processedData = data;
    if (!Array.isArray(data[0])) {
      processedData = [data];

      Prime.Logger.info(
        "Reshaped 1D data array to 2D array with a single sample",
        {
          operation: "FiberAlgebraPatternRecognition.findPatterns",
          originalShape: [data.length],
          newShape: [1, data.length],
        },
      );
    }

    // Validate data contains only numeric values
    for (let i = 0; i < processedData.length; i++) {
      const sample = processedData[i];

      // Validate sample is an array
      TypeValidation.assertArray(sample, `data[${i}]`, {
        operation: "FiberAlgebraPatternRecognition.findPatterns",
      });

      // Validate sample contains only numbers, or can be converted to numbers
      try {
        TypeValidation.assertNumberArray(sample, `data[${i}]`, {
          operation: "FiberAlgebraPatternRecognition.findPatterns",
        });
      } catch (error) {
        // Handle error by converting to numbers where possible
        Prime.Logger.warn(
          `Sample at index ${i} contains non-numeric values. Converting to numbers or using 0.`,
          {
            operation: "FiberAlgebraPatternRecognition.findPatterns",
            ...error.context,
          },
        );

        // Convert non-numeric values
        for (let j = 0; j < sample.length; j++) {
          if (typeof sample[j] !== "number" || isNaN(sample[j])) {
            const numValue = Number(sample[j]);
            if (!isNaN(numValue)) {
              sample[j] = numValue;
            } else {
              sample[j] = 0; // Replace invalid values with 0
            }
          }
        }
      }
    }

    // Normalize data if needed
    const maxVal = Math.max(
      ...processedData.flatMap((arr) => arr.map(Math.abs)),
    );
    if (maxVal > 1.0) {
      processedData = processedData.map((sample) =>
        sample.map((val) => val / maxVal),
      );
    }

    // Encode the full dataset
    const encodedStates = this.encodeData(processedData);

    // Compute initial coherence
    let baseCoherence = this.computeCoherence(encodedStates);

    // Ensure coherence is in [0,1] range
    baseCoherence = Math.max(0, Math.min(1, baseCoherence));

    // Apply transformations to find more patterns
    const transformedStatesList = this.applyTransformations(encodedStates);

    // Evaluate coherence of each transformation
    const coherenceScores = [];
    for (let i = 0; i < transformedStatesList.length; i++) {
      const transformedStates = transformedStatesList[i];
      let coherence = this.computeCoherence(transformedStates);

      // Ensure coherence is in [0,1] range
      coherence = Math.max(0, Math.min(1, coherence));

      coherenceScores.push([i, coherence]);
    }

    // Sort by coherence (highest first)
    coherenceScores.sort((a, b) => b[1] - a[1]);

    // Extract the top patterns
    const patterns = [];

    // Add the base pattern
    const basePattern = {
      type: "base",
      coherence: baseCoherence,
      states: encodedStates,
      transformation: null,
      strength: 0.0,
    };
    patterns.push(basePattern);

    // Add patterns from transformations
    for (let i = 0; i < Math.min(nPatterns - 1, coherenceScores.length); i++) {
      const [transIdx, coherence] = coherenceScores[i];
      const transformedStates = transformedStatesList[transIdx];

      // Determine which generator and amount were used
      const generatorIdx = Math.floor(transIdx / 3); // Since we used 3 amounts per generator
      const amountIdx = transIdx % 3;
      const amount = [0.05, 0.1, 0.2][amountIdx];

      const pattern = {
        type: "transformation",
        coherence: Math.max(0, Math.min(1, coherence)), // Ensure coherence is in [0,1]
        states: transformedStates,
        transformation: generatorIdx,
        strength: amount,
      };
      patterns.push(pattern);
    }

    // Sort patterns by coherence
    patterns.sort((a, b) => b.coherence - a.coherence);

    // Final validation of all coherence values
    for (const pattern of patterns) {
      if (pattern.coherence < 0 || pattern.coherence > 1) {
        pattern.coherence = Math.max(0, Math.min(1, pattern.coherence));
      }
    }

    return patterns;
  }

  /**
   * Extract features from a pattern for advanced analysis
   *
   * @param {Object} pattern - Pattern object from findPatterns
   * @param {Array} data - Original data used to create the pattern
   * @returns {Array} Array of extracted feature objects with weights and indices
   */
  extractPatternFeatures(pattern, data) {
    // Validate inputs
    if (!pattern || !pattern.states) {
      return [];
    }

    if (!Array.isArray(data)) {
      throw new Prime.ValidationError("Data must be an array", {
        context: { actual: typeof data },
      });
    }

    // Extract dimensions from data
    const numFeatures =
      data.length > 0 && Array.isArray(data[0]) ? data[0].length : 0;

    // Get pattern states across fibers
    const states = Object.values(pattern.states);
    if (states.length === 0) {
      return [];
    }

    // Average state across fibers
    const avgState = new Array(states[0].length).fill(0);
    for (const state of states) {
      for (let i = 0; i < state.length; i++) {
        avgState[i] += state[i] / states.length;
      }
    }

    // Find top dimensions by magnitude
    const dimensions = avgState
      .map((val, idx) => ({ value: Math.abs(val), index: idx }))
      .filter((item) => Number.isFinite(item.value) && item.value > 0)
      .sort((a, b) => b.value - a.value)
      .slice(0, 20); // Limit to top 20 dimensions

    // Analyze each dimension for patterns in original data
    const features = [];

    for (const dim of dimensions) {
      // Skip scalar component (index 0)
      if (dim.index === 0) continue;

      // For grade-1 components (vector basis), map to original data features
      if (dim.index > 0 && dim.index <= numFeatures) {
        const dataIndex = dim.index - 1; // Index in original data (0-based)

        // Calculate the relevance of this feature across data samples
        let relevance = 0;
        if (data.length > 0) {
          for (const sample of data) {
            if (Array.isArray(sample) && dataIndex < sample.length) {
              relevance += Math.abs(sample[dataIndex]);
            }
          }
          relevance /= data.length;
        }

        features.push({
          indices: [dataIndex],
          weight: dim.value * (1 + relevance),
          type: "direct",
          sign: Math.sign(avgState[dim.index]),
        });
      }
      // For higher grade components, map to combinations of features
      else if (dim.index > numFeatures) {
        // Convert basis index to binary to identify which original features are involved
        // For bivectors (grade 2), two bits will be set in the binary representation
        // This is a simplification - a proper implementation would use the basis structure
        const binaryRep = (dim.index >>> 0)
          .toString(2)
          .padStart(numFeatures + 1, "0");
        const involvedIndices = [];

        for (let i = 0; i < binaryRep.length; i++) {
          if (binaryRep[i] === "1") {
            involvedIndices.push(binaryRep.length - 1 - i);
          }
        }

        if (involvedIndices.length > 0) {
          features.push({
            indices: involvedIndices,
            weight: dim.value,
            type: "composite",
            sign: Math.sign(avgState[dim.index]),
          });
        }
      }
    }

    // Sort by weight and return
    return features.sort((a, b) => b.weight - a.weight);
  }

  /**
   * Extract feature vectors from identified patterns
   *
   * @param {Array} patterns - List of patterns from findPatterns
   * @param {number} nFeatures - Number of features to extract (default: 10)
   * @returns {Array} Feature matrix (patterns × features)
   */
  extractFeatures(patterns, nFeatures = 10) {
    // Validate input
    if (!Array.isArray(patterns)) {
      throw new Prime.ValidationError("Patterns must be an array", {
        context: { actual: typeof patterns },
      });
    }

    if (patterns.length === 0) {
      return [];
    }

    // Initialize feature matrix
    const features = Array(patterns.length)
      .fill()
      .map(() => Array(nFeatures).fill(0));

    for (let i = 0; i < patterns.length; i++) {
      const pattern = patterns[i];

      // Feature 1: Coherence score
      features[i][0] = pattern.coherence;

      // Feature 2: Pattern type (0 for base, 1 for transformation)
      features[i][1] = pattern.type === "base" ? 0 : 1;

      // Feature 3: Transformation strength (if applicable)
      features[i][2] = pattern.strength || 0;

      // Features 4-6: Principal components of states (averaged across fibers)
      const states = Object.values(pattern.states);
      if (states.length > 0) {
        // Compute mean state
        const meanState = Array(states[0].length).fill(0);
        for (const state of states) {
          for (let j = 0; j < state.length; j++) {
            meanState[j] += state[j] / states.length;
          }
        }

        // Use first few components as features
        for (let j = 0; j < Math.min(3, meanState.length); j++) {
          if (j + 3 < nFeatures) {
            features[i][j + 3] = meanState[j];
          }
        }
      }

      // Features 7-10: Statistical moments of state distribution
      if (states.length > 0) {
        // Calculate mean of all states first
        const statesMean = Array(states[0].length).fill(0);
        for (const state of states) {
          for (let j = 0; j < state.length; j++) {
            statesMean[j] += state[j] / states.length;
          }
        }

        // Compute statistical moments
        for (let j = 0; j < Math.min(4, nFeatures - 6); j++) {
          // j+1 is the moment order (1st, 2nd, 3rd, 4th)
          let moment = 0;

          for (const state of states) {
            for (let k = 0; k < state.length; k++) {
              moment +=
                Math.pow(state[k] - statesMean[k], j + 1) / states.length;
            }
          }

          features[i][j + 6] = moment;
        }
      }
    }

    return features;
  }

  /**
   * Classify patterns based on extracted features
   *
   * @param {Array} features - Feature matrix from extractFeatures
   * @param {number} nClusters - Number of pattern classes to identify (default: 3)
   * @returns {Array} Array of cluster assignments
   */
  classifyPatterns(features, nClusters = 3) {
    // Validate input
    if (!Array.isArray(features)) {
      throw new Prime.ValidationError("Features must be an array", {
        context: { actual: typeof features },
      });
    }

    if (features.length === 0) {
      return [];
    }

    // Simple clustering using distances
    const clusters = Array(features.length).fill(0);

    if (features.length <= nClusters) {
      // If we have fewer patterns than clusters, each pattern gets its own cluster
      for (let i = 0; i < features.length; i++) {
        clusters[i] = i;
      }
      return clusters;
    }

    // Calculate pairwise distances
    const distances = Array(features.length)
      .fill()
      .map(() => Array(features.length).fill(0));

    for (let i = 0; i < features.length; i++) {
      for (let j = i + 1; j < features.length; j++) {
        // Calculate Euclidean distance using standardized math
        const distance = StandardMath.Vector.distance(features[i], features[j]);

        distances[i][j] = distance;
        distances[j][i] = distance;
      }
    }

    // Initialize first cluster center
    const centers = [0];

    // Greedily choose remaining cluster centers
    for (let c = 1; c < nClusters; c++) {
      // Find the pattern furthest from all existing centers
      let maxMinDist = -1;
      let maxIdx = -1;

      for (let i = 0; i < features.length; i++) {
        if (!centers.includes(i)) {
          // Compute minimum distance to any center
          let minDist = Infinity;
          for (const center of centers) {
            minDist = Math.min(minDist, distances[i][center]);
          }

          if (minDist > maxMinDist) {
            maxMinDist = minDist;
            maxIdx = i;
          }
        }
      }

      if (maxIdx !== -1) {
        centers.push(maxIdx);
      }
    }

    // Assign each pattern to nearest center
    for (let i = 0; i < features.length; i++) {
      let nearestCenter = 0;
      let minDistance = Infinity;

      for (let j = 0; j < centers.length; j++) {
        const centerIdx = centers[j];
        const distance = distances[i][centerIdx];

        if (distance < minDistance) {
          minDistance = distance;
          nearestCenter = j;
        }
      }

      clusters[i] = nearestCenter;
    }

    return clusters;
  }

  /**
   * Complete analysis pipeline: find patterns, extract features, and classify
   *
   * @param {Array} data - Data to analyze
   * @param {number} nPatterns - Number of patterns to find (default: 5)
   * @returns {Object} Analysis results
   */
  analyzeData(data, nPatterns = 5) {
    // Validate input
    if (!Array.isArray(data)) {
      throw new Prime.ValidationError("Data must be an array", {
        context: { actual: typeof data },
      });
    }

    // Step 1: Find patterns
    const patterns = this.findPatterns(data, nPatterns);

    // Step 2: Extract features
    const features = this.extractFeatures(patterns);

    // Step 3: Classify patterns
    const nClusters = Math.min(nPatterns, patterns.length);
    const labels =
      nClusters > 0 ? this.classifyPatterns(features, nClusters) : [];

    // Prepare results
    return {
      patterns,
      features,
      labels,
      nPatternsFound: patterns.length,
    };
  }

  /**
   * Create a new fiber at the specified manifold position
   *
   * @param {Array} position - Position in the reference manifold
   * @returns {Object} A new fiber object at the specified position
   */
  createFiber(position) {
    // Validate input
    if (!Array.isArray(position)) {
      throw new Prime.ValidationError("Position must be an array", {
        context: { actual: typeof position },
      });
    }

    const CliffordAlgebraFiber = coherenceModule.CliffordAlgebraFiber;

    if (!CliffordAlgebraFiber) {
      throw new Prime.MathematicalError(
        "CliffordAlgebraFiber implementation is required for fiber creation",
        { context: { module: "patternRecognition" } },
      );
    }

    // Use the CliffordAlgebraFiber class
    const fiber = new CliffordAlgebraFiber({
      dimension: this.dimension,
      position: position,
    });

    // Initialize the state
    const maxSafeDimension = 10;
    const maxBasisSize = 1000000;
    const nBasis = Math.min(
      maxBasisSize,
      Math.pow(2, Math.min(maxSafeDimension, this.dimension)),
    );
    const initialState = new Array(nBasis).fill(0);

    // Set initial values in the first few positions
    for (let i = 0; i < Math.min(position.length, initialState.length); i++) {
      initialState[i] = position[i];
    }

    fiber.setState(initialState);
    return fiber;
  }
}

/**
 * Pattern recognition system for detecting structures in sequence data
 */
class SequencePatternRecognition {
  /**
   * Create a new sequence pattern recognition system
   *
   * @param {Object} options - Configuration options
   * @param {number} options.maxPatternLength - Maximum pattern length to consider (default: 10)
   * @param {number} options.minSupport - Minimum support for patterns (default: 0.1)
   * @param {boolean} options.useCoherence - Whether to use coherence measures (default: true)
   */
  constructor(options = {}) {
    // Validate options if provided
    if (options !== undefined) {
      TypeValidation.assertObject(options, "options", {
        operation: "SequencePatternRecognition.constructor",
      });

      // Validate maxPatternLength if provided
      if (options.maxPatternLength !== undefined) {
        TypeValidation.assertPositiveInteger(
          options.maxPatternLength,
          "options.maxPatternLength",
          {
            operation: "SequencePatternRecognition.constructor",
          },
        );

        // Check for reasonable value
        if (options.maxPatternLength > 1000) {
          Prime.Logger.warn(
            `Maximum pattern length ${options.maxPatternLength} is very large`,
            {
              operation: "SequencePatternRecognition.constructor",
              recommendedMaximum: 1000,
            },
          );
        }
      }

      // Validate minSupport if provided
      if (options.minSupport !== undefined) {
        TypeValidation.assertNumber(options.minSupport, "options.minSupport", {
          operation: "SequencePatternRecognition.constructor",
        });

        // Check for value in range [0,1]
        if (options.minSupport < 0 || options.minSupport > 1) {
          throw new Prime.ValidationError(
            `Minimum support must be between 0 and 1`,
            {
              operation: "SequencePatternRecognition.constructor",
              providedValue: options.minSupport,
              allowedRange: [0, 1],
            },
          );
        }

        // Check for very small value that might lead to excessive patterns
        if (options.minSupport < 0.01) {
          Prime.Logger.warn(
            `Very small minimum support ${options.minSupport} may lead to excessive pattern generation`,
            {
              operation: "SequencePatternRecognition.constructor",
              recommendedMinimum: 0.01,
            },
          );
        }
      }

      // Validate useCoherence if provided
      if (options.useCoherence !== undefined) {
        TypeValidation.assertBoolean(
          options.useCoherence,
          "options.useCoherence",
          {
            operation: "SequencePatternRecognition.constructor",
          },
        );
      }
    }

    this.maxPatternLength = options.maxPatternLength || 10;
    this.minSupport = options.minSupport || 0.1;
    this.useCoherence = options.useCoherence !== false;

    this._patternCache = {};
  }

  /**
   * Find frequent patterns in a sequence
   *
   * @param {Array} sequence - Input sequence
   * @param {number} maxPatterns - Maximum number of patterns to return (default: 10)
   * @returns {Array} Array of pattern objects with support and locations
   */
  findPatterns(sequence, maxPatterns = 10) {
    // Validate input
    if (!Array.isArray(sequence)) {
      throw new Prime.ValidationError("Input must be an array", {
        context: { actual: typeof sequence },
      });
    }

    if (sequence.length === 0) {
      return [];
    }

    // Generate all subsequences of appropriate length
    const patterns = new Map();
    const minPatternLength = 2;

    for (
      let len = minPatternLength;
      len <= Math.min(this.maxPatternLength, sequence.length);
      len++
    ) {
      for (let i = 0; i <= sequence.length - len; i++) {
        const subseq = sequence.slice(i, i + len);
        const patternKey = JSON.stringify(subseq);

        if (!patterns.has(patternKey)) {
          patterns.set(patternKey, {
            pattern: subseq,
            locations: [i],
            length: len,
          });
        } else {
          patterns.get(patternKey).locations.push(i);
        }
      }
    }

    // Convert to array and calculate support
    const patternArray = Array.from(patterns.values()).map((p) => ({
      ...p,
      support: p.locations.length / (sequence.length - p.length + 1),
    }));

    // Filter by minimum support
    const filteredPatterns = patternArray.filter(
      (p) => p.support >= this.minSupport,
    );

    // Sort by support and length (prefer longer patterns with same support)
    filteredPatterns.sort((a, b) => {
      if (Math.abs(a.support - b.support) < 0.001) {
        return b.length - a.length;
      }
      return b.support - a.support;
    });

    // Return top patterns
    return filteredPatterns.slice(0, maxPatterns);
  }

  /**
   * Compute a coherence score for a pattern
   *
   * @param {Array} pattern - The pattern sequence
   * @param {Array} fullSequence - The full sequence containing the pattern
   * @returns {number} Coherence score between 0 and 1
   */
  computePatternCoherence(pattern, fullSequence) {
    // Validate pattern is provided and is an array
    TypeValidation.assertDefined(pattern, "pattern", {
      operation: "SequencePatternRecognition.computePatternCoherence",
    });

    TypeValidation.assertArray(pattern, "pattern", {
      operation: "SequencePatternRecognition.computePatternCoherence",
    });

    // Validate fullSequence is provided and is an array
    TypeValidation.assertDefined(fullSequence, "fullSequence", {
      operation: "SequencePatternRecognition.computePatternCoherence",
    });

    TypeValidation.assertArray(fullSequence, "fullSequence", {
      operation: "SequencePatternRecognition.computePatternCoherence",
    });

    // Check for empty pattern
    if (pattern.length === 0) {
      Prime.Logger.warn("Empty pattern provided to computePatternCoherence", {
        operation: "SequencePatternRecognition.computePatternCoherence",
      });

      return 0; // No coherence for empty pattern
    }

    // Check for empty sequence
    if (fullSequence.length === 0) {
      Prime.Logger.warn("Empty sequence provided to computePatternCoherence", {
        operation: "SequencePatternRecognition.computePatternCoherence",
      });

      return 0; // No coherence with empty sequence
    }

    // Check if pattern is longer than sequence
    if (pattern.length > fullSequence.length) {
      Prime.Logger.warn("Pattern is longer than the full sequence", {
        operation: "SequencePatternRecognition.computePatternCoherence",
        patternLength: pattern.length,
        sequenceLength: fullSequence.length,
      });

      return 0; // Cannot have coherence if pattern doesn't fit in sequence
    }

    if (!this.useCoherence) {
      return 1.0;
    }

    // For coherence, we use a sliding window approach
    const patternLength = pattern.length;

    if (patternLength === 0 || fullSequence.length < patternLength) {
      return 0;
    }

    // Prepare windows across the sequence
    const windows = [];
    for (let i = 0; i <= fullSequence.length - patternLength; i++) {
      windows.push(fullSequence.slice(i, i + patternLength));
    }

    // Calculate coherence as similarity between pattern and each window
    let totalCoherence = 0;

    for (const window of windows) {
      // Compute similarity (simple implementation)
      let similarity = 0;
      for (let i = 0; i < patternLength; i++) {
        if (window[i] === pattern[i]) {
          similarity += 1;
        }
      }
      similarity /= patternLength;

      totalCoherence += similarity;
    }

    // Normalize by number of windows and ensure it's in the [0,1] range
    let coherence = windows.length > 0 ? totalCoherence / windows.length : 0;

    // Clamp to [0,1] range
    coherence = Math.max(0, Math.min(1, coherence));

    return coherence;
  }

  /**
   * Analyze a sequence for patterns and their relationships
   *
   * @param {Array} sequence - Input sequence to analyze
   * @param {Object} options - Analysis options
   * @param {number} options.maxPatterns - Maximum patterns to return (default: 10)
   * @returns {Object} Analysis results
   */
  analyzeSequence(sequence, options = {}) {
    // Validate input
    if (!Array.isArray(sequence)) {
      throw new Prime.ValidationError("Sequence must be an array", {
        context: { actual: typeof sequence },
      });
    }

    const maxPatterns = options.maxPatterns || 10;

    // Find frequent patterns
    const patterns = this.findPatterns(sequence, maxPatterns);

    // Compute coherence for each pattern
    for (const pattern of patterns) {
      pattern.coherence = this.computePatternCoherence(
        pattern.pattern,
        sequence,
      );
    }

    // Find relationships between patterns
    const relationships = [];

    for (let i = 0; i < patterns.length; i++) {
      for (let j = i + 1; j < patterns.length; j++) {
        const patternA = patterns[i].pattern;
        const patternB = patterns[j].pattern;

        // Check for containment
        let relationship = null;
        const strA = JSON.stringify(patternA);
        const strB = JSON.stringify(patternB);

        if (strA.includes(strB)) {
          relationship = "contains";
        } else if (strB.includes(strA)) {
          relationship = "contained_in";
        } else {
          // Check for overlap
          const overlapThreshold =
            Math.min(patternA.length, patternB.length) / 2;
          let maxOverlap = 0;

          // Check suffix of A matching prefix of B
          for (
            let k = 1;
            k <= Math.min(patternA.length, patternB.length);
            k++
          ) {
            const suffixA = patternA.slice(patternA.length - k);
            const prefixB = patternB.slice(0, k);

            if (JSON.stringify(suffixA) === JSON.stringify(prefixB)) {
              maxOverlap = k;
            }
          }

          // Check suffix of B matching prefix of A
          for (
            let k = 1;
            k <= Math.min(patternA.length, patternB.length);
            k++
          ) {
            const suffixB = patternB.slice(patternB.length - k);
            const prefixA = patternA.slice(0, k);

            if (JSON.stringify(suffixB) === JSON.stringify(prefixA)) {
              maxOverlap = Math.max(maxOverlap, k);
            }
          }

          if (maxOverlap >= overlapThreshold) {
            relationship = "overlaps";
          }
        }

        if (relationship) {
          relationships.push({
            patternA: i,
            patternB: j,
            type: relationship,
          });
        }
      }
    }

    return {
      patterns,
      relationships,
      sequenceLength: sequence.length,
      coverage: this._calculateCoverage(patterns, sequence.length),
    };
  }

  /**
   * Calculate how much of the sequence is covered by the discovered patterns
   *
   * @private
   * @param {Array} patterns - Discovered patterns
   * @param {number} sequenceLength - Length of the original sequence
   * @returns {number} Coverage ratio between 0 and 1
   */
  _calculateCoverage(patterns, sequenceLength) {
    if (patterns.length === 0 || sequenceLength === 0) {
      return 0;
    }

    // Create a coverage array
    const coverage = new Array(sequenceLength).fill(false);

    // Mark all positions covered by patterns
    for (const pattern of patterns) {
      for (const start of pattern.locations) {
        for (let i = 0; i < pattern.length; i++) {
          if (start + i < sequenceLength) {
            coverage[start + i] = true;
          }
        }
      }
    }

    // Count covered positions
    const coveredCount = coverage.filter(Boolean).length;

    return coveredCount / sequenceLength;
  }
}

// Export the public API
module.exports = {
  FiberAlgebraPatternRecognition,
  SequencePatternRecognition,
};
