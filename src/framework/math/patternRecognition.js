/**
 * Fiber Algebra Pattern Recognition for the Prime Framework
 * Implements pattern detection using Clifford algebra fiber structures
 */

// Import core if available
let Prime;
try {
  Prime = require("../../core.js");
} catch (e) {
  // Handle case where core isn't available yet
  Prime = {};
}

// Try to import math utilities and coherence module
let mathUtils;
try {
  mathUtils = require("./index.js");
} catch (e) {
  // Create minimal placeholder if not available
  mathUtils = {
    vector: {
      cosineSimilarity: () => ({ similarity: 0 }),
    },
  };
}

let coherenceModule;
try {
  coherenceModule = require("./coherence.js");
} catch (e) {
  coherenceModule = { CliffordAlgebraFiber: null };
}

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

    // For each point in the manifold
    for (let i = 0; i < this.manifold.length; i++) {
      if (CliffordAlgebraFiber) {
        // Use the CliffordAlgebraFiber class if available
        fibers[i] = new CliffordAlgebraFiber({
          dimension: this.dimension,
          position: this.manifold[i],
        });
      } else {
        // Create a simplified fiber structure as fallback
        fibers[i] = {
          position: this.manifold[i],
          dimension: this.dimension,
          state: new Array(Math.pow(2, this.dimension)).fill(0),
          patterns: [],
        };
      }
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
    // Number of basis elements in the full Clifford algebra
    const nBasis = Math.pow(2, this.dimension);

    // Create antisymmetric matrices as Lie algebra generators
    const generators = [];

    // Create simple rotation generators (antisymmetric matrices)
    for (let i = 0; i < Math.min(10, nBasis); i++) {
      for (let j = 0; j < i; j++) {
        // Create a rotation in the i-j plane
        const generator = Array(nBasis)
          .fill()
          .map(() => Array(nBasis).fill(0));
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
    const transformation = Array(nBasis)
      .fill()
      .map((_, i) => {
        return Array(nBasis)
          .fill()
          .map((_, j) => {
            return (i === j ? 1 : 0) + amount * generator[i][j];
          });
      });

    // Apply transformation matrix to state
    const transformed = Array(nBasis).fill(0);
    for (let i = 0; i < nBasis; i++) {
      for (let j = 0; j < nBasis; j++) {
        transformed[i] += transformation[i][j] * state[j];
      }
    }

    // Normalize if needed
    const norm = Math.sqrt(
      transformed.reduce((sum, val) => sum + val * val, 0),
    );
    if (norm > 0) {
      for (let i = 0; i < transformed.length; i++) {
        transformed[i] /= norm;
      }
    }

    return transformed;
  }

  /**
   * Encode data into the fiber algebras across the manifold
   *
   * @param {Array} data - Data to encode (samples × features)
   * @returns {Object} Dictionary mapping fiber indices to encoded states
   */
  encodeData(data) {
    // Ensure data is 2D array
    let processedData = data;
    if (!Array.isArray(data[0])) {
      // If 1D array, reshape to 2D with a single sample
      processedData = [data];
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

    // Normalize data vectors
    normalizedData = normalizedData.map((sample) => {
      const norm = Math.sqrt(sample.reduce((sum, val) => sum + val * val, 0));
      return norm > 0 ? sample.map((val) => val / norm) : sample;
    });

    const encodedStates = {};

    // Encode data into each fiber
    for (const idx in this.fibers) {
      const fiber = this.fibers[idx];

      // Initialize state with zeros
      const nBasis = Math.pow(2, this.dimension);
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

      // Normalize the state
      const norm = Math.sqrt(state.reduce((sum, val) => sum + val * val, 0));
      if (norm > 0) {
        for (let i = 0; i < state.length; i++) {
          state[i] /= norm;
        }
      }

      // Store the encoded state in the fiber
      encodedStates[idx] = state.slice();

      // If using CliffordAlgebraFiber, also set its state
      if (typeof fiber.setState === "function") {
        fiber.setState(state);
      } else {
        fiber.state = state.slice();
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

          // Compute coherence as inner product
          let innerProduct = 0;
          for (let k = 0; k < stateI.length; k++) {
            innerProduct += stateI[k] * stateJ[k];
          }

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
    // Ensure data is 2D
    let processedData = data;
    if (!Array.isArray(data[0])) {
      processedData = [data];
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
   * Extract feature vectors from identified patterns
   *
   * @param {Array} patterns - List of patterns from findPatterns
   * @param {number} nFeatures - Number of features to extract (default: 10)
   * @returns {Array} Feature matrix (patterns × features)
   */
  extractFeatures(patterns, nFeatures = 10) {
    if (!patterns || patterns.length === 0) {
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
    if (!features || features.length === 0) {
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
        // Calculate Euclidean distance
        let distance = 0;
        for (let k = 0; k < features[i].length; k++) {
          distance += Math.pow(features[i][k] - features[j][k], 2);
        }
        distance = Math.sqrt(distance);

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
      throw new TypeError("Input must be an array");
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
