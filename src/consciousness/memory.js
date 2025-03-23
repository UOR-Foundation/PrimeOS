/**
 * Memory Structure - Index experiences by coherence patterns
 *
 * This module implements the memory structure needed for consciousness
 * simulation, indexing experiences by coherence patterns.
 *
 * Key features:
 * - Stores episodic memories with coherence-based indexing
 * - Provides associative recall based on coherence similarity
 * - Implements memory consolidation over time
 * - Supports pattern recognition across stored experiences
 */

// Try to import core if available
let Prime;
try {
  Prime = require('../core.js');
} catch (e) {
  // Handle case where core isn't available yet
  Prime = {};
}

// Import required modules
const MathUtils = require('../framework/math/index.js');

/**
 * MemoryStructure provides mechanisms for storing and retrieving experiences
 * based on coherence patterns
 */
class MemoryStructure {
  /**
   * Create a new memory structure
   *
   * @param {Object} options - Configuration options
   * @param {number} options.shortTermCapacity - Short-term memory capacity (default: 100)
   * @param {number} options.longTermCapacity - Long-term memory capacity (default: 1000)
   * @param {number} options.indexDimension - Dimensions for memory indexing (default: 7)
   * @param {number} options.consolidationThreshold - Threshold for memory consolidation (default: 0.6)
   * @param {number} options.retrievalThreshold - Threshold for memory retrieval (default: 0.7)
   * @param {Function} options.similarityFunction - Function to calculate memory similarity (default: built-in)
   */
  constructor(options = {}) {
    this.shortTermCapacity = options.shortTermCapacity || 100;
    this.longTermCapacity = options.longTermCapacity || 1000;
    this.indexDimension = options.indexDimension || 7;
    this.consolidationThreshold = options.consolidationThreshold || 0.6;
    this.retrievalThreshold = options.retrievalThreshold || 0.7;
    this.similarityFunction =
      options.similarityFunction || this._defaultSimilarityFunction;

    // Memory stores
    this.shortTermMemory = [];
    this.longTermMemory = [];
    this.episodicMemory = [];

    // Memory indices
    this.coherenceIndex = {};
    this.temporalIndex = {};
    this.patternIndex = {};

    // Memory trace tracking
    this._activeTraces = new Map();
    this._lastConsolidation = Date.now();

    // Performance tracking
    this._stats = {
      memoriesStored: 0,
      memoriesRetrieved: 0,
      memoriesConsolidated: 0,
      memoryQueries: 0,
      totalProcessingTime: 0,
    };
  }

  /**
   * Initialize memory structure
   *
   * @param {Object} initialState - Initial state to seed memory
   * @returns {boolean} Success flag
   */
  initialize(initialState) {
    if (!initialState) {
      return false;
    }

    // Create an initial memory from the state
    const initialMemory = this._createMemoryFromState(initialState);

    // Add to short-term memory
    this.shortTermMemory.push(initialMemory);

    // Index the memory
    this._indexMemory(initialMemory);

    this._stats.memoriesStored++;
    return true;
  }

  /**
   * Store a new experience in memory
   *
   * @param {Object} state - Consciousness state to store
   * @param {Object} [context={}] - Additional context for the memory
   * @returns {Object} Memory record
   */
  store(state, context = {}) {
    const startTime = Date.now();

    // Create memory record
    const memory = this._createMemoryFromState(state, context);

    // Add to short-term memory
    this.shortTermMemory.push(memory);

    // Trim short-term memory if needed
    if (this.shortTermMemory.length > this.shortTermCapacity) {
      // Move oldest memories to consolidation
      const oldestMemories = this.shortTermMemory.splice(
        0,
        this.shortTermMemory.length - this.shortTermCapacity,
      );

      this._consolidateMemories(oldestMemories);
    }

    // Index the memory
    this._indexMemory(memory);

    // Update stats
    this._stats.memoriesStored++;
    this._stats.totalProcessingTime += Date.now() - startTime;

    return memory;
  }

  /**
   * Retrieve memories similar to a state
   *
   * @param {Object} state - Query state
   * @param {Object} [options={}] - Retrieval options
   * @param {number} [options.limit=5] - Maximum number of memories to retrieve
   * @param {number} [options.threshold] - Similarity threshold (overrides default)
   * @param {boolean} [options.includeShortTerm=true] - Whether to include short-term memories
   * @param {boolean} [options.includeLongTerm=true] - Whether to include long-term memories
   * @returns {Array} Retrieved memories with similarity scores
   */
  retrieve(state, options = {}) {
    const startTime = Date.now();
    this._stats.memoryQueries++;

    const limit = options.limit || 5;
    const threshold = options.threshold || this.retrievalThreshold;
    const includeShortTerm = options.includeShortTerm !== false;
    const includeLongTerm = options.includeLongTerm !== false;

    // Extract query vector from state
    const queryVector = this._extractStateVector(state);

    // Get memory candidates based on index lookup to reduce search space
    const candidates = this._getCandidatesFromIndices(queryVector);

    // Calculate similarity for candidates
    const withSimilarity = [];

    for (const memory of candidates) {
      // Skip based on options
      if (
        (!includeShortTerm && memory.storage === 'short-term') ||
        (!includeLongTerm && memory.storage === 'long-term')
      ) {
        continue;
      }

      // Calculate similarity
      const similarity = this.similarityFunction(queryVector, memory.vector);

      // Only include if above threshold
      if (similarity >= threshold) {
        withSimilarity.push({
          memory,
          similarity,
        });
      }
    }

    // Sort by similarity (descending) and limit results
    withSimilarity.sort((a, b) => b.similarity - a.similarity);
    const results = withSimilarity.slice(0, limit);

    // Update stats
    this._stats.memoriesRetrieved += results.length;
    this._stats.totalProcessingTime += Date.now() - startTime;

    return results;
  }

  /**
   * Find patterns across memories
   *
   * @param {Object} [options={}] - Pattern finding options
   * @param {number} [options.minSupport=0.3] - Minimum support for patterns
   * @param {number} [options.minConfidence=0.7] - Minimum confidence for patterns
   * @param {number} [options.maxPatterns=10] - Maximum patterns to find
   * @returns {Array} Discovered patterns
   */
  findPatterns(options = {}) {
    const minSupport = options.minSupport || 0.3;
    const minConfidence = options.minConfidence || 0.7;
    const maxPatterns = options.maxPatterns || 10;

    // Combined memories for pattern discovery
    const memories = [...this.shortTermMemory, ...this.longTermMemory];

    if (memories.length < 5) {
      return []; // Not enough data for meaningful patterns
    }

    // Find frequent coherence patterns
    const patterns = this._findCoherencePatterns(memories, minSupport);

    // Calculate confidence for patterns
    const withConfidence = [];

    for (const pattern of patterns) {
      const confidence = this._calculatePatternConfidence(pattern, memories);

      if (confidence >= minConfidence) {
        withConfidence.push({
          ...pattern,
          confidence,
        });
      }
    }

    // Sort by confidence and return top patterns
    withConfidence.sort((a, b) => b.confidence - a.confidence);
    return withConfidence.slice(0, maxPatterns);
  }

  /**
   * Create a memory trace starting from a specific state
   *
   * @param {Object} state - Starting state for trace
   * @param {Object} [options={}] - Trace options
   * @param {number} [options.maxLength=10] - Maximum trace length
   * @param {number} [options.minSimilarity=0.6] - Minimum similarity for trace
   * @returns {Object} Memory trace
   */
  createMemoryTrace(state, options = {}) {
    const maxLength = options.maxLength || 10;
    const minSimilarity = options.minSimilarity || 0.6;

    // Extract vector from state - will be used in future enhancements
    // Currently using direct state matching for simplicity
    this._extractStateVector(state);

    // Create trace ID
    const traceId = `trace_${Date.now()}_${Math.floor(Math.random() * 1000)}`;

    // Find initial memory similar to state
    const initialMatches = this.retrieve(state, {
      limit: 1,
      threshold: minSimilarity,
    });

    if (initialMatches.length === 0) {
      // No matching starting point, create minimal trace
      const trace = {
        id: traceId,
        nodes: [],
        transitions: [],
        startTime: Date.now(),
        active: false,
      };

      this._activeTraces.set(traceId, trace);
      return trace;
    }

    // Use the matching memory as starting point
    const startMemory = initialMatches[0].memory;

    // Build trace through temporally connected memories
    const trace = {
      id: traceId,
      nodes: [startMemory],
      transitions: [],
      startTime: Date.now(),
      active: true,
    };

    // Expand trace forwards and backwards in time
    this._expandTrace(trace, startMemory, maxLength, minSimilarity);

    // Store active trace
    this._activeTraces.set(traceId, trace);

    return trace;
  }

  /**
   * Create a memory record from a state
   *
   * @private
   * @param {Object} state - State to create memory from
   * @param {Object} [context={}] - Additional context
   * @returns {Object} Memory record
   */
  _createMemoryFromState(state, context = {}) {
    // Create a deep copy of the state
    const stateCopy = this._deepCopy(state);

    // Extract vector for indexing
    const vector = this._extractStateVector(stateCopy);

    // Generate a unique ID
    const memoryId = `mem_${Date.now()}_${Math.floor(Math.random() * 10000)}`;

    // Create memory record
    const memory = {
      id: memoryId,
      timestamp: Date.now(),
      vector,
      state: stateCopy,
      context: { ...context },
      coherence: stateCopy.coherence || 0.5,
      significance: this._calculateSignificance(stateCopy, vector),
      storage: 'short-term',
      retrievalCount: 0,
      lastRetrieved: null,
      traces: [],
    };

    return memory;
  }

  /**
   * Index a memory for faster retrieval
   *
   * @private
   * @param {Object} memory - Memory to index
   */
  _indexMemory(memory) {
    // Add to temporal index (by hour)
    const hourKey = Math.floor(memory.timestamp / 3600000);

    if (!this.temporalIndex[hourKey]) {
      this.temporalIndex[hourKey] = [];
    }

    this.temporalIndex[hourKey].push(memory.id);

    // Add to coherence index
    // We'll create multiple indices based on dimensions
    for (
      let i = 0;
      i < Math.min(this.indexDimension, memory.vector.length);
      i++
    ) {
      // Discretize the dimension value (0-1) into 10 bins
      const binKey = Math.floor(memory.vector[i] * 10);
      const dimensionKey = `d${i}_${binKey}`;

      if (!this.coherenceIndex[dimensionKey]) {
        this.coherenceIndex[dimensionKey] = [];
      }

      this.coherenceIndex[dimensionKey].push(memory.id);
    }

    // Calculate and store key patterns
    const patterns = this._extractPatternsFromVector(memory.vector);

    for (const pattern of patterns) {
      const patternKey = `p_${pattern.join('_')}`;

      if (!this.patternIndex[patternKey]) {
        this.patternIndex[patternKey] = [];
      }

      this.patternIndex[patternKey].push(memory.id);
    }
  }

  /**
   * Extract state vector from an object
   *
   * @private
   * @param {Object} state - State object
   * @returns {Array} Vector representation
   */
  _extractStateVector(state) {
    // If state is already an array, return a copy
    if (Array.isArray(state)) {
      return [...state];
    }

    // If state has a vector property, use it
    if (state.vector && Array.isArray(state.vector)) {
      return [...state.vector];
    }

    // Create vector from state properties
    const vector = new Array(this.indexDimension).fill(0);

    // Fill vector with available state attributes
    if (state.attention !== undefined) vector[0] = state.attention;
    if (state.awareness !== undefined) vector[1] = state.awareness;
    if (state.coherence !== undefined) vector[2] = state.coherence;
    if (state.integration !== undefined) vector[3] = state.integration;
    if (state.differentiation !== undefined) vector[4] = state.differentiation;
    if (state.selfReference !== undefined) vector[5] = state.selfReference;
    if (state.temporalBinding !== undefined) vector[6] = state.temporalBinding;

    return vector;
  }

  /**
   * Calculate memory significance
   *
   * @private
   * @param {Object} state - State object
   * @param {Array} vector - State vector
   * @returns {number} Significance value (0-1)
   */
  _calculateSignificance(state, vector) {
    // Combine multiple factors to determine significance:
    // 1. Coherence level (higher coherence = more significant)
    const coherence = state.coherence || vector[2] || 0.5;

    // 2. Attention level (higher attention = more significant)
    const attention = state.attention || vector[0] || 0.3;

    // 3. Self-reference (higher self-reference = more significant)
    const selfReference = state.selfReference || vector[5] || 0.2;

    // 4. Magnitude of vector (higher magnitude = more significant)
    const magnitude =
      Math.sqrt(vector.reduce((sum, v) => sum + v * v, 0)) /
      Math.sqrt(vector.length);

    // Combine factors with different weights
    return (
      0.3 * coherence + 0.3 * attention + 0.2 * selfReference + 0.2 * magnitude
    );
  }

  /**
   * Default similarity function between vectors
   *
   * @private
   * @param {Array} vec1 - First vector
   * @param {Array} vec2 - Second vector
   * @returns {number} Similarity value (0-1)
   */
  _defaultSimilarityFunction(vec1, vec2) {
    if (!vec1 || !vec2 || !vec1.length || !vec2.length) {
      return 0;
    }

    // Calculate cosine similarity
    let dotProduct = 0;
    let mag1 = 0;
    let mag2 = 0;

    const minLength = Math.min(vec1.length, vec2.length);

    for (let i = 0; i < minLength; i++) {
      dotProduct += vec1[i] * vec2[i];
      mag1 += vec1[i] * vec1[i];
      mag2 += vec2[i] * vec2[i];
    }

    const magnitude = Math.sqrt(mag1) * Math.sqrt(mag2);

    if (magnitude < 1e-10) {
      return 0;
    }

    // Convert from [-1,1] to [0,1] range
    return (dotProduct / magnitude + 1) / 2;
  }

  /**
   * Get memory candidates from indices
   *
   * @private
   * @param {Array} vector - Query vector
   * @returns {Array} Candidate memories
   */
  _getCandidatesFromIndices(vector) {
    const candidateIds = new Set();

    // Check coherence index for each dimension
    for (let i = 0; i < Math.min(this.indexDimension, vector.length); i++) {
      // Use the exact bin plus adjacent bins for fuzzy matching
      const bin = Math.floor(vector[i] * 10);

      for (let offset = -1; offset <= 1; offset++) {
        const checkBin = bin + offset;

        if (checkBin >= 0 && checkBin <= 10) {
          const dimensionKey = `d${i}_${checkBin}`;

          if (this.coherenceIndex[dimensionKey]) {
            for (const id of this.coherenceIndex[dimensionKey]) {
              candidateIds.add(id);
            }
          }
        }
      }
    }

    // Get pattern matches
    const patterns = this._extractPatternsFromVector(vector);

    for (const pattern of patterns) {
      const patternKey = `p_${pattern.join('_')}`;

      if (this.patternIndex[patternKey]) {
        for (const id of this.patternIndex[patternKey]) {
          candidateIds.add(id);
        }
      }
    }

    // If we have few or no candidates, include recent memories
    if (candidateIds.size < 10) {
      // Add some recent memories from temporal index
      const currentHour = Math.floor(Date.now() / 3600000);

      // Check current and recent hour buckets
      for (let h = 0; h >= -24; h--) {
        const hourKey = currentHour + h;

        if (this.temporalIndex[hourKey]) {
          for (const id of this.temporalIndex[hourKey]) {
            candidateIds.add(id);
          }
        }

        // Stop if we have enough candidates
        if (candidateIds.size >= 30) {
          break;
        }
      }
    }

    // Resolve IDs to actual memories
    const candidates = [];

    for (const id of candidateIds) {
      // Check in short-term memory
      const shortTerm = this.shortTermMemory.find((m) => m.id === id);
      if (shortTerm) {
        candidates.push(shortTerm);
        continue;
      }

      // Check in long-term memory
      const longTerm = this.longTermMemory.find((m) => m.id === id);
      if (longTerm) {
        candidates.push(longTerm);
      }
    }

    return candidates;
  }

  /**
   * Extract pattern features from vector
   *
   * @private
   * @param {Array} vector - State vector
   * @returns {Array} Patterns
   */
  _extractPatternsFromVector(vector) {
    const patterns = [];

    // Find dimensions with high values (top 3)
    const topDimensions = vector
      .map((value, index) => ({ value, index }))
      .filter((item) => item.value > 0.6)
      .sort((a, b) => b.value - a.value)
      .slice(0, 3)
      .map((item) => item.index);

    if (topDimensions.length > 0) {
      patterns.push(topDimensions);
    }

    // Find dimensions with low values (bottom 3)
    const bottomDimensions = vector
      .map((value, index) => ({ value, index }))
      .filter((item) => item.value < 0.4)
      .sort((a, b) => a.value - b.value)
      .slice(0, 3)
      .map((item) => item.index);

    if (bottomDimensions.length > 0) {
      patterns.push(bottomDimensions);
    }

    // Find significant ratios between dimensions
    if (vector.length >= 6) {
      // Attention/awareness ratio pattern
      if (
        vector[0] > 0 &&
        vector[1] > 0 &&
        Math.abs(vector[0] / vector[1] - 1) > 0.5
      ) {
        patterns.push([0, 1, vector[0] > vector[1] ? 1 : 0]);
      }

      // Coherence/differentiation pattern
      if (
        vector[2] > 0 &&
        vector[4] > 0 &&
        Math.abs(vector[2] / vector[4] - 1) > 0.5
      ) {
        patterns.push([2, 4, vector[2] > vector[4] ? 1 : 0]);
      }
    }

    return patterns;
  }

  /**
   * Consolidate memories from short-term to long-term
   *
   * @private
   * @param {Array} memories - Memories to consolidate
   */
  _consolidateMemories(memories) {
    if (!memories || memories.length === 0) {
      return;
    }

    const consolidated = [];

    for (const memory of memories) {
      // Skip if already in long-term memory
      if (memory.storage === 'long-term') {
        continue;
      }

      // Determine if memory should be consolidated based on significance
      if (
        memory.significance >= this.consolidationThreshold ||
        memory.retrievalCount > 0
      ) {
        // Create compressed version for long-term storage
        const compressedMemory = this._compressMemory(memory);
        compressedMemory.storage = 'long-term';

        // Add to long-term memory
        this.longTermMemory.push(compressedMemory);
        consolidated.push(compressedMemory);
      } else {
        // Add to episodic memory (may be forgotten)
        this.episodicMemory.push(memory);
      }
    }

    // Update stats
    this._stats.memoriesConsolidated += consolidated.length;

    // Check if long-term memory needs pruning
    if (this.longTermMemory.length > this.longTermCapacity) {
      this._pruneLongTermMemory();
    }

    // Check if episodic memory needs pruning
    if (this.episodicMemory.length > this.longTermCapacity * 2) {
      this._pruneEpisodicMemory();
    }
  }

  /**
   * Compress a memory for long-term storage
   *
   * @private
   * @param {Object} memory - Memory to compress
   * @returns {Object} Compressed memory
   */
  _compressMemory(memory) {
    // Create a minimal representation for long-term storage
    return {
      id: memory.id,
      timestamp: memory.timestamp,
      vector: [...memory.vector],
      coherence: memory.coherence,
      significance: memory.significance,
      storage: memory.storage,
      retrievalCount: memory.retrievalCount,
      lastRetrieved: memory.lastRetrieved,

      // Only keep essential state information
      state: {
        attention: memory.state.attention,
        awareness: memory.state.awareness,
        coherence: memory.state.coherence,
        integration: memory.state.integration,
        differentiation: memory.state.differentiation,
        selfReference: memory.state.selfReference,
        temporalBinding: memory.state.temporalBinding,
      },

      // Keep minimal context
      context: {
        type: memory.context.type,
        summary: memory.context.summary,
      },

      // Keep trace references
      traces: [...memory.traces],
    };
  }

  /**
   * Prune long-term memory to capacity
   *
   * @private
   */
  _pruneLongTermMemory() {
    if (this.longTermMemory.length <= this.longTermCapacity) {
      return;
    }

    // Calculate retention score for each memory
    const withScore = this.longTermMemory.map((memory) => {
      // Retention score based on:
      // 1. Significance
      // 2. Retrieval count (rehearsal)
      // 3. Recency of access
      // 4. Association with active traces

      let score = memory.significance * 3;

      // Retrieval count bonus
      score += Math.min(3, memory.retrievalCount) * 0.5;

      // Recency bonus (if retrieved recently)
      if (memory.lastRetrieved) {
        const daysSinceRetrieval =
          (Date.now() - memory.lastRetrieved) / 86400000;
        if (daysSinceRetrieval < 7) {
          score += (7 - daysSinceRetrieval) * 0.1;
        }
      }

      // Trace association bonus
      if (memory.traces.length > 0) {
        score += Math.min(2, memory.traces.length) * 0.2;
      }

      return { memory, score };
    });

    // Sort by score descending
    withScore.sort((a, b) => b.score - a.score);

    // Keep top memories within capacity
    this.longTermMemory = withScore
      .slice(0, this.longTermCapacity)
      .map((item) => item.memory);

    // Move pruned memories to episodic (they might be forgotten)
    const pruned = withScore
      .slice(this.longTermCapacity)
      .map((item) => item.memory);

    if (pruned.length > 0) {
      this.episodicMemory.push(...pruned);
    }
  }

  /**
   * Prune episodic memory
   *
   * @private
   */
  _pruneEpisodicMemory() {
    if (this.episodicMemory.length <= this.longTermCapacity) {
      return;
    }

    // Sort by significance
    this.episodicMemory.sort((a, b) => b.significance - a.significance);

    // Keep only the most significant memories
    this.episodicMemory = this.episodicMemory.slice(0, this.longTermCapacity);
  }

  /**
   * Find coherence patterns in memories
   *
   * @private
   * @param {Array} memories - Memories to analyze
   * @param {number} minSupport - Minimum pattern support
   * @returns {Array} Patterns
   */
  _findCoherencePatterns(memories, minSupport) {
    // Extract features from all memories
    const allFeatures = new Map();

    for (const memory of memories) {
      const patterns = this._extractPatternsFromVector(memory.vector);

      for (const pattern of patterns) {
        const key = pattern.join('_');

        if (!allFeatures.has(key)) {
          allFeatures.set(key, {
            pattern,
            count: 0,
            memories: [],
          });
        }

        const feature = allFeatures.get(key);
        feature.count++;
        feature.memories.push(memory.id);
      }
    }

    // Calculate support for each feature
    const minCount = Math.ceil(memories.length * minSupport);

    // Filter features with sufficient support
    const frequentPatterns = [];

    // Process each feature (key not needed for this operation)
    for (const feature of allFeatures.values()) {
      if (feature.count >= minCount) {
        frequentPatterns.push({
          pattern: feature.pattern,
          support: feature.count / memories.length,
          memories: feature.memories,
        });
      }
    }

    return frequentPatterns;
  }

  /**
   * Calculate confidence for a pattern
   *
   * @private
   * @param {Object} pattern - Pattern to evaluate
   * @param {Array} memories - All memories
   * @returns {number} Confidence value (0-1)
   */
  _calculatePatternConfidence(pattern, memories) {
    // For pattern confidence, we check how consistent the pattern is
    // when its preconditions are met

    // For simplicity, we'll use first two dimensions as precondition
    // and third as outcome (if available)
    if (pattern.pattern.length < 3) {
      return pattern.support; // Use support as fallback
    }

    const preconditionDims = pattern.pattern.slice(0, 2);
    const outcomeDim = pattern.pattern[2];

    let matchingPreconditions = 0;
    let matchingOutcomes = 0;

    for (const memory of memories) {
      // Check if precondition dimensions match
      let preconditionMatch = true;

      for (const dim of preconditionDims) {
        if (memory.vector[dim] < 0.5) {
          preconditionMatch = false;
          break;
        }
      }

      if (preconditionMatch) {
        matchingPreconditions++;

        // Check if outcome dimension matches
        if (
          typeof outcomeDim === 'number' &&
          memory.vector[outcomeDim] >= 0.5
        ) {
          matchingOutcomes++;
        }
      }
    }

    // Calculate confidence
    if (matchingPreconditions === 0) {
      return 0;
    }

    return matchingOutcomes / matchingPreconditions;
  }

  /**
   * Expand a memory trace
   *
   * @private
   * @param {Object} trace - Trace to expand
   * @param {Object} seedMemory - Starting memory
   * @param {number} maxLength - Maximum trace length
   * @param {number} minSimilarity - Minimum similarity
   */
  _expandTrace(trace, seedMemory, maxLength, minSimilarity) {
    // Find temporal neighbors of the seed memory
    const memories = [...this.shortTermMemory, ...this.longTermMemory];

    // Sort by temporal proximity to seed
    const sorted = memories
      .filter((m) => m.id !== seedMemory.id) // Exclude seed itself
      .map((memory) => ({
        memory,
        timeDelta: Math.abs(memory.timestamp - seedMemory.timestamp),
        similarity: this.similarityFunction(memory.vector, seedMemory.vector),
      }))
      .filter((item) => item.similarity >= minSimilarity)
      .sort((a, b) => a.timeDelta - b.timeDelta);

    // Add memories to trace
    for (const item of sorted) {
      // Stop if we've reached max length
      if (trace.nodes.length >= maxLength) {
        break;
      }

      // Add memory to trace if not already included
      if (!trace.nodes.some((m) => m.id === item.memory.id)) {
        trace.nodes.push(item.memory);

        // Add transition
        trace.transitions.push({
          from: seedMemory.id,
          to: item.memory.id,
          similarity: item.similarity,
          timeDelta: item.timeDelta,
        });

        // Update memory's trace references
        item.memory.traces.push(trace.id);
      }
    }

    // Sort nodes by timestamp
    trace.nodes.sort((a, b) => a.timestamp - b.timestamp);
  }

  /**
   * Create deep copy of an object
   *
   * @private
   * @param {Object} obj - Object to copy
   * @returns {Object} Deep copy
   */
  _deepCopy(obj) {
    if (!obj) return null;
    return JSON.parse(JSON.stringify(obj));
  }

  /**
   * Get recently stored memories
   *
   * @param {number} [count=10] - Number of memories to retrieve
   * @returns {Array} Recent memories
   */
  getRecentMemories(count = 10) {
    const numMemories = Math.min(count, this.shortTermMemory.length);
    return this.shortTermMemory.slice(-numMemories);
  }

  /**
   * Get most significant memories
   *
   * @param {number} [count=10] - Number of memories to retrieve
   * @returns {Array} Significant memories
   */
  getSignificantMemories(count = 10) {
    // Combine short and long-term memories
    const allMemories = [...this.shortTermMemory, ...this.longTermMemory];

    // Sort by significance
    const sorted = [...allMemories].sort(
      (a, b) => b.significance - a.significance,
    );

    return sorted.slice(0, Math.min(count, sorted.length));
  }

  /**
   * Get active memory traces
   *
   * @returns {Array} Active traces
   */
  getActiveTraces() {
    return Array.from(this._activeTraces.values());
  }

  /**
   * Get system performance statistics
   *
   * @returns {Object} Performance statistics
   */
  getStats() {
    const averageProcessingTime =
      this._stats.memoriesStored > 0
        ? this._stats.totalProcessingTime / this._stats.memoriesStored
        : 0;

    return {
      ...this._stats,
      shortTermCount: this.shortTermMemory.length,
      longTermCount: this.longTermMemory.length,
      episodicCount: this.episodicMemory.length,
      totalMemories:
        this.shortTermMemory.length +
        this.longTermMemory.length +
        this.episodicMemory.length,
      averageProcessingTime,
      patternCount: Object.keys(this.patternIndex).length,
      consolidationThreshold: this.consolidationThreshold,
    };
  }

  /**
   * Reset the memory structure
   */
  reset() {
    // Clear all memory stores
    this.shortTermMemory = [];
    this.longTermMemory = [];
    this.episodicMemory = [];

    // Clear indices
    this.coherenceIndex = {};
    this.temporalIndex = {};
    this.patternIndex = {};

    // Reset tracking
    this._activeTraces.clear();
    this._lastConsolidation = Date.now();

    // Reset stats
    this._stats = {
      memoriesStored: 0,
      memoriesRetrieved: 0,
      memoriesConsolidated: 0,
      memoryQueries: 0,
      totalProcessingTime: 0,
    };
  }
}

module.exports = MemoryStructure;
