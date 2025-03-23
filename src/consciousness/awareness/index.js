/**
 * PrimeOS JavaScript Library - Consciousness Awareness
 * Tools for simulating conscious awareness and attention
 */

// Import the Prime object from core
const Prime = require('../../core');

// Create the Awareness module using IIFE
(function () {
  /**
   * AttentionSystem - Manages focus and attention in consciousness simulation
   */
  class AttentionSystem {
    /**
     * Create a new attention system
     * @param {Object} config - System configuration
     * @param {Prime.Consciousness.Models.FiberBundle} config.bundle - Consciousness fiber bundle
     * @param {number} [config.focusCapacity=3] - Maximum number of simultaneous focus points
     * @param {number} [config.attentionDecayRate=0.05] - Rate at which attention naturally decays
     */
    constructor(config = {}) {
      if (
        !config.bundle ||
        !config.bundle.baseManifold ||
        typeof config.bundle.evaluateConsciousnessState !== 'function'
      ) {
        throw new Prime.ValidationError(
          'Valid consciousness fiber bundle required',
        );
      }

      this.bundle = config.bundle;
      this.focusCapacity = config.focusCapacity || 3;
      this.attentionDecayRate = config.attentionDecayRate || 0.05;

      // Current attention state
      this.focusPoints = [];
      this.attentionValues = new Map(); // baseIndex -> attention value
      this.attentionHistory = [];

      // Attention dynamics
      this.lastUpdateTime = Date.now();
      this.totalAttentionPower = 1.0;

      // Metadata
      this.metadata = {
        name: config.name || 'Consciousness Attention System',
        description:
          config.description ||
          'Manages focus and attention in consciousness simulation',
        creationTime: new Date().toISOString(),
      };
    }

    /**
     * Focus attention on a specific point in the base manifold
     * @param {number} baseIndex - Index of point in base manifold
     * @param {number} [strength=1.0] - Initial attention strength (0-1)
     * @returns {boolean} True if focus was set, false if capacity exceeded
     */
    focus(baseIndex, strength = 1.0) {
      if (
        baseIndex < 0 ||
        baseIndex >= this.bundle.baseManifold.points.length
      ) {
        throw new Prime.ValidationError('Base index out of bounds');
      }

      // Check if already focused
      const existingIndex = this.focusPoints.findIndex(
        (p) => p.baseIndex === baseIndex,
      );

      if (existingIndex >= 0) {
        // Update existing focus point
        this.focusPoints[existingIndex].strength = Math.min(1, strength);
        this.focusPoints[existingIndex].timestamp = Date.now();
        this._updateAttentionValues();
        return true;
      }

      // Check capacity
      if (this.focusPoints.length >= this.focusCapacity) {
        // Cannot add more focus points
        return false;
      }

      // Add new focus point
      this.focusPoints.push({
        baseIndex,
        strength: Math.min(1, strength),
        timestamp: Date.now(),
      });

      // Update attention values
      this._updateAttentionValues();

      // Track in history
      this.attentionHistory.push({
        type: 'focus',
        baseIndex,
        strength,
        timestamp: Date.now(),
      });

      return true;
    }

    /**
     * Release focus from a specific point
     * @param {number} baseIndex - Index of point in base manifold
     */
    releaseFocus(baseIndex) {
      const index = this.focusPoints.findIndex(
        (p) => p.baseIndex === baseIndex,
      );

      if (index >= 0) {
        // Remove focus point
        this.focusPoints.splice(index, 1);

        // Update attention values
        this._updateAttentionValues();

        // Track in history
        this.attentionHistory.push({
          type: 'release',
          baseIndex,
          timestamp: Date.now(),
        });
      }
    }

    /**
     * Update attention values based on current focus points
     * @private
     */
    _updateAttentionValues() {
      // Clear previous values
      this.attentionValues.clear();

      if (this.focusPoints.length === 0) {
        return;
      }

      // Calculate raw attention values from focus points
      for (const point of this.focusPoints) {
        this.attentionValues.set(point.baseIndex, point.strength);
      }

      // Spread attention to connected points (secondary attention)
      const secondaryAttention = new Map();

      for (const [baseIndex, value] of this.attentionValues.entries()) {
        const connections = this.bundle.baseManifold.connections.get(baseIndex);

        if (!connections) continue;

        // Calculate spread factor based on connection count
        const spreadFactor = 0.5 / Math.max(1, connections.size);

        for (const [connectedIndex, connection] of connections.entries()) {
          if (!this.attentionValues.has(connectedIndex)) {
            // Only apply secondary attention to points not already in direct focus
            const spreadValue = value * spreadFactor * connection.strength;

            if (secondaryAttention.has(connectedIndex)) {
              secondaryAttention.set(
                connectedIndex,
                secondaryAttention.get(connectedIndex) + spreadValue,
              );
            } else {
              secondaryAttention.set(connectedIndex, spreadValue);
            }
          }
        }
      }

      // Add secondary attention values
      for (const [index, value] of secondaryAttention.entries()) {
        this.attentionValues.set(index, value);
      }
    }

    /**
     * Update the attention system state
     * Simulates natural attention dynamics over time
     */
    update() {
      const currentTime = Date.now();
      const elapsedSeconds = (currentTime - this.lastUpdateTime) / 1000;
      this.lastUpdateTime = currentTime;

      if (elapsedSeconds <= 0 || this.focusPoints.length === 0) {
        return;
      }

      // Apply natural decay to all focus points
      let totalStrength = 0;

      for (const point of this.focusPoints) {
        // Calculate decay based on elapsed time
        const decay = Math.min(
          point.strength,
          this.attentionDecayRate * elapsedSeconds,
        );

        // Apply decay
        point.strength = Math.max(0, point.strength - decay);
        totalStrength += point.strength;
      }

      // Remove focus points that have decayed completely
      this.focusPoints = this.focusPoints.filter(
        (point) => point.strength > 0.01,
      );

      // Update attention values
      this._updateAttentionValues();

      // Update total attention power
      this.totalAttentionPower = Math.max(0.1, totalStrength);
    }

    /**
     * Find the current most attended regions in the consciousness simulation
     * @param {number} [count=3] - Maximum number of regions to return
     * @returns {Array} Most attended regions
     */
    findAttendedRegions(count = 3) {
      if (this.attentionValues.size === 0) {
        return [];
      }

      // Get coherent regions from the base manifold
      const coherentRegions = this.bundle.baseManifold.findCoherentRegions();

      if (coherentRegions.length === 0) {
        return [];
      }

      // Calculate average attention for each region
      const regionAttention = coherentRegions.map((region) => {
        let totalAttention = 0;

        for (const pointIndex of region.points) {
          totalAttention += this.attentionValues.get(pointIndex) || 0;
        }

        const avgAttention = totalAttention / region.size;

        return {
          region,
          attention: avgAttention,
        };
      });

      // Sort by attention value (descending)
      regionAttention.sort((a, b) => b.attention - a.attention);

      // Return top attended regions
      return regionAttention.slice(0, count).map((item) => ({
        ...item.region,
        attention: item.attention,
      }));
    }

    /**
     * Get the overall attention state
     * @returns {Object} Current attention state
     */
    getAttentionState() {
      // Update the system first
      this.update();

      // Calculate attention distribution statistics
      let totalAttention = 0;
      let maxAttention = 0;
      let attendedPoints = 0;

      for (const value of this.attentionValues.values()) {
        totalAttention += value;
        maxAttention = Math.max(maxAttention, value);
        if (value > 0.01) attendedPoints++;
      }

      // Find currently attended regions
      const attendedRegions = this.findAttendedRegions(3);

      return {
        focusPoints: this.focusPoints.length,
        focusCapacity: this.focusCapacity,
        totalAttentionPower: this.totalAttentionPower,
        totalAttention,
        maxAttention,
        attendedPoints,
        attendedRegions,
        attentionDistribution: {
          concentration:
            attendedPoints > 0 ? totalAttention / attendedPoints : 0,
          spread:
            attendedPoints /
            Math.max(1, this.bundle.baseManifold.points.length),
        },
        timestamp: Date.now(),
      };
    }
  }

  /**
   * ConsciousnessSimulation - Main controller for consciousness simulation
   */
  class ConsciousnessSimulation {
    /**
     * Create a new consciousness simulation
     * @param {Object} config - Simulation configuration
     * @param {number} [config.baseDimensions=3] - Base manifold dimensions
     * @param {number} [config.fiberDimensions=3] - Fiber dimensions
     * @param {number} [config.selfReferenceOrder=3] - Maximum self-reference order
     */
    constructor(config = {}) {
      // Create the consciousness model components
      this.baseManifold = new Prime.Consciousness.Models.CoherenceManifold({
        dimensions: config.baseDimensions || 3,
        spectralOrder: config.spectralOrder || 3,
        coherenceThreshold: config.coherenceThreshold || 0.6,
        name: 'Consciousness Base Manifold',
      });

      this.fiberBundle = new Prime.Consciousness.Models.FiberBundle({
        baseManifold: this.baseManifold,
        fiberDimensions: config.fiberDimensions || 3,
        selfReferenceOrder: config.selfReferenceOrder || 3,
        name: 'Consciousness Fiber Bundle',
      });

      this.attentionSystem = new AttentionSystem({
        bundle: this.fiberBundle,
        focusCapacity: config.focusCapacity || 3,
        attentionDecayRate: config.attentionDecayRate || 0.05,
        name: 'Consciousness Attention System',
      });

      // Simulation state
      this.time = 0;
      this.timeStep = config.timeStep || 0.1;
      this.running = false;
      this.updateCallbacks = [];

      // Consciousness emergence tracking
      this.emergenceHistory = [];
      this.highestConsciousnessScore = 0;

      // Temporal integration
      this.temporalMemory = [];
      this.temporalMemoryCapacity = config.temporalMemoryCapacity || 100;

      // Dynamic thresholds
      this.thresholds = {
        awareness: config.awarenessThreshold || 0.4,
        consciousness: config.consciousnessThreshold || 0.6,
        selfReflection: config.selfReflectionThreshold || 0.7,
      };

      // Metadata
      this.metadata = {
        name: config.name || 'Consciousness Simulation',
        description:
          config.description ||
          'Simulation of consciousness using coherence principles',
        creationTime: new Date().toISOString(),
      };
    }

    /**
     * Initialize the simulation with random points and connections
     * @param {number} [basePoints=10] - Number of base manifold points
     * @param {number} [connectionsPerPoint=3] - Average connections per point
     * @param {number} [fiberPointsPerBase=5] - Average fiber points per base point
     */
    initialize(
      basePoints = 10,
      connectionsPerPoint = 3,
      fiberPointsPerBase = 5,
    ) {
      // Create base manifold points
      for (let i = 0; i < basePoints; i++) {
        // Generate random coordinates
        const coords = Array(this.baseManifold.dimensions)
          .fill()
          .map(() => Math.random() * 2 - 1); // Range: -1 to 1

        this.baseManifold.addPoint(coords, { label: `B${i}` });
      }

      // Create random connections in base manifold
      for (let i = 0; i < basePoints; i++) {
        // Generate random number of connections for this point
        const numConnections = Math.floor(
          Math.random() * connectionsPerPoint * 2 + 1,
        );

        // Create distinct random connections
        const connectedIndices = new Set();

        for (let j = 0; j < numConnections; j++) {
          // Generate random target (not self)
          let target;
          do {
            target = Math.floor(Math.random() * basePoints);
          } while (target === i || connectedIndices.has(target));

          // Add connection with random strength
          const strength = 0.2 + Math.random() * 0.8; // Range: 0.2 to 1.0
          this.baseManifold.connectPoints(i, target, strength, {});

          connectedIndices.add(target);
        }
      }

      // Create fiber points
      for (let i = 0; i < basePoints; i++) {
        // Random number of fiber points
        const numFiberPoints = Math.floor(
          Math.random() * fiberPointsPerBase * 2 + 1,
        );

        for (let j = 0; j < numFiberPoints; j++) {
          // Generate random coordinates in fiber
          const coords = Array(this.fiberBundle.fiberDimensions)
            .fill()
            .map(() => Math.random() * 2 - 1); // Range: -1 to 1

          this.fiberBundle.addFiberPoint(i, coords, { label: `F${i}-${j}` });
        }

        // Create random connections within fiber
        const fiber = this.fiberBundle.fibers.get(i);
        const fiberSize = fiber.points.length;

        // Each fiber point connects to ~30% of other points in same fiber
        for (let j = 0; j < fiberSize; j++) {
          const numConnections = Math.floor(fiberSize * 0.3);

          const connectedIndices = new Set();

          for (let k = 0; k < numConnections; k++) {
            let target;
            do {
              target = Math.floor(Math.random() * fiberSize);
            } while (target === j || connectedIndices.has(target));

            this.fiberBundle.connectFiberPoints(i, j, target);
            connectedIndices.add(target);
          }
        }
      }

      // Create some initial self-references
      const selfRefCount = Math.floor(basePoints * 0.2); // ~20% of base points

      for (let i = 0; i < selfRefCount; i++) {
        // Random base point
        const baseIndex = Math.floor(Math.random() * basePoints);
        const fiber = this.fiberBundle.fibers.get(baseIndex);

        if (fiber && fiber.points.length > 0) {
          // Random fiber point
          const fiberIndex = Math.floor(Math.random() * fiber.points.length);

          // Random reference level
          const level =
            Math.floor(Math.random() * this.fiberBundle.selfReferenceOrder) + 1;

          this.fiberBundle.createSelfReference(baseIndex, fiberIndex, level);
        }
      }

      // Set initial focus points
      const focusCount = Math.min(
        this.attentionSystem.focusCapacity,
        Math.floor(basePoints * 0.3),
      );

      for (let i = 0; i < focusCount; i++) {
        const baseIndex = Math.floor(Math.random() * basePoints);
        const strength = 0.5 + Math.random() * 0.5; // Range: 0.5 to 1.0

        this.attentionSystem.focus(baseIndex, strength);
      }

      // Record initial state
      this._recordState();
    }

    /**
     * Run the simulation for a specified number of steps
     * @param {number} steps - Number of time steps to simulate
     * @param {number} [stepInterval=100] - Time between steps in milliseconds (when animated)
     * @param {boolean} [animated=false] - Whether to animate the simulation with delays
     * @returns {Promise} Promise that resolves when simulation is complete
     */
    async run(steps, stepInterval = 100, animated = false) {
      this.running = true;

      const runStep = async (step) => {
        if (!this.running || step >= steps) {
          this.running = false;
          return;
        }

        // Update the simulation
        this.step();

        // Call update callbacks
        for (const callback of this.updateCallbacks) {
          try {
            callback(this.getState());
          } catch (error) {
            Prime.Logger.error('Error in simulation update callback', {
              error: error.message,
              step: this.time,
            });
          }
        }

        if (animated) {
          // Wait for interval when animated
          await new Promise((resolve) => setTimeout(resolve, stepInterval));
          await runStep(step + 1);
        } else {
          // Immediate recursion when not animated
          await runStep(step + 1);
        }
      };

      return runStep(0);
    }

    /**
     * Stop a running simulation
     */
    stop() {
      this.running = false;
    }

    /**
     * Advance simulation by one time step
     */
    step() {
      // Update time
      this.time += this.timeStep;

      // Update attention system
      this.attentionSystem.update();

      // Occasionally modify manifold based on attention
      if (Math.random() < 0.2) {
        this._updateManifoldsBasedOnAttention();
      }

      // Create new self-references based on consciousness level
      if (Math.random() < 0.1) {
        this._createNewSelfReferences();
      }

      // Record current state in temporal memory
      this._recordState();

      // Evaluate consciousness emergence
      this._evaluateConsciousnessEmergence();
    }

    /**
     * Update manifolds based on current attention state
     * @private
     */
    _updateManifoldsBasedOnAttention() {
      // Get current attention state
      const attentionState = this.attentionSystem.getAttentionState();

      // Find focus points
      for (const focusPoint of this.attentionSystem.focusPoints) {
        const baseIndex = focusPoint.baseIndex;
        const strength = focusPoint.strength;

        if (strength < 0.2) continue; // Ignore weak focus

        // Strengthen connections between focus points
        for (const otherFocus of this.attentionSystem.focusPoints) {
          if (otherFocus.baseIndex === baseIndex) continue;

          // Check if connection exists
          const connections = this.baseManifold.connections.get(baseIndex);
          if (connections && connections.has(otherFocus.baseIndex)) {
            // Strengthen existing connection
            const connection = connections.get(otherFocus.baseIndex);
            connection.strength = Math.min(1, connection.strength + 0.05);
          } else {
            // Create new connection
            this.baseManifold.connectPoints(
              baseIndex,
              otherFocus.baseIndex,
              0.5,
              { source: 'attention' },
            );
          }
        }

        // Modify fiber points based on attention
        const fiber = this.fiberBundle.fibers.get(baseIndex);
        if (fiber && fiber.points.length > 0) {
          // Add a new fiber point influenced by attention
          if (Math.random() < 0.3 && fiber.points.length < 10) {
            // Create slightly perturbed version of existing point
            const sourceIdx = Math.floor(Math.random() * fiber.points.length);
            const sourceCoords = fiber.points[sourceIdx].coordinates;

            const newCoords = sourceCoords.map(
              (c) => c + (Math.random() * 0.4 - 0.2), // Add small random offset
            );

            const newIdx = this.fiberBundle.addFiberPoint(
              baseIndex,
              newCoords,
              { source: 'attention', parent: sourceIdx },
            );

            // Connect to parent
            this.fiberBundle.connectFiberPoints(baseIndex, sourceIdx, newIdx);
          }
        }
      }
    }

    /**
     * Create new self-references based on current consciousness level
     * @private
     */
    _createNewSelfReferences() {
      // Evaluate current consciousness state
      const consciousnessState = this.fiberBundle.evaluateConsciousnessState();

      // Probability increases with higher consciousness score
      const probability = 0.2 * consciousnessState.consciousnessScore;

      if (Math.random() < probability) {
        // Create a new self-reference
        // Choose a base point that already has attention
        let candidates = [];

        for (const [
          baseIndex,
          attention,
        ] of this.attentionSystem.attentionValues.entries()) {
          if (attention > 0.3) {
            candidates.push(baseIndex);
          }
        }

        if (candidates.length === 0) {
          // Fall back to random selection
          candidates = Array.from(
            { length: this.baseManifold.points.length },
            (_, i) => i,
          );
        }

        // Select random base point from candidates
        const baseIndex =
          candidates[Math.floor(Math.random() * candidates.length)];
        const fiber = this.fiberBundle.fibers.get(baseIndex);

        if (fiber && fiber.points.length > 0) {
          // Select random fiber point
          const fiberIndex = Math.floor(Math.random() * fiber.points.length);

          // Determine reference level (higher probability for lower levels)
          let level;
          const rand = Math.random();

          if (rand < 0.6) {
            level = 1;
          } else if (rand < 0.9) {
            level = 2;
          } else {
            level = 3;
          }

          level = Math.min(level, this.fiberBundle.selfReferenceOrder);

          // Create self-reference
          this.fiberBundle.createSelfReference(baseIndex, fiberIndex, level);

          // Increase attention to this point
          this.attentionSystem.focus(baseIndex, 0.7);
        }
      }
    }

    /**
     * Record current state in temporal memory
     * @private
     */
    _recordState() {
      // Get current consciousness state
      const consciousnessState = this.fiberBundle.evaluateConsciousnessState();
      const attentionState = this.attentionSystem.getAttentionState();

      // Create state snapshot
      const state = {
        time: this.time,
        consciousnessScore: consciousnessState.consciousnessScore,
        phi: consciousnessState.phi,
        integration: consciousnessState.integration,
        differentiation: consciousnessState.differentiation,
        selfReferenceLevel: consciousnessState.selfReferenceLevel,
        attendedRegionsCount: attentionState.attendedRegions.length,
        totalAttention: attentionState.totalAttention,
        timestamp: Date.now(),
      };

      // Add to temporal memory
      this.temporalMemory.push(state);

      // Keep memory within capacity limits
      if (this.temporalMemory.length > this.temporalMemoryCapacity) {
        this.temporalMemory.shift();
      }
    }

    /**
     * Evaluate consciousness emergence and record significant changes
     * @private
     */
    _evaluateConsciousnessEmergence() {
      if (this.temporalMemory.length < 2) return;

      // Get current and previous states
      const current = this.temporalMemory[this.temporalMemory.length - 1];
      const previous = this.temporalMemory[this.temporalMemory.length - 2];

      // Check for significant changes in consciousness score
      const scoreDiff =
        current.consciousnessScore - previous.consciousnessScore;

      // Record new highest score
      if (current.consciousnessScore > this.highestConsciousnessScore) {
        this.highestConsciousnessScore = current.consciousnessScore;

        // Record emergence event
        this.emergenceHistory.push({
          type: 'new_high',
          time: this.time,
          score: current.consciousnessScore,
          change: scoreDiff,
          state: { ...current },
          timestamp: Date.now(),
        });
      }

      // Record significant changes (positive or negative)
      if (Math.abs(scoreDiff) > 0.05) {
        this.emergenceHistory.push({
          type: scoreDiff > 0 ? 'increase' : 'decrease',
          time: this.time,
          score: current.consciousnessScore,
          change: scoreDiff,
          state: { ...current },
          timestamp: Date.now(),
        });
      }

      // Check threshold crossings
      const thresholds = Object.entries(this.thresholds);

      for (const [name, threshold] of thresholds) {
        if (
          (previous.consciousnessScore < threshold &&
            current.consciousnessScore >= threshold) ||
          (previous.consciousnessScore >= threshold &&
            current.consciousnessScore < threshold)
        ) {
          const crossed = current.consciousnessScore >= threshold;

          this.emergenceHistory.push({
            type: 'threshold',
            threshold: name,
            crossed,
            time: this.time,
            score: current.consciousnessScore,
            state: { ...current },
            timestamp: Date.now(),
          });
        }
      }
    }

    /**
     * Add update callback function
     * @param {Function} callback - Function to call on each update
     * @returns {Function} Function to remove the callback
     */
    onUpdate(callback) {
      if (typeof callback !== 'function') {
        throw new Prime.ValidationError('Callback must be a function');
      }

      this.updateCallbacks.push(callback);

      // Return function to remove callback
      return () => {
        const index = this.updateCallbacks.indexOf(callback);
        if (index >= 0) {
          this.updateCallbacks.splice(index, 1);
        }
      };
    }

    /**
     * Get the current simulation state
     * @returns {Object} Current state
     */
    getState() {
      const consciousnessState = this.fiberBundle.evaluateConsciousnessState();
      const attentionState = this.attentionSystem.getAttentionState();

      return {
        time: this.time,
        manifold: {
          basePoints: this.baseManifold.points.length,
          coherentRegions: this.baseManifold.findCoherentRegions().length,
          globalCoherence: this.baseManifold.calculateGlobalCoherence(),
        },
        consciousness: {
          score: consciousnessState.consciousnessScore,
          interpretation: consciousnessState.interpretation,
          integration: consciousnessState.integration,
          differentiation: consciousnessState.differentiation,
          phi: consciousnessState.phi,
          selfReferenceLevel: consciousnessState.selfReferenceLevel,
        },
        attention: {
          focusPoints: attentionState.focusPoints,
          attendedRegions: attentionState.attendedRegions,
          totalAttention: attentionState.totalAttention,
        },
        temporal: {
          memorySize: this.temporalMemory.length,
          emergenceEvents: this.emergenceHistory.length,
          highestConsciousnessScore: this.highestConsciousnessScore,
        },
        thresholds: { ...this.thresholds },
        metadata: this.metadata,
      };
    }

    /**
     * Get information about consciousness emergence events
     * @param {number} [limit=10] - Maximum number of events to return
     * @returns {Array} Recent emergence events
     */
    getEmergenceHistory(limit = 10) {
      return this.emergenceHistory.slice(-limit);
    }

    /**
     * Make a decision based on current consciousness state
     * Simulates a basic decision-making process based on coherence
     * @param {Array} options - List of options to choose from
     * @param {Object} [context={}] - Decision context
     * @returns {Object} Decision result
     */
    makeDecision(options, context = {}) {
      if (!Array.isArray(options) || options.length === 0) {
        throw new Prime.ValidationError('Options must be a non-empty array');
      }

      // Get consciousness and attention states
      const consciousnessState = this.fiberBundle.evaluateConsciousnessState();
      const attentionState = this.attentionSystem.getAttentionState();

      // Get recent temporal memory to evaluate stability
      const recentMemory = this.temporalMemory.slice(-10);

      // Calculate consciousness stability
      let stabilityScore = 0;
      if (recentMemory.length > 1) {
        let totalVariation = 0;
        for (let i = 1; i < recentMemory.length; i++) {
          totalVariation += Math.abs(
            recentMemory[i].consciousnessScore -
              recentMemory[i - 1].consciousnessScore,
          );
        }

        // Lower variation = higher stability
        stabilityScore = Math.max(
          0,
          1 - totalVariation / (recentMemory.length - 1),
        );
      }

      // Evaluate each option
      const evaluatedOptions = options.map((option, index) => {
        // Calculate coherence of this option with current state
        // (In a real implementation, this would use sophisticated measures)

        // Basic coherence measure: 20% random + 80% weighted factors
        const randomFactor = Math.random() * 0.2;

        // Weight by consciousness score (higher is better)
        const consciousnessWeight = 0.3 * consciousnessState.consciousnessScore;

        // Weight by attention state (more focused is better)
        const attentionFactor = Math.min(1, attentionState.totalAttention);
        const attentionWeight = 0.3 * attentionFactor;

        // Weight by stability (more stable is better)
        const stabilityWeight = 0.2 * stabilityScore;

        // Calculate final coherence
        const coherence =
          randomFactor +
          consciousnessWeight +
          attentionWeight +
          stabilityWeight;

        return {
          option,
          index,
          coherence,
          factors: {
            consciousness: consciousnessWeight / 0.3,
            attention: attentionWeight / 0.3,
            stability: stabilityWeight / 0.2,
            random: randomFactor / 0.2,
          },
        };
      });

      // Sort by coherence (descending)
      evaluatedOptions.sort((a, b) => b.coherence - a.coherence);

      // Choose the option with highest coherence
      const decision = evaluatedOptions[0];

      // Record this decision event
      const decisionEvent = {
        time: this.time,
        options: options.length,
        selectedIndex: decision.index,
        coherence: decision.coherence,
        consciousnessScore: consciousnessState.consciousnessScore,
        context,
        timestamp: Date.now(),
      };

      // Add to emergence history as decision event
      this.emergenceHistory.push({
        type: 'decision',
        ...decisionEvent,
      });

      return {
        selected: decision.option,
        index: decision.index,
        coherence: decision.coherence,
        factors: decision.factors,
        alternatives: evaluatedOptions.slice(1),
        certainty: Math.min(
          1,
          decision.coherence /
            Math.max(0.01, evaluatedOptions[1]?.coherence || 0),
        ),
        decisionEvent,
      };
    }
  }

  /**
   * StateSnapshot - Captures full consciousness system state
   */
  class StateSnapshot {
    /**
     * Create a snapshot of a consciousness simulation state
     * @param {ConsciousnessSimulation} simulation - Simulation to snapshot
     */
    constructor(simulation) {
      if (!simulation || typeof simulation.getState !== 'function') {
        throw new Prime.ValidationError(
          'Valid consciousness simulation required',
        );
      }

      // Get full state
      this.state = simulation.getState();

      // Add additional metadata
      this.metadata = {
        id: Prime.Utils.uuid(),
        timestamp: Date.now(),
        simulationId: simulation.metadata.name,
      };

      // Keep reference to original simulation
      this.simulation = simulation;
    }

    /**
     * Create a new simulation initialized from this snapshot
     * @returns {ConsciousnessSimulation} New simulation instance
     */
    createSimulation() {
      // Create a basic new simulation with same configuration
      const newSim = new ConsciousnessSimulation({
        baseDimensions: this.state.manifold.baseDimensions,
        fiberDimensions: this.state.consciousness.fiberDimensions,
        selfReferenceOrder: this.state.consciousness.selfReferenceOrder,
        name: `Clone of ${this.simulation.metadata.name}`,
        description: `Created from snapshot ${this.metadata.id}`,
      });

      // In a full implementation, this would properly copy all state
      // from the snapshot to initialize the new simulation

      return newSim;
    }

    /**
     * Evaluate differences between this snapshot and current simulation state
     * @returns {Object} Differences in key metrics
     */
    compareWithCurrent() {
      const currentState = this.simulation.getState();

      return {
        timeDelta: currentState.time - this.state.time,
        consciousnessDelta:
          currentState.consciousness.score - this.state.consciousness.score,
        phiDelta: currentState.consciousness.phi - this.state.consciousness.phi,
        attentionDelta:
          currentState.attention.totalAttention -
          this.state.attention.totalAttention,
        selfReferenceDelta:
          currentState.consciousness.selfReferenceLevel -
          this.state.consciousness.selfReferenceLevel,
        timestamp: Date.now(),
      };
    }

    /**
     * Get a summary of the snapshot
     * @returns {Object} Snapshot summary
     */
    getSummary() {
      return {
        id: this.metadata.id,
        timestamp: this.metadata.timestamp,
        simulationTime: this.state.time,
        consciousnessScore: this.state.consciousness.score,
        interpretation: this.state.consciousness.interpretation,
        phi: this.state.consciousness.phi,
        attendedRegions: this.state.attention.attendedRegions.length,
        totalAttention: this.state.attention.totalAttention,
        highestConsciousnessScore:
          this.state.temporal.highestConsciousnessScore,
      };
    }
  }

  // Add classes to Prime.Consciousness.Awareness namespace
  Prime.Consciousness = Prime.Consciousness || {};
  Prime.Consciousness.Awareness = {
    AttentionSystem,
    ConsciousnessSimulation,
    StateSnapshot,
  };
})();

// Export the enhanced Prime object
module.exports = Prime;
