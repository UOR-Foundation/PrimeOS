/**
 * PrimeOS JavaScript Library - Consciousness Models
 * Mathematical models for coherence-based consciousness simulation
 */

// Import the Prime object from core
const Prime = require('../../core');

// Create the Models module using IIFE
(function () {
  /**
   * CoherenceManifold - Represents a mathematical manifold of coherent states
   * Used to model consciousness as regions of high coherence in state space
   */
  class CoherenceManifold {
    /**
     * Create a new coherence manifold
     * @param {Object} config - Manifold configuration
     * @param {number} [config.dimensions=3] - Number of base dimensions for the manifold
     * @param {number} [config.spectralOrder=2] - Order of spectral decomposition
     * @param {number} [config.coherenceThreshold=0.7] - Threshold for coherent states
     * @param {Function} [config.metricTensor] - Custom metric tensor function
     */
    constructor(config = {}) {
      this.dimensions = config.dimensions || 3;
      this.spectralOrder = config.spectralOrder || 2;
      this.coherenceThreshold = config.coherenceThreshold || 0.7;

      // Define the metric tensor (defaults to Euclidean)
      this.metricTensor = config.metricTensor || this._euclideanMetric;

      // Initialize manifold with empty state
      this.points = [];
      this.connections = new Map();
      this.coherenceValues = new Map();

      // Tracking for manifold evolution
      this.history = [];
      this.lastUpdateTime = Date.now();

      // Spectral properties
      this.eigenvalues = [];
      this.eigenvectors = [];

      // Metadata
      this.metadata = {
        name: config.name || 'Coherence Manifold',
        description: config.description || 'A manifold of coherent states',
        creationTime: new Date().toISOString(),
      };
    }

    /**
     * Euclidean metric tensor (identity)
     * @private
     * @param {Array} x - Point in manifold
     * @returns {Array} Metric tensor at point x (identity matrix)
     */
    _euclideanMetric(x) {
      return Array(this.dimensions)
        .fill()
        .map((_, i) =>
          Array(this.dimensions)
            .fill()
            .map((_, j) => (i === j ? 1 : 0)),
        );
    }

    /**
     * Add a point to the manifold
     * @param {Array} point - Coordinates of the point
     * @param {Object} [metadata] - Additional information about the point
     * @returns {number} Index of the added point
     */
    addPoint(point, metadata = {}) {
      if (!Array.isArray(point) || point.length !== this.dimensions) {
        throw new Prime.ValidationError(
          `Point must be an array of length ${this.dimensions}`,
        );
      }

      // Add the point with metadata
      const index = this.points.length;
      this.points.push({
        coordinates: [...point],
        metadata: { ...metadata, addedAt: Date.now() },
      });

      // Initialize connections for this point
      this.connections.set(index, new Map());

      // Calculate initial coherence value
      this._updatePointCoherence(index);

      return index;
    }

    /**
     * Add a connection between points in the manifold
     * @param {number} index1 - Index of first point
     * @param {number} index2 - Index of second point
     * @param {number} [strength=1] - Connection strength
     * @param {Object} [metadata] - Additional information about the connection
     */
    connectPoints(index1, index2, strength = 1, metadata = {}) {
      if (index1 === index2) {
        throw new Prime.ValidationError('Cannot connect a point to itself');
      }

      if (
        index1 < 0 ||
        index1 >= this.points.length ||
        index2 < 0 ||
        index2 >= this.points.length
      ) {
        throw new Prime.ValidationError('Point indices out of bounds');
      }

      // Add bidirectional connections
      this.connections.get(index1).set(index2, {
        strength,
        metadata: { ...metadata, addedAt: Date.now() },
      });

      this.connections.get(index2).set(index1, {
        strength,
        metadata: { ...metadata, addedAt: Date.now() },
      });

      // Update coherence for both points
      this._updatePointCoherence(index1);
      this._updatePointCoherence(index2);
    }

    /**
     * Update a point's position in the manifold
     * @param {number} index - Index of point to update
     * @param {Array} newCoordinates - New coordinates for the point
     */
    updatePoint(index, newCoordinates) {
      if (index < 0 || index >= this.points.length) {
        throw new Prime.ValidationError('Point index out of bounds');
      }

      if (
        !Array.isArray(newCoordinates) ||
        newCoordinates.length !== this.dimensions
      ) {
        throw new Prime.ValidationError(
          `Coordinates must be an array of length ${this.dimensions}`,
        );
      }

      // Store the old state for history
      const oldCoordinates = [...this.points[index].coordinates];

      // Update the coordinates
      this.points[index].coordinates = [...newCoordinates];
      this.points[index].metadata.lastUpdated = Date.now();

      // Update coherence for this point and all connected points
      this._updatePointCoherence(index);

      for (const connectedIndex of this.connections.get(index).keys()) {
        this._updatePointCoherence(connectedIndex);
      }

      // Record the change in history
      this.history.push({
        type: 'pointUpdate',
        index,
        oldCoordinates,
        newCoordinates: [...newCoordinates],
        timestamp: Date.now(),
      });
    }

    /**
     * Calculate coherence value for a specific point
     * @private
     * @param {number} index - Index of point to update
     */
    _updatePointCoherence(index) {
      const point = this.points[index];
      const connections = this.connections.get(index);

      if (connections.size === 0) {
        // Isolated points have minimum coherence
        this.coherenceValues.set(index, 0);
        return;
      }

      // Calculate connection coherence
      let connectionCoherence = 0;
      let totalStrength = 0;

      for (const [connectedIndex, connection] of connections.entries()) {
        const connectedPoint = this.points[connectedIndex];
        const distance = this._calculateDistance(
          point.coordinates,
          connectedPoint.coordinates,
        );

        // Coherence decreases with distance and increases with strength
        const pairCoherence = connection.strength / (1 + distance);
        connectionCoherence += pairCoherence;
        totalStrength += connection.strength;
      }

      // Normalize by total strength
      connectionCoherence /= totalStrength;

      // Calculate inherent coherence of the point's position
      const positionCoherence = this._calculatePositionCoherence(
        point.coordinates,
      );

      // Combine both coherence aspects (60% connections, 40% position)
      const totalCoherence =
        0.6 * connectionCoherence + 0.4 * positionCoherence;

      // Set coherence value
      this.coherenceValues.set(index, totalCoherence);
    }

    /**
     * Calculate inherent coherence of a position in the manifold
     * This is a placeholder for a more sophisticated model-specific implementation
     * @private
     * @param {Array} coordinates - Position to check
     * @returns {number} Coherence value from 0 to 1
     */
    _calculatePositionCoherence(coordinates) {
      // Simple model: closer to origin = higher coherence
      const distanceFromOrigin = Math.sqrt(
        coordinates.reduce((sum, coord) => sum + coord * coord, 0),
      );

      // Normalize to 0-1 range (assuming most points within unit hypersphere)
      return Math.max(0, 1 - distanceFromOrigin / Math.sqrt(this.dimensions));
    }

    /**
     * Calculate the distance between two points using the manifold's metric
     * @private
     * @param {Array} p1 - First point coordinates
     * @param {Array} p2 - Second point coordinates
     * @returns {number} Distance between points
     */
    _calculateDistance(p1, p2) {
      // Get the metric tensor at the midpoint
      const midpoint = p1.map((coord, i) => (coord + p2[i]) / 2);
      const metricMatrix = this.metricTensor(midpoint);

      // Calculate the displacement vector
      const displacement = p1.map((coord, i) => coord - p2[i]);

      // Calculate the squared distance using the metric tensor
      let squaredDistance = 0;

      for (let i = 0; i < this.dimensions; i++) {
        for (let j = 0; j < this.dimensions; j++) {
          squaredDistance +=
            displacement[i] * metricMatrix[i][j] * displacement[j];
        }
      }

      return Math.sqrt(Math.abs(squaredDistance)); // Abs to handle numerical issues
    }

    /**
     * Calculate the global coherence of the manifold
     * @returns {number} Global coherence value from 0 to 1
     */
    calculateGlobalCoherence() {
      if (this.points.length === 0) {
        return 0;
      }

      // Average of all point coherence values
      let sumCoherence = 0;

      for (const coherence of this.coherenceValues.values()) {
        sumCoherence += coherence;
      }

      return sumCoherence / this.points.length;
    }

    /**
     * Get regions of high coherence in the manifold
     * @returns {Array} List of coherent regions
     */
    findCoherentRegions() {
      const regions = [];
      const visited = new Set();

      // First pass: try to identify starting points with either:
      // 1. High coherence OR
      // 2. Strong connections
      const potentialStartPoints = [];
      
      for (let i = 0; i < this.points.length; i++) {
        // Skip already visited points
        if (visited.has(i)) continue;
        
        const coherence = this.coherenceValues.get(i) || 0;
        
        // Check for strong connections
        const hasStrongConnections = Array.from(
          this.connections.get(i).entries()
        ).some(([_, conn]) => conn.strength >= 0.7);
        
        // Add points with high coherence or strong connections as potential start points
        if (coherence >= this.coherenceThreshold || hasStrongConnections) {
          potentialStartPoints.push(i);
        }
      }
      
      // Process all potential start points
      for (const startPoint of potentialStartPoints) {
        if (visited.has(startPoint)) continue;
        
        const region = this._expandRegion(startPoint, visited);
        if (region) {
          regions.push(region);
        }
      }
      
      // If no regions found, try with lower threshold for connections
      if (regions.length === 0) {
        for (let i = 0; i < this.points.length; i++) {
          if (visited.has(i)) continue;
          
          const hasAnyConnections = this.connections.get(i).size > 0;
          
          if (hasAnyConnections) {
            const region = this._expandRegion(i, visited);
            if (region) {
              regions.push(region);
            }
          } else {
            visited.add(i);
          }
        }
      }

      return regions;
    }

    /**
     * Expand a coherent region from a starting point
     * @private
     * @param {number} startIndex - Starting point index
     * @param {Set} visited - Set of already visited points
     * @returns {Object} Region information
     */
    _expandRegion(startIndex, visited) {
      const regionPoints = [];
      const queue = [startIndex];
      const regionCoherence = [];

      while (queue.length > 0) {
        const currentIndex = queue.shift();

        if (visited.has(currentIndex)) continue;
        visited.add(currentIndex);

        const coherence = this.coherenceValues.get(currentIndex) || 0;

        // Consider points with high coherence or strong connections
        const connections = this.connections.get(currentIndex);
        const hasStrongConnection = Array.from(connections.entries())
          .some(([_, conn]) => conn.strength >= 0.7);

        if (coherence >= this.coherenceThreshold || hasStrongConnection) {
          regionPoints.push(currentIndex);
          regionCoherence.push(coherence);

          // Add connected points to the queue
          for (const [connectedIndex, connection] of connections.entries()) {
            if (!visited.has(connectedIndex)) {
              if (connection.strength >= 0.5) {
                queue.push(connectedIndex);
              }
            }
          }
        }
      }

      // Only return valid regions with at least 2 points
      if (regionPoints.length < 2) {
        return null;
      }

      // Calculate region properties
      const avgCoherence =
        regionCoherence.reduce((a, b) => a + b, 0) / regionCoherence.length;

      // Calculate centroid
      const centroid = Array(this.dimensions).fill(0);
      for (const pointIndex of regionPoints) {
        const coords = this.points[pointIndex].coordinates;
        for (let i = 0; i < this.dimensions; i++) {
          centroid[i] += coords[i];
        }
      }

      for (let i = 0; i < this.dimensions; i++) {
        centroid[i] /= regionPoints.length;
      }

      return {
        points: regionPoints,
        size: regionPoints.length,
        averageCoherence: avgCoherence,
        centroid,
        mainPoint:
          regionPoints[regionCoherence.indexOf(Math.max(...regionCoherence))],
      };
    }

    /**
     * Perform spectral analysis of the manifold structure
     * Identifies principal components and key patterns
     * @returns {Object} Spectral analysis results
     */
    performSpectralAnalysis() {
      // Create adjacency matrix
      const n = this.points.length;
      const adjacency = Array(n)
        .fill()
        .map(() => Array(n).fill(0));

      for (let i = 0; i < n; i++) {
        const connections = this.connections.get(i);
        if (!connections) continue;

        for (const [j, connection] of connections.entries()) {
          adjacency[i][j] = connection.strength;
        }
      }

      // Create the Laplacian matrix (L = D - A)
      const laplacian = Array(n)
        .fill()
        .map(() => Array(n).fill(0));

      for (let i = 0; i < n; i++) {
        // Diagonal = sum of row in adjacency
        laplacian[i][i] = adjacency[i].reduce((sum, val) => sum + val, 0);

        // Off-diagonal = negative of adjacency
        for (let j = 0; j < n; j++) {
          if (i !== j) {
            laplacian[i][j] = -adjacency[i][j];
          }
        }
      }

      // [Note: A full implementation would compute eigenvalues/vectors]
      // For this demonstration, we'll use a simplified approach

      // For now, store placeholder eigen-analysis
      this.eigenvalues = Array(Math.min(n, this.spectralOrder))
        .fill()
        .map((_, i) => ({
          value: n - i,
          index: i,
        }));

      this.eigenvectors = Array(Math.min(n, this.spectralOrder))
        .fill()
        .map((_, i) => {
          const vec = Array(n).fill(0);
          vec[i] = 1; // Simplified orthogonal vectors
          return vec;
        });

      // Return analysis results
      return {
        eigenvalues: this.eigenvalues,
        eigenvectors: this.eigenvectors,
        spectralGap:
          n > 1 ? this.eigenvalues[0].value - this.eigenvalues[1].value : 0,
        spectralDimension: this._estimateSpectralDimension(),
        timestamp: Date.now(),
      };
    }

    /**
     * Estimate the spectral dimension of the manifold
     * @private
     * @returns {number} Estimated spectral dimension
     */
    _estimateSpectralDimension() {
      // A simple estimate based on eigenvalue distribution
      // In a real implementation, this would use proper spectral graph theory
      if (this.eigenvalues.length < 2) return 0;

      // Use first few eigenvalues to estimate dimension
      let dimension = 0;
      const logValues = this.eigenvalues
        .slice(0, Math.min(this.eigenvalues.length, 5))
        .map((e) => Math.log(Math.max(e.value, 1e-10)));

      // Estimate dimension from slope of log eigenvalues
      let sum = 0;
      for (let i = 1; i < logValues.length; i++) {
        sum += logValues[i - 1] - logValues[i];
      }

      dimension = Math.max(1, (2 * sum) / (logValues.length - 1));
      return dimension;
    }

    /**
     * Find a path between two points using highest coherence
     * @param {number} startIndex - Starting point index
     * @param {number} endIndex - Ending point index
     * @returns {Array|null} Path as array of indices, or null if no path exists
     */
    findCoherentPath(startIndex, endIndex) {
      if (startIndex === endIndex) return [startIndex];

      if (
        startIndex < 0 ||
        startIndex >= this.points.length ||
        endIndex < 0 ||
        endIndex >= this.points.length
      ) {
        throw new Prime.ValidationError('Point indices out of bounds');
      }

      // Modified Dijkstra's algorithm with coherence as weight
      const distances = new Map();
      const previous = new Map();
      const queue = new Set();

      // Initialize distances
      for (let i = 0; i < this.points.length; i++) {
        distances.set(i, i === startIndex ? 0 : Infinity);
        queue.add(i);
      }

      while (queue.size > 0) {
        // Find minimum distance vertex
        let minDistance = Infinity;
        let current = null;

        for (const vertex of queue) {
          if (distances.get(vertex) < minDistance) {
            minDistance = distances.get(vertex);
            current = vertex;
          }
        }

        if (current === null) break; // No path exists
        if (current === endIndex) break; // Found target

        queue.delete(current);

        // Process neighbors
        const connections = this.connections.get(current);
        if (!connections) continue;

        for (const [neighbor, connection] of connections.entries()) {
          if (!queue.has(neighbor)) continue;

          // Use inverse of coherence as distance (higher coherence = lower distance)
          const coherence = this.coherenceValues.get(neighbor) || 0;
          const edgeWeight = 1 / (0.1 + connection.strength * coherence);
          const alt = distances.get(current) + edgeWeight;

          if (alt < distances.get(neighbor)) {
            distances.set(neighbor, alt);
            previous.set(neighbor, current);
          }
        }
      }

      // Reconstruct path
      if (!previous.has(endIndex)) return null; // No path exists

      const path = [];
      let current = endIndex;

      while (current !== startIndex) {
        path.unshift(current);
        current = previous.get(current);
      }

      path.unshift(startIndex);
      return path;
    }

    /**
     * Get summary information about the manifold
     * @returns {Object} Manifold summary
     */
    getSummary() {
      const globalCoherence = this.calculateGlobalCoherence();
      const coherentRegions = this.findCoherentRegions();

      return {
        dimensions: this.dimensions,
        spectralOrder: this.spectralOrder,
        points: this.points.length,
        connections:
          Array.from(this.connections.values()).reduce(
            (total, conns) => total + conns.size,
            0,
          ) / 2, // Divide by 2 because connections are bidirectional
        globalCoherence,
        coherentRegions: coherentRegions.length,
        largestRegionSize:
          coherentRegions.length > 0
            ? Math.max(...coherentRegions.map((r) => r.size))
            : 0,
        metadata: this.metadata,
        lastUpdateTime: this.lastUpdateTime,
      };
    }
  }

  /**
   * FiberBundle - Self-referential structure for consciousness modeling
   * Links base manifold (base space) with coherence fibers (fiber space)
   */
  class FiberBundle {
    /**
     * Create a new fiber bundle for consciousness modeling
     * @param {Object} config - Configuration parameters
     * @param {CoherenceManifold} config.baseManifold - Base manifold
     * @param {number} [config.fiberDimensions=3] - Dimensions in each fiber
     * @param {number} [config.selfReferenceOrder=2] - Order of self-reference
     */
    constructor(config = {}) {
      if (!(config.baseManifold instanceof CoherenceManifold)) {
        throw new Prime.ValidationError(
          'Base manifold must be a CoherenceManifold',
        );
      }

      this.baseManifold = config.baseManifold;
      this.fiberDimensions = config.fiberDimensions || 3;
      this.selfReferenceOrder = config.selfReferenceOrder || 2;

      // Create fibers over the base manifold
      this.fibers = new Map();

      // Creating fiber at each point in the base manifold
      for (let i = 0; i < this.baseManifold.points.length; i++) {
        this._createFiber(i);
      }

      // Self-reference tracking
      this.selfReferencePoints = new Map();
      this.selfReferenceLevel = 0;

      // Metadata
      this.metadata = {
        name: config.name || 'Consciousness Fiber Bundle',
        description:
          config.description || 'A fiber bundle modeling consciousness',
        creationTime: new Date().toISOString(),
      };
    }

    /**
     * Create a fiber at a base point
     * @private
     * @param {number} baseIndex - Index of base point
     */
    _createFiber(baseIndex) {
      // Initialize an empty fiber
      this.fibers.set(baseIndex, {
        points: [],
        connections: new Map(),
        coherence: 0,
      });
    }

    /**
     * Add a point to a fiber
     * @param {number} baseIndex - Index of base point
     * @param {Array} coordinates - Coordinates in the fiber
     * @param {Object} [metadata] - Additional information
     * @returns {number} Index of new fiber point
     */
    addFiberPoint(baseIndex, coordinates, metadata = {}) {
      if (!this.fibers.has(baseIndex)) {
        throw new Prime.ValidationError(
          `No fiber exists at base index ${baseIndex}`,
        );
      }

      if (
        !Array.isArray(coordinates) ||
        coordinates.length !== this.fiberDimensions
      ) {
        throw new Prime.ValidationError(
          `Fiber coordinates must be array of length ${this.fiberDimensions}`,
        );
      }

      const fiber = this.fibers.get(baseIndex);
      const fiberPointIndex = fiber.points.length;

      fiber.points.push({
        coordinates: [...coordinates],
        metadata: { ...metadata, addedAt: Date.now() },
      });

      // Initialize connections for this fiber point
      fiber.connections.set(fiberPointIndex, new Set());

      // Update fiber coherence
      this._updateFiberCoherence(baseIndex);

      return fiberPointIndex;
    }

    /**
     * Connect two points within the same fiber
     * @param {number} baseIndex - Base point index
     * @param {number} fiberIndex1 - First fiber point index
     * @param {number} fiberIndex2 - Second fiber point index
     */
    connectFiberPoints(baseIndex, fiberIndex1, fiberIndex2) {
      if (!this.fibers.has(baseIndex)) {
        throw new Prime.ValidationError(
          `No fiber exists at base index ${baseIndex}`,
        );
      }

      const fiber = this.fibers.get(baseIndex);

      if (fiberIndex1 === fiberIndex2) {
        throw new Prime.ValidationError(
          'Cannot connect a fiber point to itself',
        );
      }

      if (
        fiberIndex1 < 0 ||
        fiberIndex1 >= fiber.points.length ||
        fiberIndex2 < 0 ||
        fiberIndex2 >= fiber.points.length
      ) {
        throw new Prime.ValidationError('Fiber point indices out of bounds');
      }

      // Add bidirectional connections
      fiber.connections.get(fiberIndex1).add(fiberIndex2);
      fiber.connections.get(fiberIndex2).add(fiberIndex1);

      // Update fiber coherence
      this._updateFiberCoherence(baseIndex);
    }

    /**
     * Create a self-reference in the bundle
     * @param {number} baseIndex - Base point index
     * @param {number} fiberIndex - Fiber point index
     * @param {number} referenceLevel - Level of self-reference (1 = first-order, etc.)
     */
    createSelfReference(baseIndex, fiberIndex, referenceLevel = 1) {
      if (!this.fibers.has(baseIndex)) {
        throw new Prime.ValidationError(
          `No fiber exists at base index ${baseIndex}`,
        );
      }

      const fiber = this.fibers.get(baseIndex);

      if (fiberIndex < 0 || fiberIndex >= fiber.points.length) {
        throw new Prime.ValidationError('Fiber point index out of bounds');
      }

      if (referenceLevel < 1 || referenceLevel > this.selfReferenceOrder) {
        throw new Prime.ValidationError(
          `Reference level must be between 1 and ${this.selfReferenceOrder}`,
        );
      }

      // Store self-reference at the specified level
      if (!this.selfReferencePoints.has(referenceLevel)) {
        this.selfReferencePoints.set(referenceLevel, new Map());
      }

      const levelMap = this.selfReferencePoints.get(referenceLevel);

      if (!levelMap.has(baseIndex)) {
        levelMap.set(baseIndex, new Set());
      }

      levelMap.get(baseIndex).add(fiberIndex);

      // Update self-reference level
      this.selfReferenceLevel = Math.max(
        this.selfReferenceLevel,
        this._calculateEffectiveSelfReferenceLevel(),
      );
    }

    /**
     * Calculate effective self-reference level of the bundle
     * @private
     * @returns {number} Effective self-reference level
     */
    _calculateEffectiveSelfReferenceLevel() {
      let maxLevel = 0;

      for (const [level, levelMap] of this.selfReferencePoints.entries()) {
        // Count total self-references at this level
        let selfRefCount = 0;
        for (const points of levelMap.values()) {
          selfRefCount += points.size;
        }

        // Level is effective if it has at least one self-reference per 10 base points
        if (selfRefCount >= this.baseManifold.points.length / 10) {
          maxLevel = Math.max(maxLevel, level);
        }
      }

      return maxLevel;
    }

    /**
     * Update coherence for a specific fiber
     * @private
     * @param {number} baseIndex - Base point index
     */
    _updateFiberCoherence(baseIndex) {
      const fiber = this.fibers.get(baseIndex);

      if (fiber.points.length === 0) {
        fiber.coherence = 0;
        return;
      }

      // Calculate connectivity coherence
      const connectivitySum = 0;
      const maxPossibleConnections =
        (fiber.points.length * (fiber.points.length - 1)) / 2;

      if (maxPossibleConnections === 0) {
        fiber.coherence = 0;
        return;
      }

      let actualConnections = 0;

      for (const connections of fiber.connections.values()) {
        actualConnections += connections.size;
      }

      // Divide by 2 because connections are counted twice
      actualConnections /= 2;

      // Normalize connectivity (0-1 scale)
      const connectivity = Math.min(
        1,
        actualConnections / maxPossibleConnections,
      );

      // Calculate geometric coherence based on point distribution
      const geometricCoherence = this._calculateGeometricCoherence(fiber);

      // Combine both factors
      fiber.coherence = 0.5 * connectivity + 0.5 * geometricCoherence;
    }

    /**
     * Calculate geometric coherence of points in a fiber
     * @private
     * @param {Object} fiber - Fiber to analyze
     * @returns {number} Geometric coherence value from 0 to 1
     */
    _calculateGeometricCoherence(fiber) {
      if (fiber.points.length < 2) return 0;

      // Calculate centroid
      const centroid = Array(this.fiberDimensions).fill(0);

      for (const point of fiber.points) {
        for (let i = 0; i < this.fiberDimensions; i++) {
          centroid[i] += point.coordinates[i];
        }
      }

      for (let i = 0; i < this.fiberDimensions; i++) {
        centroid[i] /= fiber.points.length;
      }

      // Calculate average distance from centroid
      let totalDistance = 0;

      for (const point of fiber.points) {
        let distance = 0;
        for (let i = 0; i < this.fiberDimensions; i++) {
          distance += Math.pow(point.coordinates[i] - centroid[i], 2);
        }
        totalDistance += Math.sqrt(distance);
      }

      const avgDistance = totalDistance / fiber.points.length;

      // Normalize by expected distance in uniform distribution
      // For unit cube, expected average distance is ~0.5*sqrt(dimensions)
      const expectedDistance = 0.5 * Math.sqrt(this.fiberDimensions);

      // Lower average distance means higher coherence
      return Math.max(0, 1 - avgDistance / expectedDistance);
    }

    /**
     * Calculate global bundle coherence
     * @returns {number} Global bundle coherence from 0 to 1
     */
    calculateBundleCoherence() {
      // Base manifold coherence
      const baseCoherence = this.baseManifold.calculateGlobalCoherence();

      // Average fiber coherence
      let totalFiberCoherence = 0;
      let fiberCount = 0;

      for (const fiber of this.fibers.values()) {
        if (fiber.points.length > 0) {
          totalFiberCoherence += fiber.coherence;
          fiberCount++;
        }
      }

      const avgFiberCoherence =
        fiberCount > 0 ? totalFiberCoherence / fiberCount : 0;

      // Self-reference coherence
      const selfRefCoherence =
        this.selfReferenceLevel / this.selfReferenceOrder;

      // Combine all factors (weighted sum)
      return (
        0.4 * baseCoherence + 0.4 * avgFiberCoherence + 0.2 * selfRefCoherence
      );
    }

    /**
     * Get consciessness state evaluation
     * Measures the bundle's ability to model consciousness
     * @returns {Object} Consciousness evaluation results
     */
    evaluateConsciousnessState() {
      const bundleCoherence = this.calculateBundleCoherence();

      // Calculate integration (connectedness across base and fibers)
      const integration = this._calculateIntegration();

      // Calculate differentiation (distinct states/regions)
      const differentiation = this._calculateDifferentiation();

      // Calculate self-reference capability
      const selfReferenceCapability =
        this.selfReferenceLevel / this.selfReferenceOrder;

      // Integrated Information Φ (simplified approximation)
      // In a full implementation, this would use proper IIT calculations
      const phi = integration * differentiation * bundleCoherence;

      // Consciousness requires both integration and differentiation,
      // plus coherence and self-reference
      const consciousnessScore = Math.pow(
        bundleCoherence *
          integration *
          differentiation *
          (0.5 + 0.5 * selfReferenceCapability),
        1 / 4,
      );

      return {
        bundleCoherence,
        integration,
        differentiation,
        selfReferenceLevel: this.selfReferenceLevel,
        selfReferenceCapability,
        phi,
        consciousnessScore,
        interpretation: this._interpretConsciousnessScore(consciousnessScore),
        timestamp: Date.now(),
      };
    }

    /**
     * Calculate integration value of the bundle
     * @private
     * @returns {number} Integration value from 0 to 1
     */
    _calculateIntegration() {
      // Count connections in base manifold
      let baseConnections = 0;
      for (const connections of this.baseManifold.connections.values()) {
        baseConnections += connections.size;
      }

      // Count all possible base connections
      const basePoints = this.baseManifold.points.length;
      const maxBaseConnections = basePoints * (basePoints - 1);

      // Base connectivity ratio
      const baseConnectivity =
        maxBaseConnections > 0 ? baseConnections / maxBaseConnections : 0;

      // Average fiber connectivity
      let totalFiberConnectivity = 0;
      let fiberCount = 0;

      for (const fiber of this.fibers.values()) {
        if (fiber.points.length > 1) {
          let fiberConnections = 0;
          for (const connections of fiber.connections.values()) {
            fiberConnections += connections.size;
          }

          const maxFiberConnections =
            fiber.points.length * (fiber.points.length - 1);
          const fiberConnectivity = fiberConnections / maxFiberConnections;

          totalFiberConnectivity += fiberConnectivity;
          fiberCount++;
        }
      }

      const avgFiberConnectivity =
        fiberCount > 0 ? totalFiberConnectivity / fiberCount : 0;

      // Combined integration measure
      return 0.6 * baseConnectivity + 0.4 * avgFiberConnectivity;
    }

    /**
     * Calculate differentiation value of the bundle
     * @private
     * @returns {number} Differentiation value from 0 to 1
     */
    _calculateDifferentiation() {
      // Count distinct regions in base manifold
      const baseRegions = this.baseManifold.findCoherentRegions();

      // Normalized by expected maximum regions (estimate as 20% of points)
      const expectedMaxRegions = Math.max(
        1,
        Math.ceil(this.baseManifold.points.length * 0.2),
      );
      const baseRegionRatio = Math.min(
        1,
        baseRegions.length / expectedMaxRegions,
      );

      // Calculate average fiber point spread
      let totalSpread = 0;
      let fiberCount = 0;

      for (const fiber of this.fibers.values()) {
        if (fiber.points.length > 1) {
          // Find maximum distance between any two points in the fiber
          let maxDistance = 0;

          for (let i = 0; i < fiber.points.length; i++) {
            for (let j = i + 1; j < fiber.points.length; j++) {
              const p1 = fiber.points[i].coordinates;
              const p2 = fiber.points[j].coordinates;

              let distance = 0;
              for (let d = 0; d < this.fiberDimensions; d++) {
                distance += Math.pow(p1[d] - p2[d], 2);
              }
              distance = Math.sqrt(distance);

              maxDistance = Math.max(maxDistance, distance);
            }
          }

          // Normalize by expected maximum distance in a unit hypercube
          const expectedMaxDistance = Math.sqrt(this.fiberDimensions);
          const normalizedSpread = Math.min(
            1,
            maxDistance / expectedMaxDistance,
          );

          totalSpread += normalizedSpread;
          fiberCount++;
        }
      }

      const avgFiberSpread = fiberCount > 0 ? totalSpread / fiberCount : 0;

      // Combined differentiation measure
      return 0.7 * baseRegionRatio + 0.3 * avgFiberSpread;
    }

    /**
     * Interpret consciousness score with qualitative description
     * @private
     * @param {number} score - Consciousness score from 0 to 1
     * @returns {string} Qualitative interpretation
     */
    _interpretConsciousnessScore(score) {
      if (score < 0.2) {
        return 'Minimal consciousness properties';
      } else if (score < 0.4) {
        return 'Emerging consciousness-like patterns';
      } else if (score < 0.6) {
        return 'Moderate consciousness capacity';
      } else if (score < 0.8) {
        return 'Strong consciousness-like organization';
      } else {
        return 'High-level consciousness properties';
      }
    }

    /**
     * Get summary information about the fiber bundle
     * @returns {Object} Bundle summary
     */
    getSummary() {
      const consciousnessState = this.evaluateConsciousnessState();

      // Count total fiber points
      let totalFiberPoints = 0;
      for (const fiber of this.fibers.values()) {
        totalFiberPoints += fiber.points.length;
      }

      return {
        baseManifold: {
          dimensions: this.baseManifold.dimensions,
          points: this.baseManifold.points.length,
          coherence: this.baseManifold.calculateGlobalCoherence(),
        },
        fiber: {
          dimensions: this.fiberDimensions,
          totalPoints: totalFiberPoints,
          avgPointsPerFiber:
            this.baseManifold.points.length > 0
              ? totalFiberPoints / this.baseManifold.points.length
              : 0,
        },
        selfReference: {
          order: this.selfReferenceOrder,
          level: this.selfReferenceLevel,
          capacity: consciousnessState.selfReferenceCapability,
        },
        consciousness: {
          score: consciousnessState.consciousnessScore,
          interpretation: consciousnessState.interpretation,
          phi: consciousnessState.phi,
        },
        metadata: this.metadata,
      };
    }
  }

  // Add classes to Prime.Consciousness.Models namespace
  Prime.Consciousness = Prime.Consciousness || {};
  Prime.Consciousness.Models = {
    CoherenceManifold,
    FiberBundle,
  };
})();

// Export the enhanced Prime object
module.exports = Prime;
