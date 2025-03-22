/**
 * PrimeOS JavaScript Library - Framework
 * Base 0: ManifoldSpace Implementation
 * Mathematical space that contains manifolds
 */

// Import core
const Prime = require("../../core.js");
const { Manifold } = require("./manifold.js");

/**
 * ManifoldSpace represents a mathematical space that contains manifolds
 */
class ManifoldSpace {
  /**
   * Create a new mathematical space for manifolds
   * @param {Object} config - Space configuration
   * @param {string} config.id - Space identifier
   * @param {string} config.name - Space name
   * @param {number} config.dimension - Space dimension
   * @param {Object} config.properties - Space properties
   */
  constructor(config = {}) {
    this.id =
      config.id || `space_${Date.now()}_${Math.floor(Math.random() * 10000)}`;
    this.name = config.name || "GenericSpace";
    this.dimension = config.dimension || 0;
    this.properties = config.properties || {};

    // Store manifolds in this space
    this._manifolds = new Map();

    // Track coherence of the space
    this._coherence = 1.0;

    // Connect to coherence system if available
    if (Prime.coherence && Prime.coherence.systemCoherence && typeof Prime.coherence.systemCoherence.registerSpace === 'function') {
      Prime.coherence.systemCoherence.registerSpace(this);
    }
  }

  /**
   * Add a manifold to this space
   * @param {Manifold} manifold - Manifold to add
   * @returns {ManifoldSpace} This space for chaining
   */
  addManifold(manifold) {
    if (!(manifold instanceof Manifold)) {
      throw new Prime.ValidationError("Expected a Manifold instance");
    }

    this._manifolds.set(manifold.getId(), manifold);
    manifold.addToSpace(this.id);

    // Update space coherence
    this._updateCoherence();

    return this;
  }

  /**
   * Remove a manifold from this space
   * @param {Manifold|string} manifoldOrId - Manifold or manifold ID to remove
   * @returns {ManifoldSpace} This space for chaining
   */
  removeManifold(manifoldOrId) {
    const id =
      manifoldOrId instanceof Manifold ? manifoldOrId.getId() : manifoldOrId;

    const manifold = this._manifolds.get(id);
    if (manifold) {
      this._manifolds.delete(id);
      manifold.removeFromSpace(this.id);

      // Update space coherence
      this._updateCoherence();
    }

    return this;
  }

  /**
   * Get all manifolds in this space
   * @returns {Array} Array of manifolds
   */
  getManifolds() {
    return Array.from(this._manifolds.values());
  }

  /**
   * Find manifolds by property
   * @param {string} property - Property to match
   * @param {*} value - Value to match
   * @returns {Array} Matching manifolds
   */
  findManifolds(property, value) {
    return this.getManifolds().filter((manifold) => {
      // Check in meta
      if (manifold.meta && manifold.meta[property] === value) {
        return true;
      }

      // Check in invariant
      if (manifold.invariant && manifold.invariant[property] === value) {
        return true;
      }

      // Check in variant
      if (manifold.variant && manifold.variant[property] === value) {
        return true;
      }

      return false;
    });
  }

  /**
   * Check if a manifold exists in this space
   * @param {Manifold|string} manifoldOrId - Manifold or manifold ID to check
   * @returns {boolean} True if manifold exists in space
   */
  hasManifold(manifoldOrId) {
    const id =
      manifoldOrId instanceof Manifold ? manifoldOrId.getId() : manifoldOrId;
    return this._manifolds.has(id);
  }

  /**
   * Get the coherence of the space
   * @returns {number} Coherence score (0-1)
   */
  getCoherence() {
    return this._coherence;
  }

  /**
   * Update the coherence of the space
   * @private
   */
  _updateCoherence() {
    const manifolds = this.getManifolds();

    if (manifolds.length === 0) {
      this._coherence = 1.0;
      return;
    }

    // Calculate average coherence of manifolds in this space
    let totalCoherence = 0;
    for (const manifold of manifolds) {
      totalCoherence += manifold.getCoherenceScore();
    }

    const averageCoherence = totalCoherence / manifolds.length;

    // For proper mathematical space, we'd calculate additional coherence
    // properties based on the mathematical structure
    this._coherence = averageCoherence;
  }
  
  /**
   * Find manifolds with the highest coherence
   * @param {number} limit - Maximum number to return
   * @returns {Array} Array of manifolds sorted by coherence
   */
  getMostCoherentManifolds(limit = 10) {
    const manifolds = this.getManifolds();
    
    // Sort by coherence (highest first)
    const sorted = [...manifolds].sort(
      (a, b) => b.getCoherenceScore() - a.getCoherenceScore()
    );
    
    // Return top N
    return sorted.slice(0, limit);
  }
  
  /**
   * Get statistics about this manifold space
   * @returns {Object} Space statistics
   */
  getStatistics() {
    const manifolds = this.getManifolds();
    const manifoldCount = manifolds.length;
    
    // Calculate coherence statistics
    let totalCoherence = 0;
    let minCoherence = 1.0;
    let maxCoherence = 0.0;
    
    // Count manifold types
    const typeCount = {};
    
    for (const manifold of manifolds) {
      const coherence = manifold.getCoherenceScore();
      totalCoherence += coherence;
      minCoherence = Math.min(minCoherence, coherence);
      maxCoherence = Math.max(maxCoherence, coherence);
      
      // Count by type
      const type = manifold.getType();
      typeCount[type] = (typeCount[type] || 0) + 1;
    }
    
    // Calculate relations
    const relationCount = manifolds.reduce((count, manifold) => {
      return count + manifold.getRelatedManifolds().length;
    }, 0);
    
    return {
      id: this.id,
      name: this.name,
      dimension: this.dimension,
      manifolds: {
        count: manifoldCount,
        byType: typeCount
      },
      coherence: {
        overall: this._coherence,
        average: manifoldCount > 0 ? totalCoherence / manifoldCount : 1.0,
        min: manifoldCount > 0 ? minCoherence : 1.0,
        max: manifoldCount > 0 ? maxCoherence : 1.0
      },
      relations: {
        count: relationCount,
        average: manifoldCount > 0 ? relationCount / manifoldCount : 0
      }
    };
  }
  
  /**
   * Create a composite manifold from all manifolds in this space
   * @param {Object} options - Options for composition
   * @returns {Manifold} Composite manifold
   */
  createCompositeManifold(options = {}) {
    const manifolds = this.getManifolds();
    if (manifolds.length === 0) {
      throw new Prime.InvalidOperationError("Cannot create composite from empty space");
    }
    
    // Create meta information
    const meta = {
      id: options.id || `composite_${this.id}_${Date.now()}`,
      type: "composite",
      name: options.name || `Composite of ${this.name}`,
      description: options.description || `Composite manifold created from ${manifolds.length} manifolds in ${this.name}`,
      sourceSpace: this.id,
      sourceManifolds: manifolds.map(m => m.getId())
    };
    
    // Merge invariant properties (only common properties across all manifolds)
    const invariantKeys = new Set();
    const invariantValuesMap = new Map();
    
    // First, collect all keys from all manifolds
    for (const manifold of manifolds) {
      Object.keys(manifold.getInvariant()).forEach(key => invariantKeys.add(key));
    }
    
    // Then, for each key, check if all manifolds have the same value
    for (const key of invariantKeys) {
      const values = manifolds.map(m => m.getInvariant()[key]);
      const uniqueValues = new Set(values.filter(v => v !== undefined));
      
      // If all manifolds have the same value, include it in the composite
      if (uniqueValues.size === 1) {
        invariantValuesMap.set(key, values[0]);
      }
    }
    
    // Convert to object
    const invariant = Object.fromEntries(invariantValuesMap.entries());
    
    // Create variant data from aggregating manifold values
    const variant = {
      compositeSource: "space",
      manifoldCount: manifolds.length,
      coherence: this._coherence,
      relationCount: manifolds.reduce((count, m) => count + m.getRelatedManifolds().length, 0),
      // Include aggregate values from all manifolds' variants
      aggregate: this._aggregateVariantValues(manifolds)
    };
    
    // Create the composite manifold
    const composite = new Manifold({
      meta,
      invariant,
      variant,
      depth: options.depth || Math.max(...manifolds.map(m => m.getDepth())) + 1,
      spaces: [this.id]
    });
    
    // Establish relations to all component manifolds
    for (const manifold of manifolds) {
      composite.relateTo(manifold, "composed_of");
    }
    
    return composite;
  }
  
  /**
   * Aggregate variant values from manifolds
   * @private
   * @param {Array<Manifold>} manifolds - Manifolds to aggregate
   * @returns {Object} Aggregated values
   */
  _aggregateVariantValues(manifolds) {
    // Track all numeric and array properties across all manifolds
    const numericValues = {};
    const arrayValues = {};
    
    for (const manifold of manifolds) {
      const variant = manifold.getVariant();
      
      for (const [key, value] of Object.entries(variant)) {
        if (typeof value === 'number') {
          if (!numericValues[key]) {
            numericValues[key] = [];
          }
          numericValues[key].push(value);
        } else if (Array.isArray(value) && value.every(v => typeof v === 'number')) {
          if (!arrayValues[key]) {
            arrayValues[key] = [];
          }
          arrayValues[key].push(value);
        }
      }
    }
    
    // Calculate statistics for numeric values
    const numericStats = {};
    for (const [key, values] of Object.entries(numericValues)) {
      if (values.length > 0) {
        const sum = values.reduce((a, b) => a + b, 0);
        const mean = sum / values.length;
        const sorted = [...values].sort((a, b) => a - b);
        const median = sorted[Math.floor(sorted.length / 2)];
        
        const squaredDiffs = values.map(x => Math.pow(x - mean, 2));
        const variance = squaredDiffs.reduce((a, b) => a + b, 0) / values.length;
        
        numericStats[key] = {
          count: values.length,
          min: Math.min(...values),
          max: Math.max(...values),
          mean,
          median,
          stdDev: Math.sqrt(variance)
        };
      }
    }
    
    // Calculate statistics for array values
    const arrayStats = {};
    for (const [key, arrays] of Object.entries(arrayValues)) {
      if (arrays.length > 0) {
        // Only attempt to aggregate arrays of the same length
        const firstLength = arrays[0].length;
        const sameLength = arrays.every(arr => arr.length === firstLength);
        
        if (sameLength) {
          // Calculate element-wise statistics
          const elemStats = [];
          
          for (let i = 0; i < firstLength; i++) {
            const elemValues = arrays.map(arr => arr[i]);
            const elemSum = elemValues.reduce((a, b) => a + b, 0);
            const elemMean = elemSum / elemValues.length;
            
            const elemSquaredDiffs = elemValues.map(x => Math.pow(x - elemMean, 2));
            const elemVariance = elemSquaredDiffs.reduce((a, b) => a + b, 0) / elemValues.length;
            
            elemStats.push({
              min: Math.min(...elemValues),
              max: Math.max(...elemValues),
              mean: elemMean,
              stdDev: Math.sqrt(elemVariance)
            });
          }
          
          arrayStats[key] = {
            count: arrays.length,
            length: firstLength,
            elements: elemStats
          };
        } else {
          // Just count arrays of different lengths
          arrayStats[key] = {
            count: arrays.length,
            variableLength: true
          };
        }
      }
    }
    
    return {
      numeric: numericStats,
      arrays: arrayStats
    };
  }
}

module.exports = { ManifoldSpace };