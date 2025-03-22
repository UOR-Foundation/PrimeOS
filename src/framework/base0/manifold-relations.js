/**
 * PrimeOS JavaScript Library - Framework
 * Base 0: Manifold Relations
 * Code for establishing and managing relationships between manifolds
 */

// Import core
const Prime = require("../../core.js");
const { Manifold } = require("./manifold.js");

/**
 * ManifoldRelations - Utilities for working with relationships between manifolds
 */
const ManifoldRelations = {
  /**
   * Connect two manifolds with a labeled relation
   * @param {Manifold} source - Source manifold
   * @param {Manifold} target - Target manifold
   * @param {string} relationType - Type of relation
   * @param {Object} [metadata={}] - Additional relation metadata
   * @returns {Object} Relation information
   */
  connect: function(source, target, relationType, metadata = {}) {
    if (!(source instanceof Manifold) || !(target instanceof Manifold)) {
      throw new Prime.ValidationError("Source and target must be manifolds");
    }

    // Create the relation
    const relation = {
      type: relationType,
      sourceId: source.getId(),
      targetId: target.getId(),
      metadata: metadata || {},
      established: new Date().toISOString()
    };

    // Add relation to source manifold
    source.relateTo(target, relationType, metadata);

    return relation;
  },

  /**
   * Create a bidirectional relationship between manifolds
   * @param {Manifold} manifoldA - First manifold
   * @param {Manifold} manifoldB - Second manifold
   * @param {string} relationType - Type of relation
   * @param {Object} [metadata={}] - Additional relation metadata
   * @returns {Array} Array of relation information (both directions)
   */
  createBidirectionalRelation: function(manifoldA, manifoldB, relationType, metadata = {}) {
    if (!(manifoldA instanceof Manifold) || !(manifoldB instanceof Manifold)) {
      throw new Prime.ValidationError("Both arguments must be manifolds");
    }

    // Create relations in both directions
    const relationAtoB = this.connect(manifoldA, manifoldB, relationType, metadata);
    const relationBtoA = this.connect(manifoldB, manifoldA, relationType, metadata);

    return [relationAtoB, relationBtoA];
  },

  /**
   * Find all manifolds related to the source by a specific relation type
   * @param {Manifold} source - Source manifold
   * @param {string} relationType - Type of relation to find
   * @returns {Array} Related manifolds
   */
  findRelatedManifolds: function(source, relationType) {
    if (!(source instanceof Manifold)) {
      throw new Prime.ValidationError("Source must be a manifold");
    }

    // Use the manifold's internal relation tracking
    return source.getRelatedManifolds(relationType);
  },

  /**
   * Create a relation graph between manifolds
   * @param {Array<Manifold>} manifolds - Array of manifolds to analyze
   * @param {Object} options - Options for graph creation
   * @returns {Object} Relation graph
   */
  createRelationGraph: function(manifolds, options = {}) {
    const graph = {
      nodes: [],
      edges: [],
      metadata: {
        createdAt: new Date().toISOString(),
        nodeCount: 0,
        edgeCount: 0
      }
    };

    // Create a map for quick manifold lookup by ID
    const manifoldMap = new Map();
    for (const manifold of manifolds) {
      if (!(manifold instanceof Manifold)) {
        throw new Prime.ValidationError("All items must be manifolds");
      }

      manifoldMap.set(manifold.getId(), manifold);
    }

    // Process each manifold to create nodes and edges
    for (const manifold of manifolds) {
      // Add node for this manifold
      graph.nodes.push({
        id: manifold.getId(),
        type: "manifold",
        label: manifold.getMeta().name || manifold.getId(),
        properties: {
          type: manifold.getType(),
          depth: manifold.getDepth(),
          coherence: manifold.getCoherenceScore(),
          spaces: manifold.getSpaces()
        }
      });

      // Collect relations as edges
      const relations = manifold.getRelatedManifolds();
      for (const relation of relations) {
        // Only add relations to manifolds in our list
        if (manifoldMap.has(relation.manifold.getId())) {
          graph.edges.push({
            source: manifold.getId(),
            target: relation.manifold.getId(),
            type: relation.type,
            metadata: relation.metadata || {}
          });
        }
      }
    }

    // Update metadata
    graph.metadata.nodeCount = graph.nodes.length;
    graph.metadata.edgeCount = graph.edges.length;

    return graph;
  },

  /**
   * Find paths between two manifolds
   * @param {Manifold} source - Source manifold
   * @param {Manifold} target - Target manifold
   * @param {Object} options - Options for path finding
   * @returns {Array} Paths between manifolds
   */
  findPaths: function(source, target, options = {}) {
    if (!(source instanceof Manifold) || !(target instanceof Manifold)) {
      throw new Prime.ValidationError("Source and target must be manifolds");
    }

    const maxDepth = options.maxDepth || 5;
    const relationTypes = options.relationTypes || null;

    // Use breadth-first search to find paths
    const visited = new Set();
    const queue = [{
      manifold: source,
      path: [],
      relationPath: []
    }];
    
    const result = [];

    while (queue.length > 0) {
      const { manifold, path, relationPath } = queue.shift();
      const manifoldId = manifold.getId();

      // If we found the target, add the path to results
      if (manifoldId === target.getId()) {
        result.push({
          path: [...path, manifoldId],
          relationPath,
          length: path.length
        });
        continue;
      }

      // Skip if we've visited this manifold already or exceeded max depth
      if (visited.has(manifoldId) || path.length >= maxDepth) {
        continue;
      }

      visited.add(manifoldId);

      // Get related manifolds
      const relations = manifold.getRelatedManifolds();
      
      for (const relation of relations) {
        // Skip if not requested relation type
        if (relationTypes && !relationTypes.includes(relation.type)) {
          continue;
        }

        // Add to queue for BFS
        queue.push({
          manifold: relation.manifold,
          path: [...path, manifoldId],
          relationPath: [...relationPath, relation.type]
        });
      }
    }

    return result;
  },

  /**
   * Calculate relation density between manifolds
   * @param {Array<Manifold>} manifolds - Array of manifolds to analyze
   * @returns {Object} Relation density statistics
   */
  calculateRelationDensity: function(manifolds) {
    if (!Array.isArray(manifolds) || manifolds.length === 0) {
      throw new Prime.ValidationError("Manifolds must be a non-empty array");
    }

    const n = manifolds.length;
    const maxPossibleRelations = n * (n - 1); // Directed relations
    let actualRelations = 0;
    
    // Count actual relations
    for (const manifold of manifolds) {
      actualRelations += manifold.getRelatedManifolds().length;
    }

    // Calculate density
    const density = maxPossibleRelations > 0 
      ? actualRelations / maxPossibleRelations 
      : 0;

    // Categorize relation types
    const relationTypes = {};
    for (const manifold of manifolds) {
      for (const relation of manifold.getRelatedManifolds()) {
        relationTypes[relation.type] = (relationTypes[relation.type] || 0) + 1;
      }
    }

    return {
      manifoldCount: n,
      possibleRelations: maxPossibleRelations,
      actualRelations,
      density,
      relationTypes
    };
  }
};

module.exports = ManifoldRelations;