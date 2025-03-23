/**
 * PrimeOS JavaScript Library - Framework
 * Base 0: Manifold Operations
 *
 * This file serves as a unified entry point for all manifold operations,
 * importing and re-exporting functionality from specialized modules.
 */

// Import Prime for namespace
const Prime = require('../../core.js');

// Ensure Prime.Framework.Base0 namespace exists
Prime.Framework = Prime.Framework || {};
Prime.Framework.Base0 = Prime.Framework.Base0 || {};

// Import specialized modules with proper error handling to avoid crashes on circular dependencies
function safeRequire(modulePath) {
  try {
    return require(modulePath);
  } catch (error) {
    // Create an empty placeholder to break the dependency cycle
    return {};
  }
}

const GeodesicOperations = safeRequire('./geodesic-operations.js');
const TangentSpaceOperations = safeRequire('./tangent-space.js');
const ManifoldVisualization = safeRequire('./manifold-visualization.js');
const ManifoldTransformations = safeRequire('./manifold-transformations.js');
const ManifoldRelations = safeRequire('./manifold-relations.js');

/**
 * ManifoldOperations - Combined operations for manifolds
 * Imports and re-exports functionality from specialized modules for backward compatibility
 */
const ManifoldOperations = {
  // Geodesic Operations
  computeGeodesic:
    GeodesicOperations.computeGeodesic ||
    function () {
      console.warn('GeodesicOperations not fully loaded');
      return {};
    },
  interpolate:
    GeodesicOperations.interpolate ||
    function () {
      console.warn('GeodesicOperations not fully loaded');
      return {};
    },
  parallelTransport:
    GeodesicOperations.parallelTransport ||
    function () {
      console.warn('GeodesicOperations not fully loaded');
      return {};
    },
  sectionalCurvature:
    GeodesicOperations.sectionalCurvature ||
    function () {
      console.warn('GeodesicOperations not fully loaded');
      return {};
    },

  // Tangent Space Operations
  tangentSpace:
    TangentSpaceOperations.calculateTangentSpace ||
    function () {
      console.warn('TangentSpaceOperations not fully loaded');
      return {};
    },
  calculateTangentSpace:
    TangentSpaceOperations.calculateTangentSpace ||
    function () {
      console.warn('TangentSpaceOperations not fully loaded');
      return {};
    },
  calculateCurvature:
    TangentSpaceOperations.calculateCurvature ||
    function () {
      console.warn('TangentSpaceOperations not fully loaded');
      return {};
    },
  projectToTangentSpace:
    TangentSpaceOperations.projectToTangentSpace ||
    function () {
      console.warn('TangentSpaceOperations not fully loaded');
      return {};
    },
  isTangentVector:
    TangentSpaceOperations.isTangentVector ||
    function () {
      console.warn('TangentSpaceOperations not fully loaded');
      return false;
    },
  calculateMetricTensor:
    TangentSpaceOperations.calculateMetricTensor ||
    function () {
      console.warn('TangentSpaceOperations not fully loaded');
      return {};
    },

  // Visualization Operations
  createVisualization:
    ManifoldVisualization.createVisualization ||
    function () {
      console.warn('ManifoldVisualization not fully loaded');
      return {};
    },
  createMultiManifoldVisualization:
    ManifoldVisualization.createMultiManifoldVisualization ||
    function () {
      console.warn('ManifoldVisualization not fully loaded');
      return {};
    },
  createHeatmap:
    ManifoldVisualization.createHeatmap ||
    function () {
      console.warn('ManifoldVisualization not fully loaded');
      return {};
    },

  // Transformation Operations
  alignWith:
    ManifoldTransformations.alignWith ||
    function () {
      console.warn('ManifoldTransformations not fully loaded');
      return {};
    },
  scale:
    ManifoldTransformations.scale ||
    function () {
      console.warn('ManifoldTransformations not fully loaded');
      return {};
    },
  rotate:
    ManifoldTransformations.rotate ||
    function () {
      console.warn('ManifoldTransformations not fully loaded');
      return {};
    },
  mirror:
    ManifoldTransformations.mirror ||
    function () {
      console.warn('ManifoldTransformations not fully loaded');
      return {};
    },

  // Relation Operations
  connect:
    ManifoldRelations.connect ||
    function () {
      console.warn('ManifoldRelations not fully loaded');
      return {};
    },
  createBidirectionalRelation:
    ManifoldRelations.createBidirectionalRelation ||
    function () {
      console.warn('ManifoldRelations not fully loaded');
      return {};
    },
  findRelatedManifolds:
    ManifoldRelations.findRelatedManifolds ||
    function () {
      console.warn('ManifoldRelations not fully loaded');
      return [];
    },
  createRelationGraph:
    ManifoldRelations.createRelationGraph ||
    function () {
      console.warn('ManifoldRelations not fully loaded');
      return {};
    },
  findPaths:
    ManifoldRelations.findPaths ||
    function () {
      console.warn('ManifoldRelations not fully loaded');
      return [];
    },
  calculateRelationDensity:
    ManifoldRelations.calculateRelationDensity ||
    function () {
      console.warn('ManifoldRelations not fully loaded');
      return 0;
    },

  // Namespaced access to specialized modules (for advanced usage)
  geodesic: GeodesicOperations,
  tangent: TangentSpaceOperations,
  visualization: ManifoldVisualization,
  transformation: ManifoldTransformations,
  relations: ManifoldRelations,
};

// Add to Prime namespace with proper circular dependency handling
if (
  Object.getOwnPropertyDescriptor(
    Prime.Framework.Base0,
    'ManifoldOperations',
  ) &&
  Object.getOwnPropertyDescriptor(Prime.Framework.Base0, 'ManifoldOperations')
    .get
) {
  // Use a more careful approach to update properties that already have getters
  const descriptor = Object.getOwnPropertyDescriptor(
    Prime.Framework.Base0,
    'ManifoldOperations',
  );
  const originalGetter = descriptor.get;

  Object.defineProperty(Prime.Framework.Base0, 'ManifoldOperations', {
    get: function () {
      const result = originalGetter.call(this);
      if (!result || Object.keys(result).length === 0) {
        return ManifoldOperations;
      }
      return result;
    },
    configurable: true,
  });
} else {
  // Direct assignment if no getter exists
  Prime.Framework.Base0.ManifoldOperations = ManifoldOperations;
}

// Export both ManifoldOperations and the enhanced Prime object
module.exports = ManifoldOperations;
