/**
 * PrimeOS JavaScript Library - Framework
 * Base 0: Manifold Operations
 * 
 * This file serves as a unified entry point for all manifold operations,
 * importing and re-exporting functionality from specialized modules.
 */

// Import specialized modules
const GeodesicOperations = require('./geodesic-operations.js');
const TangentSpaceOperations = require('./tangent-space.js');
const ManifoldVisualization = require('./manifold-visualization.js');
const ManifoldTransformations = require('./manifold-transformations.js');
const ManifoldRelations = require('./manifold-relations.js');

/**
 * ManifoldOperations - Combined operations for manifolds
 * Imports and re-exports functionality from specialized modules for backward compatibility
 */
const ManifoldOperations = {
  // Geodesic Operations
  computeGeodesic: GeodesicOperations.computeGeodesic,
  interpolate: GeodesicOperations.interpolate,
  parallelTransport: GeodesicOperations.parallelTransport,
  sectionalCurvature: GeodesicOperations.sectionalCurvature,
  
  // Tangent Space Operations
  tangentSpace: TangentSpaceOperations.calculateTangentSpace,
  calculateTangentSpace: TangentSpaceOperations.calculateTangentSpace,
  calculateCurvature: TangentSpaceOperations.calculateCurvature,
  projectToTangentSpace: TangentSpaceOperations.projectToTangentSpace,
  isTangentVector: TangentSpaceOperations.isTangentVector,
  calculateMetricTensor: TangentSpaceOperations.calculateMetricTensor,
  
  // Visualization Operations
  createVisualization: ManifoldVisualization.createVisualization,
  createMultiManifoldVisualization: ManifoldVisualization.createMultiManifoldVisualization,
  createHeatmap: ManifoldVisualization.createHeatmap,
  
  // Transformation Operations
  alignWith: ManifoldTransformations.alignWith,
  scale: ManifoldTransformations.scale,
  rotate: ManifoldTransformations.rotate,
  mirror: ManifoldTransformations.mirror,
  
  // Relation Operations
  connect: ManifoldRelations.connect,
  createBidirectionalRelation: ManifoldRelations.createBidirectionalRelation,
  findRelatedManifolds: ManifoldRelations.findRelatedManifolds,
  createRelationGraph: ManifoldRelations.createRelationGraph,
  findPaths: ManifoldRelations.findPaths,
  calculateRelationDensity: ManifoldRelations.calculateRelationDensity,
  
  // Namespaced access to specialized modules (for advanced usage)
  geodesic: GeodesicOperations,
  tangent: TangentSpaceOperations,
  visualization: ManifoldVisualization,
  transformation: ManifoldTransformations,
  relations: ManifoldRelations
};

module.exports = ManifoldOperations;