/**
 * PrimeOS JavaScript Library - Math Index
 * Exports all math modules with support for tree-shaking
 */

// Import the Prime object from core
const Prime = require('../core');

// Create the Math namespace if it doesn't exist
Prime.Math = Prime.Math || {};

// Import core modules (always loaded)
require('./vector-core');
require('./matrix-core');

// Pre-initialize Vector and Matrix objects to prevent circular dependency warnings
Prime.Math.Vector = {};
Prime.Math.Matrix = {};

/**
 * Lazy-load modules only when needed
 * This allows for tree-shaking and reduces memory footprint
 */
const lazyLoadModules = {
  // Vector modules
  VectorAdvanced: './vector-advanced',
  VectorValidation: './vector-validation',

  // Matrix modules
  MatrixAdvanced: './matrix-advanced',
  MatrixValidation: './matrix-validation',

  // Facade modules (provide backward compatibility)
  Vector: './vector',
  Matrix: './matrix',

  // Other math modules
  Clifford: './clifford',

  // Future modules (now implemented)
  Lie: './lie',
  Numerical: './numerical',
  Spectral: './spectral',
};

// Create getters for lazy loading - with improved circular dependency handling
Object.keys(lazyLoadModules).forEach((moduleName) => {
  if (
    !Prime.Math[moduleName] ||
    moduleName === 'Vector' ||
    moduleName === 'Matrix'
  ) {
    let moduleLoaded = false;
    let moduleExports = null;

    // Create a placeholder that will be returned before the module is fully loaded
    const tempPlaceholder = Prime.Math[moduleName] || {};

    // Store placeholder before defining property to avoid recursive gets
    const placeholderMap = new Map();
    placeholderMap.set(moduleName, tempPlaceholder);

    Object.defineProperty(Prime.Math, moduleName, {
      get: function () {
        if (!moduleLoaded) {
          try {
            // Set the loaded flag before requiring to break potential cycles
            moduleLoaded = true;

            // Load the module
            moduleExports = require(lazyLoadModules[moduleName]);

            // If module exports the enhanced Prime object, return the module's version if it exists
            if (moduleExports === Prime) {
              if (
                typeof Prime.Math[moduleName] === 'object' &&
                Prime.Math[moduleName] !== null &&
                Prime.Math[moduleName] !== placeholderMap.get(moduleName) &&
                Object.keys(Prime.Math[moduleName]).length > 0
              ) {
                return Prime.Math[moduleName];
              }
              return placeholderMap.get(moduleName);
            }

            // Otherwise store the module exports for future gets
            placeholderMap.set(moduleName, moduleExports);
          } catch (error) {
            console.error(`Error loading module ${moduleName}:`, error.message);
          }
        }

        return placeholderMap.get(moduleName);
      },
      configurable: true,
    });
  }
});

/**
 * Helper function to load specific modules
 * @param {Array<string>} modules - Array of module names to load
 */
Prime.Math.loadModules = function (modules) {
  if (!Array.isArray(modules)) {
    throw new Prime.ValidationError('Modules must be provided as an array');
  }

  modules.forEach((moduleName) => {
    if (lazyLoadModules[moduleName]) {
      require(lazyLoadModules[moduleName]);
    } else {
      console.warn(`Unknown module: ${moduleName}`);
    }
  });
};

/**
 * Load all math modules at once
 * Use this for backward compatibility when tree-shaking is not needed
 */
Prime.Math.loadAll = function () {
  Object.values(lazyLoadModules).forEach((modulePath) => {
    require(modulePath);
  });
};

// For backward compatibility, load the facade modules
// These provide the original API but delegate to the specialized modules
require('./vector');
require('./matrix');
require('./clifford');

// Ensure matrix operations are loaded - needed for matrix-extreme-values-tests.js
// These are required to initialize the MatrixAdvanced module
require('./matrix-advanced');
require('./matrix-validation');

// Manually connect methods to Matrix for extreme value tests
const MatrixAdvanced = Prime.Math.MatrixAdvanced;
const MatrixCore = Prime.Math.MatrixCore;

// Advanced matrix operations
Prime.Math.Matrix.luDecomposition = function(matrix) {
  return MatrixAdvanced.luDecomposition(matrix);
};
Prime.Math.Matrix.qrDecomposition = function(matrix) {
  return MatrixAdvanced.qrDecomposition(matrix);
};
Prime.Math.Matrix.eigenvalues = function(matrix, options) {
  return MatrixAdvanced.eigenvalues(matrix, options);
};
Prime.Math.Matrix.choleskyDecomposition = function(matrix) {
  return MatrixAdvanced.choleskyDecomposition(matrix);
};

// Core matrix operations
Prime.Math.Matrix.multiply = function(a, b, result) {
  return MatrixCore.multiply(a, b, result);
};
Prime.Math.Matrix.transpose = function(matrix, result) {
  return MatrixCore.transpose(matrix, result);
};
Prime.Math.Matrix.create = function(rows, cols, initialValue = 0, options = {}) {
  return MatrixCore.create(rows, cols, initialValue, options);
};
Prime.Math.Matrix.dimensions = function(matrix) {
  return MatrixCore.dimensions(matrix);
};

// Export the enhanced Prime object
module.exports = Prime;
