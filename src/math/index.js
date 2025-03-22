/**
 * PrimeOS JavaScript Library - Math Index
 * Exports all math modules with support for tree-shaking
 */

// Import the Prime object from core
const Prime = require("../core");

// Create the Math namespace if it doesn't exist
Prime.Math = Prime.Math || {};

// Import core modules (always loaded)
require("./vector-core");
require("./matrix-core");

/**
 * Lazy-load modules only when needed
 * This allows for tree-shaking and reduces memory footprint
 */
const lazyLoadModules = {
  // Vector modules
  VectorAdvanced: "./vector-advanced",
  VectorValidation: "./vector-validation",
  
  // Matrix modules
  MatrixAdvanced: "./matrix-advanced",
  MatrixValidation: "./matrix-validation",
  
  // Facade modules (provide backward compatibility)
  Vector: "./vector",
  Matrix: "./matrix",
  
  // Other math modules
  Clifford: "./clifford"
  
  // Future modules
  // Lie: "./lie",
  // Numerical: "./numerical", 
  // Spectral: "./spectral"
};

// Create getters for lazy loading
Object.keys(lazyLoadModules).forEach(moduleName => {
  if (!Prime.Math[moduleName]) {
    Object.defineProperty(Prime.Math, moduleName, {
      get: function() {
        // Load the module on first access
        require(lazyLoadModules[moduleName]);
        
        // Replace this getter with the actual module
        // This ensures the module is only loaded once
        return Prime.Math[moduleName];
      },
      configurable: true
    });
  }
});

/**
 * Helper function to load specific modules
 * @param {Array<string>} modules - Array of module names to load
 */
Prime.Math.loadModules = function(modules) {
  if (!Array.isArray(modules)) {
    throw new Prime.ValidationError("Modules must be provided as an array");
  }
  
  modules.forEach(moduleName => {
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
Prime.Math.loadAll = function() {
  Object.values(lazyLoadModules).forEach(modulePath => {
    require(modulePath);
  });
};

// For backward compatibility, load the facade modules
// These provide the original API but delegate to the specialized modules
require("./vector");
require("./matrix");
require("./clifford");

// Export the enhanced Prime object
module.exports = Prime;