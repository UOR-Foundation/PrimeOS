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

// Create getters for lazy loading - with improved circular dependency handling
Object.keys(lazyLoadModules).forEach(moduleName => {
  if (!Prime.Math[moduleName]) {
    let moduleLoaded = false;
    let moduleExports = null;
    
    Object.defineProperty(Prime.Math, moduleName, {
      get: function() {
        if (!moduleLoaded) {
          try {
            // Set a temporary placeholder to break circular dependencies
            Prime.Math[moduleName] = {};
            
            // Load the module
            moduleExports = require(lazyLoadModules[moduleName]);
            moduleLoaded = true;
            
            // If module exports the enhanced Prime object, update our exports
            if (moduleExports === Prime) {
              return Prime.Math[moduleName];
            }
            
            // Otherwise, the module export becomes the module value
            Prime.Math[moduleName] = moduleExports;
          } catch (error) {
            console.error(`Error loading module ${moduleName}:`, error.message);
            // Return empty object as fallback to avoid breaking the application
            return {};
          }
        }
        
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