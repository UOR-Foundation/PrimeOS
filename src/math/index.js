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
    let tempPlaceholder = {};
    
    Object.defineProperty(Prime.Math, moduleName, {
      get: function() {
        if (!moduleLoaded) {
          try {
            // Use the temporary placeholder to break circular dependencies
            // We need to avoid modifying Prime.Math[moduleName] here to prevent recursion
            
            // Set the loaded flag before requiring to break potential cycles
            moduleLoaded = true;
            
            // Load the module
            moduleExports = require(lazyLoadModules[moduleName]);
            
            // If module exports the enhanced Prime object, keep using our placeholder
            if (moduleExports === Prime) {
              // The module has successfully registered itself on Prime.Math
              return Prime.Math[moduleName] || tempPlaceholder;
            }
            
            // Otherwise, the module export becomes the module value - but only if we haven't
            // already initialized it through a circular reference
            if (Prime.Math[moduleName] === tempPlaceholder) {
              Prime.Math[moduleName] = moduleExports;
            }
          } catch (error) {
            console.error(`Error loading module ${moduleName}:`, error.message);
            // Return placeholder object as fallback to avoid breaking the application
            return tempPlaceholder;
          }
        }
        
        return Prime.Math[moduleName] || tempPlaceholder;
      },
      configurable: true
    });
    
    // Initialize with placeholder to prevent recursion
    Prime.Math[moduleName] = tempPlaceholder;
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