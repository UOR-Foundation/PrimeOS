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
Prime.Math.MatrixErrorHandling = {};

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
  MatrixErrorHandling: './matrix-error-handling',

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
require('./matrix-error-handling');

// Ensure modules are loaded
const MatrixAdvanced = Prime.Math.MatrixAdvanced;
const MatrixCore = Prime.Math.MatrixCore;
const MatrixValidation = Prime.Math.MatrixValidation;

// Direct implementations with basic error handling

// Advanced matrix operations
Prime.Math.Matrix.determinant = function(matrix) {
  try {
    // Basic validation
    if (!MatrixValidation.isMatrix(matrix)) {
      throw new Prime.ValidationError('Matrix must be valid');
    }
    if (MatrixValidation.hasInvalidValues(matrix)) {
      throw new Prime.ValidationError('Matrix contains NaN or Infinity values');
    }
    if (!MatrixValidation.isSquare(matrix)) {
      throw new Prime.ValidationError('Matrix must be square');
    }
    
    // Find extreme values for scaling
    let maxAbs = 0;
    let minNonZero = Infinity;
    for (let i = 0; i < matrix.length; i++) {
      for (let j = 0; j < matrix[i].length; j++) {
        const absVal = Math.abs(matrix[i][j]);
        if (absVal > maxAbs) maxAbs = absVal;
        if (absVal > 0 && absVal < minNonZero) minNonZero = absVal;
      }
    }
    
    // Apply scaling if needed
    let scaledMatrix = matrix;
    let scaleFactor = 1;
    if (maxAbs > 1e100 || (minNonZero < 1e-100 && minNonZero > 0)) {
      const scale = maxAbs > 1e100 ? 1e-100 : 1e100;
      scaleFactor = scale;
      scaledMatrix = MatrixCore.scale(matrix, scale);
    }
    
    // Calculate determinant
    const det = MatrixAdvanced.determinant(scaledMatrix);
    
    // Adjust for scaling
    const n = matrix.length;
    return det * Math.pow(1/scaleFactor, n);
  } catch (error) {
    throw error;
  }
};

Prime.Math.Matrix.inverse = function(matrix) {
  try {
    // Basic validation
    if (!MatrixValidation.isMatrix(matrix)) {
      throw new Prime.ValidationError('Matrix must be valid');
    }
    if (MatrixValidation.hasInvalidValues(matrix)) {
      throw new Prime.ValidationError('Matrix contains NaN or Infinity values');
    }
    if (!MatrixValidation.isSquare(matrix)) {
      throw new Prime.ValidationError('Matrix must be square');
    }
    
    // Check if matrix is nearly singular using proper numerical approach
    if (MatrixValidation.isNearlySingular(matrix)) {
      throw new Prime.MathematicalError('Matrix is singular or nearly singular');
    }
    
    // Try regular inverse
    return MatrixAdvanced.inverse(matrix);
  } catch (error) {
    // Already checked for basic validation, so this might be a singular matrix
    if (error.message.includes('singular')) {
      try {
        // Basic pseudoinverse implementation
        const PrimeMath = require('../framework/math/prime-math.js');
        const matObj = PrimeMath.createMatrix(matrix);
        const { U, S, V } = PrimeMath.svd(matObj);
        
        // Find max singular value for threshold
        let maxSingularValue = 0;
        for (let i = 0; i < Math.min(S.rows, S.cols); i++) {
          if (S.values[i][i] > maxSingularValue) {
            maxSingularValue = S.values[i][i];
          }
        }
        
        // Compute threshold for zeroing small singular values
        const threshold = maxSingularValue * 1e-10;
        
        // Create inverse of S with filtering
        const SInv = PrimeMath.createMatrix(S.cols, S.rows);
        for (let i = 0; i < Math.min(S.rows, S.cols); i++) {
          if (S.values[i][i] > threshold) {
            SInv.values[i][i] = 1 / S.values[i][i];
          }
        }
        
        // Compute pseudoinverse: V * S^+ * U^T
        const UT = PrimeMath.transposeMatrix(U);
        const VS = PrimeMath.multiplyMatrices(V, SInv);
        const pseudoInv = PrimeMath.multiplyMatrices(VS, UT);
        
        // Convert to original format
        const result = MatrixCore.create(pseudoInv.cols, pseudoInv.rows);
        for (let i = 0; i < pseudoInv.cols; i++) {
          for (let j = 0; j < pseudoInv.rows; j++) {
            result[i][j] = pseudoInv.values[j][i];
          }
        }
        
        return result;
      } catch (e) {
        throw error; // If pseudoinverse fails, throw original error
      }
    }
    throw error;
  }
};

Prime.Math.Matrix.luDecomposition = function(matrix) {
  if (!MatrixValidation.isMatrix(matrix)) {
    throw new Prime.ValidationError('Matrix must be valid');
  }
  if (MatrixValidation.hasInvalidValues(matrix)) {
    throw new Prime.ValidationError('Matrix contains NaN or Infinity values');
  }
  if (!MatrixValidation.isSquare(matrix)) {
    throw new Prime.ValidationError('Matrix must be square');
  }
  
  // Check if matrix is nearly singular using a proper numerical approach
  if (MatrixValidation.isNearlySingular(matrix)) {
    throw new Prime.MathematicalError('Matrix is singular or nearly singular');
  }
  
  return MatrixAdvanced.luDecomposition(matrix);
};

Prime.Math.Matrix.qrDecomposition = function(matrix) {
  if (!MatrixValidation.isMatrix(matrix)) {
    throw new Prime.ValidationError('Matrix must be valid');
  }
  if (MatrixValidation.hasInvalidValues(matrix)) {
    throw new Prime.ValidationError('Matrix contains NaN or Infinity values');
  }
  
  return MatrixAdvanced.qrDecomposition(matrix);
};

Prime.Math.Matrix.eigenvalues = function(matrix, options = {}) {
  if (!MatrixValidation.isMatrix(matrix)) {
    throw new Prime.ValidationError('Matrix must be valid');
  }
  if (MatrixValidation.hasInvalidValues(matrix)) {
    throw new Prime.ValidationError('Matrix contains NaN or Infinity values');
  }
  if (!MatrixValidation.isSquare(matrix)) {
    throw new Prime.ValidationError('Matrix must be square');
  }
  
  return MatrixAdvanced.eigenvalues(matrix, options);
};

Prime.Math.Matrix.choleskyDecomposition = function(matrix) {
  if (!MatrixValidation.isMatrix(matrix)) {
    throw new Prime.ValidationError('Matrix must be valid');
  }
  if (MatrixValidation.hasInvalidValues(matrix)) {
    throw new Prime.ValidationError('Matrix contains NaN or Infinity values');
  }
  if (!MatrixValidation.isSquare(matrix)) {
    throw new Prime.ValidationError('Matrix must be square');
  }
  if (!MatrixValidation.isSymmetric(matrix)) {
    throw new Prime.ValidationError('Matrix must be symmetric for Cholesky decomposition');
  }
  
  return MatrixAdvanced.choleskyDecomposition(matrix);
};

// Additional matrix operations
Prime.Math.Matrix.trace = function(matrix) {
  return MatrixAdvanced.trace(matrix);
};

Prime.Math.Matrix.rank = function(matrix, tolerance = 1e-10) {
  return MatrixAdvanced.rank(matrix, tolerance);
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

// Matrix validation methods
Prime.Math.Matrix.isSymmetric = function(matrix, tolerance = 1e-10) {
  return MatrixValidation.isSymmetric(matrix, tolerance);
};

Prime.Math.Matrix.isNearlySingular = function(matrix, tolerance = 1e-10) {
  return MatrixValidation.isNearlySingular(matrix, tolerance);
};

Prime.Math.Matrix.isInvertible = function(matrix, tolerance = 1e-10) {
  return MatrixValidation.isInvertible(matrix, tolerance);
};

Prime.Math.Matrix.hasInvalidValues = function(matrix) {
  return MatrixValidation.hasInvalidValues(matrix);
};

// Export the enhanced Prime object
module.exports = Prime;
