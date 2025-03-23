/**
 * PrimeOS JavaScript Library - Matrix Adapter
 * Provides conversion utilities between SwappableMatrix and Prime.Math.Matrix
 */

const Prime = require('../../core');
const { PrimeStorageError } = require('../core/provider');

/**
 * Utilities to convert between SwappableMatrix and Prime.Math.Matrix
 */
const MatrixAdapter = {
  /**
   * Check if a value is a matrix (array of arrays)
   * @param {*} value - Value to check
   * @returns {boolean} True if the value is a matrix
   * @private
   */
  _isMatrix(value) {
    // Use a direct check to avoid circular dependency
    if (!value) return false;
    
    // Check for typed matrix (from MatrixCore)
    if (value._isTypedMatrix === true) {
      return true;
    }
    
    // Check for regular 2D array
    return Array.isArray(value) && value.length > 0 && Array.isArray(value[0]);
  },
  
  /**
   * Get the dimensions of a matrix
   * @param {Array|TypedArray} matrix - Matrix to get dimensions from
   * @returns {Object} Object with rows and cols properties
   * @private
   */
  _getDimensions(matrix) {
    // For typed matrices, return stored dimensions
    if (matrix._isTypedMatrix) {
      return { rows: matrix._rows, cols: matrix._cols };
    }
    
    // For regular arrays, calculate dimensions
    return {
      rows: matrix.length,
      cols: matrix[0].length,
    };
  },
  
  /**
   * Converts a Prime.Math.Matrix to a format compatible with SwappableMatrix
   * @param {Array|TypedArray} matrix - Prime.Math.Matrix to convert
   * @returns {Object} Matrix data in a format compatible with SwappableMatrix
   */
  fromMatrix(matrix) {
    // Use local matrix validation to avoid circular dependency
    if (!this._isMatrix(matrix)) {
      throw new PrimeStorageError(
        'Invalid matrix object',
        { matrix },
        'STORAGE_INVALID_MATRIX'
      );
    }
    
    // Get dimensions directly to avoid circular dependency
    const dimensions = this._getDimensions(matrix);
    
    // Create a wrapper object that retains the original matrix
    // but provides the interface needed by SwappableMatrix
    return {
      rows: dimensions.rows,
      columns: dimensions.cols,
      data: matrix,
      get: function(row, col) {
        return this.data[row][col];
      },
      set: function(row, col, value) {
        this.data[row][col] = value;
      },
      // Add trace method for compatibility
      trace: function() {
        return Promise.resolve(Prime.Math.Matrix.trace(this.data));
      }
    };
  },
  
  /**
   * Converts a SwappableMatrix to a Prime.Math.Matrix
   * @param {SwappableMatrix} swappableMatrix - SwappableMatrix to convert
   * @returns {Promise<Array|TypedArray>} Prime.Math.Matrix
   */
  async toMatrix(swappableMatrix) {
    const rows = swappableMatrix.getRows();
    const cols = swappableMatrix.getColumns();
    
    // Create a new matrix
    const matrix = Prime.Math.Matrix.create(rows, cols);
    
    // Fill with data from the swappable matrix
    for (let i = 0; i < rows; i++) {
      for (let j = 0; j < cols; j++) {
        matrix[i][j] = await swappableMatrix.get(i, j);
      }
    }
    
    return matrix;
  },
  
  /**
   * Registers this adapter with the Prime.Storage namespace
   */
  register() {
    if (Prime.Storage) {
      Prime.Storage.MatrixAdapter = this;
    }
  }
};

// Register the adapter
MatrixAdapter.register();

module.exports = MatrixAdapter;