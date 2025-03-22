/**
 * PrimeOS JavaScript Library - Math
 * Matrix Core Operations
 * Core matrix operations with memory optimization and performance enhancements
 */

// Import the Prime object
const Prime = require("../core");

/**
 * Core matrix operations with optimized implementations
 */
const MatrixCore = {
  /**
   * Create a new matrix with specified dimensions
   * @param {number} rows - Number of rows
   * @param {number} cols - Number of columns
   * @param {number} [initialValue=0] - Initial value for all elements
   * @param {Object} [options={}] - Additional options
   * @param {boolean} [options.useTypedArray=false] - Use TypedArray for memory efficiency
   * @param {string} [options.arrayType='float64'] - Type of TypedArray ('float64', 'float32', etc.)
   * @returns {Array|TypedArray} - New matrix with specified dimensions
   */
  create: function (rows, cols, initialValue = 0, options = {}) {
    if (
      !Prime.Utils.isNumber(rows) ||
      rows <= 0 ||
      !Number.isInteger(rows) ||
      !Prime.Utils.isNumber(cols) ||
      cols <= 0 ||
      !Number.isInteger(cols)
    ) {
      throw new Prime.ValidationError("Dimensions must be positive integers");
    }

    // Use TypedArrays if specified
    if (options.useTypedArray) {
      // Determine array constructor based on type
      let TypedArrayConstructor;
      switch (options.arrayType) {
        case 'float32':
          TypedArrayConstructor = Float32Array;
          break;
        case 'int32':
          TypedArrayConstructor = Int32Array;
          break;
        case 'int16':
          TypedArrayConstructor = Int16Array;
          break;
        case 'uint8':
          TypedArrayConstructor = Uint8Array;
          break;
        case 'float64':
        default:
          TypedArrayConstructor = Float64Array;
      }

      // Create a flat typed array for the entire matrix
      const flatArray = new TypedArrayConstructor(rows * cols);
      
      // Fill with initial value if needed
      if (initialValue !== 0) {
        flatArray.fill(initialValue);
      }
      
      // Create a proxy to allow 2D indexing with flatArray[i][j] notation
      // This avoids creating nested arrays while maintaining the same syntax
      const matrix = new Array(rows);
      for (let i = 0; i < rows; i++) {
        // Create a view for each row
        matrix[i] = new TypedArrayConstructor(
          flatArray.buffer, 
          i * cols * TypedArrayConstructor.BYTES_PER_ELEMENT, 
          cols
        );
      }
      
      // Add metadata for easier handling
      Object.defineProperties(matrix, {
        '_isTypedMatrix': { value: true },
        '_rows': { value: rows },
        '_cols': { value: cols },
        '_flatArray': { value: flatArray },
        '_arrayType': { value: options.arrayType || 'float64' }
      });
      
      return matrix;
    }

    // Otherwise use regular JavaScript arrays
    return Array(rows)
      .fill()
      .map(() => Array(cols).fill(initialValue));
  },

  /**
   * Create an identity matrix of specified size
   * @param {number} size - Size of the identity matrix
   * @param {Object} [options={}] - Additional options
   * @returns {Array|TypedArray} - Identity matrix
   */
  identity: function (size, options = {}) {
    if (!Prime.Utils.isNumber(size) || size <= 0 || !Number.isInteger(size)) {
      throw new Prime.ValidationError("Size must be a positive integer");
    }

    const result = this.create(size, size, 0, options);
    
    // Set diagonal elements to 1
    for (let i = 0; i < size; i++) {
      result[i][i] = 1;
    }

    return result;
  },

  /**
   * Check if a value is a matrix (array of arrays or typed matrix)
   * @param {*} value - Value to check
   * @returns {boolean} - True if the value is a matrix
   */
  isMatrix: function (value) {
    if (!value) return false;
    
    // Check for typed matrix
    if (value._isTypedMatrix === true) {
      return true;
    }
    
    // Check for regular 2D array
    return Array.isArray(value) && 
           value.length > 0 && 
           Array.isArray(value[0]);
  },
  
  /**
   * Get the dimensions of a matrix
   * @param {Array|TypedArray} matrix - Matrix to get dimensions of
   * @returns {Object} - Object with rows and cols properties
   */
  dimensions: function (matrix) {
    if (!this.isMatrix(matrix)) {
      throw new Prime.ValidationError("Value is not a matrix");
    }
    
    // For typed matrices, return stored dimensions
    if (matrix._isTypedMatrix) {
      return { rows: matrix._rows, cols: matrix._cols };
    }
    
    // For regular arrays, calculate dimensions
    return { 
      rows: matrix.length, 
      cols: matrix[0].length 
    };
  },

  /**
   * Add two matrices element-wise with Kahan summation for numerical stability
   * @param {Array|TypedArray} a - First matrix
   * @param {Array|TypedArray} b - Second matrix
   * @param {Array|TypedArray} [result] - Optional result matrix (for in-place operations)
   * @returns {Array|TypedArray} - Result of addition
   */
  add: function (a, b, result) {
    if (!this.isMatrix(a) || !this.isMatrix(b)) {
      throw new Prime.ValidationError("Matrices must be valid");
    }

    const aDim = this.dimensions(a);
    const bDim = this.dimensions(b);

    if (aDim.rows !== bDim.rows || aDim.cols !== bDim.cols) {
      throw new Prime.ValidationError(
        "Matrices must have the same dimensions"
      );
    }

    // Use provided result matrix if available and correctly sized
    if (result && this.isMatrix(result)) {
      const resultDim = this.dimensions(result);
      if (resultDim.rows !== aDim.rows || resultDim.cols !== aDim.cols) {
        throw new Prime.ValidationError(
          "Result matrix has incorrect dimensions"
        );
      }
      
      // Perform element-wise addition with Kahan summation for numerical stability
      // when dealing with values of very different magnitudes
      for (let i = 0; i < aDim.rows; i++) {
        for (let j = 0; j < aDim.cols; j++) {
          // Use Kahan summation for better numerical stability
          const sum = a[i][j];
          const y = b[i][j];
          const t = sum + y;
          // This corrects for floating point error when adding values of different magnitudes
          const c = (t - sum) - y;  // Compute the error term
          result[i][j] = t - c;     // Corrected sum
        }
      }
      
      return result;
    }
    
    // Create new result matrix with the same type as input
    // If a is typed, create a typed matrix of the same type
    const useTypedArray = a._isTypedMatrix;
    const arrayType = a._arrayType;
    
    const newResult = this.create(aDim.rows, aDim.cols, 0, { 
      useTypedArray,
      arrayType
    });
    
    // Perform element-wise addition with Kahan summation for numerical stability
    for (let i = 0; i < aDim.rows; i++) {
      for (let j = 0; j < aDim.cols; j++) {
        // Use Kahan summation for better numerical stability
        const sum = a[i][j];
        const y = b[i][j];
        const t = sum + y;
        // This corrects for floating point error when adding values of different magnitudes
        const c = (t - sum) - y;  // Compute the error term
        newResult[i][j] = t - c;  // Corrected sum
      }
    }
    
    return newResult;
  },

  /**
   * Subtract matrix b from matrix a element-wise with Kahan summation for numerical stability
   * @param {Array|TypedArray} a - First matrix
   * @param {Array|TypedArray} b - Second matrix
   * @param {Array|TypedArray} [result] - Optional result matrix (for in-place operations)
   * @returns {Array|TypedArray} - Result of subtraction
   */
  subtract: function (a, b, result) {
    if (!this.isMatrix(a) || !this.isMatrix(b)) {
      throw new Prime.ValidationError("Matrices must be valid");
    }

    const aDim = this.dimensions(a);
    const bDim = this.dimensions(b);

    if (aDim.rows !== bDim.rows || aDim.cols !== bDim.cols) {
      throw new Prime.ValidationError(
        "Matrices must have the same dimensions"
      );
    }

    // Use provided result matrix if available and correctly sized
    if (result && this.isMatrix(result)) {
      const resultDim = this.dimensions(result);
      if (resultDim.rows !== aDim.rows || resultDim.cols !== aDim.cols) {
        throw new Prime.ValidationError(
          "Result matrix has incorrect dimensions"
        );
      }
      
      // Perform element-wise subtraction with Kahan summation for numerical stability
      // when dealing with values of very different magnitudes
      for (let i = 0; i < aDim.rows; i++) {
        for (let j = 0; j < aDim.cols; j++) {
          // Use Kahan summation for better numerical stability
          const sum = a[i][j];
          const y = -b[i][j]; // Negate b for subtraction
          const t = sum + y;
          // This corrects for floating point error when subtracting values of different magnitudes
          const c = (t - sum) - y; // Compute the error term
          result[i][j] = t - c;    // Corrected result
        }
      }
      
      return result;
    }
    
    // Create new result matrix with the same type as input
    // If a is typed, create a typed matrix of the same type
    const useTypedArray = a._isTypedMatrix;
    const arrayType = a._arrayType;
    
    const newResult = this.create(aDim.rows, aDim.cols, 0, { 
      useTypedArray,
      arrayType
    });
    
    // Perform element-wise subtraction with Kahan summation for numerical stability
    for (let i = 0; i < aDim.rows; i++) {
      for (let j = 0; j < aDim.cols; j++) {
        // Use Kahan summation for better numerical stability
        const sum = a[i][j];
        const y = -b[i][j]; // Negate b for subtraction
        const t = sum + y;
        // This corrects for floating point error when subtracting values of different magnitudes
        const c = (t - sum) - y; // Compute the error term
        newResult[i][j] = t - c; // Corrected result
      }
    }
    
    return newResult;
  },

  /**
   * Multiply two matrices with Kahan summation for numerical stability
   * @param {Array|TypedArray} a - First matrix
   * @param {Array|TypedArray} b - Second matrix
   * @param {Array|TypedArray} [result] - Optional result matrix (for in-place operations)
   * @returns {Array|TypedArray} - Result of multiplication
   */
  multiply: function (a, b, result) {
    if (!this.isMatrix(a) || !this.isMatrix(b)) {
      throw new Prime.ValidationError("Matrices must be valid");
    }

    const aDim = this.dimensions(a);
    const bDim = this.dimensions(b);

    if (aDim.cols !== bDim.rows) {
      throw new Prime.ValidationError(
        "First matrix column count must match second matrix row count"
      );
    }
    
    // Use provided result matrix if available and correctly sized
    if (result && this.isMatrix(result)) {
      const resultDim = this.dimensions(result);
      if (resultDim.rows !== aDim.rows || resultDim.cols !== bDim.cols) {
        throw new Prime.ValidationError(
          "Result matrix has incorrect dimensions"
        );
      }
      
      // Zero the result matrix first
      for (let i = 0; i < aDim.rows; i++) {
        for (let j = 0; j < bDim.cols; j++) {
          result[i][j] = 0;
        }
      }
    } else {
      // Create new result matrix with the same type as input
      // If a is typed, create a typed matrix of the same type
      const useTypedArray = a._isTypedArray;
      const arrayType = a._arrayType;
      
      result = this.create(aDim.rows, bDim.cols, 0, { 
        useTypedArray,
        arrayType
      });
    }
    
    // Perform matrix multiplication with Kahan summation
    for (let i = 0; i < aDim.rows; i++) {
      for (let j = 0; j < bDim.cols; j++) {
        let sum = 0;
        let compensation = 0; // For Kahan summation
        
        for (let k = 0; k < aDim.cols; k++) {
          // Kahan summation to reduce numerical errors
          const product = a[i][k] * b[k][j];
          const y = product - compensation;
          const t = sum + y;
          compensation = (t - sum) - y;
          sum = t;
        }
        
        result[i][j] = sum;
      }
    }
    
    return result;
  },

  /**
   * Scale a matrix by a scalar
   * @param {Array|TypedArray} matrix - Matrix to scale
   * @param {number} scalar - Scaling factor
   * @param {Array|TypedArray} [result] - Optional result matrix (for in-place operations)
   * @returns {Array|TypedArray} - Scaled matrix
   */
  scale: function (matrix, scalar, result) {
    if (!this.isMatrix(matrix)) {
      throw new Prime.ValidationError("Matrix must be valid");
    }

    if (!Prime.Utils.isNumber(scalar)) {
      throw new Prime.ValidationError("Scalar must be a number");
    }

    const dim = this.dimensions(matrix);
    
    // Use provided result matrix if available and correctly sized
    if (result && this.isMatrix(result)) {
      const resultDim = this.dimensions(result);
      if (resultDim.rows !== dim.rows || resultDim.cols !== dim.cols) {
        throw new Prime.ValidationError(
          "Result matrix has incorrect dimensions"
        );
      }
      
      // Perform scaling
      for (let i = 0; i < dim.rows; i++) {
        for (let j = 0; j < dim.cols; j++) {
          result[i][j] = matrix[i][j] * scalar;
        }
      }
      
      return result;
    }
    
    // Create new result matrix with the same type as input
    const useTypedArray = matrix._isTypedArray;
    const arrayType = matrix._arrayType;
    
    const newResult = this.create(dim.rows, dim.cols, 0, { 
      useTypedArray,
      arrayType
    });
    
    // Perform scaling
    for (let i = 0; i < dim.rows; i++) {
      for (let j = 0; j < dim.cols; j++) {
        newResult[i][j] = matrix[i][j] * scalar;
      }
    }
    
    return newResult;
  },

  /**
   * Transpose a matrix
   * @param {Array|TypedArray} matrix - Matrix to transpose
   * @param {Array|TypedArray} [result] - Optional result matrix (for in-place operations)
   * @returns {Array|TypedArray} - Transposed matrix
   */
  transpose: function (matrix, result) {
    if (!this.isMatrix(matrix)) {
      throw new Prime.ValidationError("Matrix must be valid");
    }

    const dim = this.dimensions(matrix);
    
    // Use provided result matrix if available and correctly sized
    if (result && this.isMatrix(result)) {
      const resultDim = this.dimensions(result);
      if (resultDim.rows !== dim.cols || resultDim.cols !== dim.rows) {
        throw new Prime.ValidationError(
          "Result matrix must have transposed dimensions"
        );
      }
      
      // Perform transposition
      for (let i = 0; i < dim.rows; i++) {
        for (let j = 0; j < dim.cols; j++) {
          result[j][i] = matrix[i][j];
        }
      }
      
      return result;
    }
    
    // Create new result matrix with the same type as input
    const useTypedArray = matrix._isTypedArray;
    const arrayType = matrix._arrayType;
    
    const newResult = this.create(dim.cols, dim.rows, 0, { 
      useTypedArray,
      arrayType
    });
    
    // Perform transposition
    for (let i = 0; i < dim.rows; i++) {
      for (let j = 0; j < dim.cols; j++) {
        newResult[j][i] = matrix[i][j];
      }
    }
    
    return newResult;
  },
  
  /**
   * Copy values from one matrix to another
   * @param {Array|TypedArray} source - Source matrix
   * @param {Array|TypedArray} destination - Destination matrix
   * @returns {Array|TypedArray} - Destination matrix (modified in-place)
   */
  copy: function (source, destination) {
    if (!this.isMatrix(source) || !this.isMatrix(destination)) {
      throw new Prime.ValidationError("Source and destination must be valid matrices");
    }
    
    const sourceDim = this.dimensions(source);
    const destDim = this.dimensions(destination);
    
    if (sourceDim.rows !== destDim.rows || sourceDim.cols !== destDim.cols) {
      throw new Prime.ValidationError("Matrices must have the same dimensions");
    }
    
    // Copy values
    for (let i = 0; i < sourceDim.rows; i++) {
      for (let j = 0; j < sourceDim.cols; j++) {
        destination[i][j] = source[i][j];
      }
    }
    
    return destination;
  },
  
  /**
   * Create a deep copy of a matrix
   * @param {Array|TypedArray} matrix - Matrix to clone
   * @returns {Array|TypedArray} - New copy of the matrix
   */
  clone: function (matrix) {
    if (!this.isMatrix(matrix)) {
      throw new Prime.ValidationError("Matrix must be valid");
    }
    
    const dim = this.dimensions(matrix);
    
    // Create new matrix with the same type as input
    const useTypedArray = matrix._isTypedArray;
    const arrayType = matrix._arrayType;
    
    const result = this.create(dim.rows, dim.cols, 0, { 
      useTypedArray,
      arrayType
    });
    
    // Copy values
    for (let i = 0; i < dim.rows; i++) {
      for (let j = 0; j < dim.cols; j++) {
        result[i][j] = matrix[i][j];
      }
    }
    
    return result;
  },
  
  /**
   * Element-wise multiplication of two matrices (Hadamard product)
   * @param {Array|TypedArray} a - First matrix
   * @param {Array|TypedArray} b - Second matrix
   * @param {Array|TypedArray} [result] - Optional result matrix (for in-place operations)
   * @returns {Array|TypedArray} - Result of element-wise multiplication
   */
  elementWiseMultiply: function (a, b, result) {
    if (!this.isMatrix(a) || !this.isMatrix(b)) {
      throw new Prime.ValidationError("Matrices must be valid");
    }
    
    const aDim = this.dimensions(a);
    const bDim = this.dimensions(b);
    
    if (aDim.rows !== bDim.rows || aDim.cols !== bDim.cols) {
      throw new Prime.ValidationError("Matrices must have the same dimensions");
    }
    
    // Use provided result matrix if available and correctly sized
    if (result && this.isMatrix(result)) {
      const resultDim = this.dimensions(result);
      if (resultDim.rows !== aDim.rows || resultDim.cols !== aDim.cols) {
        throw new Prime.ValidationError("Result matrix has incorrect dimensions");
      }
      
      // Perform element-wise multiplication
      for (let i = 0; i < aDim.rows; i++) {
        for (let j = 0; j < aDim.cols; j++) {
          result[i][j] = a[i][j] * b[i][j];
        }
      }
      
      return result;
    }
    
    // Create new result matrix with the same type as input
    const useTypedArray = a._isTypedArray;
    const arrayType = a._arrayType;
    
    const newResult = this.create(aDim.rows, aDim.cols, 0, { 
      useTypedArray,
      arrayType
    });
    
    // Perform element-wise multiplication
    for (let i = 0; i < aDim.rows; i++) {
      for (let j = 0; j < aDim.cols; j++) {
        newResult[i][j] = a[i][j] * b[i][j];
      }
    }
    
    return newResult;
  },
  
  /**
   * Fill a matrix with a specific value
   * @param {Array|TypedArray} matrix - Matrix to fill
   * @param {number} value - Value to fill the matrix with
   * @returns {Array|TypedArray} - Filled matrix (modified in-place)
   */
  fill: function (matrix, value) {
    if (!this.isMatrix(matrix)) {
      throw new Prime.ValidationError("Matrix must be valid");
    }
    
    if (!Prime.Utils.isNumber(value)) {
      throw new Prime.ValidationError("Fill value must be a number");
    }
    
    const dim = this.dimensions(matrix);
    
    // Fill matrix with value
    for (let i = 0; i < dim.rows; i++) {
      for (let j = 0; j < dim.cols; j++) {
        matrix[i][j] = value;
      }
    }
    
    return matrix;
  }
};

// Export the MatrixCore module
Prime.Math = Prime.Math || {};
Prime.Math.MatrixCore = MatrixCore;

// Export the enhanced Prime object
module.exports = Prime;