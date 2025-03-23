/**
 * PrimeOS JavaScript Library - Swappable Matrix
 * Matrix implementation that swaps data to storage as needed
 */

const Prime = require('../../core');
const { StorageError } = require('../index');

/**
 * Matrix implementation that keeps part of the data in memory
 * and swaps to storage as needed
 */
class SwappableMatrix {
  /**
   * Creates a new swappable matrix
   * @param {StorageManager} storageManager - Storage manager to use
   * @param {string} id - ID of the stored matrix
   * @param {Object} matrix - Original matrix
   * @param {SwappableMatrixOptions} [options] - Matrix options
   */
  constructor(storageManager, id, matrix, options = {}) {
    this.storageManager = storageManager;
    this.id = id;
    
    // Get matrix dimensions - handle different matrix types
    if (matrix.rows && matrix.columns) {
      // Object with rows/columns properties
      this.rows = matrix.rows;
      this.columns = matrix.columns;
    } else if (matrix.getRows && matrix.getColumns) {
      // Matrix with getter methods
      this.rows = matrix.getRows();
      this.columns = matrix.getColumns();
    } else if (Prime.Math.Matrix.isMatrix(matrix)) {
      // Standard Matrix
      const dimensions = Prime.Math.Matrix.dimensions(matrix);
      this.rows = dimensions.rows;
      this.columns = dimensions.cols || dimensions.columns;
    } else {
      // Handle array-like matrix
      this.rows = matrix.length;
      this.columns = matrix[0] ? matrix[0].length : 0;
    }
    
    this.options = {
      blockSize: options.blockSize || 100,
      maxCachedBlocks: options.maxCachedBlocks || 10,
      evictionPolicy: options.evictionPolicy || 'lru',
      ...options
    };
    
    // Calculate number of blocks
    this.rowBlocks = Math.ceil(this.rows / this.options.blockSize);
    this.columnBlocks = Math.ceil(this.columns / this.options.blockSize);
    this.totalBlocks = this.rowBlocks * this.columnBlocks;
    
    // Initialize block cache
    this.blockCache = new Map();
    this.accessOrder = []; // For LRU eviction
    
    // Initialize - we'll split and store blocks after construction
    this.fullMatrix = this.rows * this.columns <= this.options.blockSize * this.options.maxCachedBlocks ? 
      matrix : null;
      
    // This property tracks whether we've split and stored the matrix
    this.initialized = false;
  }
  
  /**
   * Ensures the matrix is initialized
   * @private
   */
  async _ensureInitialized() {
    if (this.initialized) {
      return;
    }
    
    if (!this.fullMatrix) {
      // Split and store the matrix
      await this._splitAndStoreBlocks(this.originalMatrix);
    }
    
    this.initialized = true;
  }

  /**
   * Splits a matrix into blocks and stores them
   * @private
   * @param {Object} matrix - Matrix to split
   */
  async _splitAndStoreBlocks(matrix) {
    // For each block, extract data and store it
    const storePromises = [];
    
    for (let rowBlock = 0; rowBlock < this.rowBlocks; rowBlock++) {
      for (let colBlock = 0; colBlock < this.columnBlocks; colBlock++) {
        const blockId = this._getBlockId(rowBlock, colBlock);
        const blockData = this._extractBlock(matrix, rowBlock, colBlock);
        
        // Store block data
        storePromises.push(
          this.storageManager.store(blockData, `${this.id}_block_${blockId}`)
        );
      }
    }
    
    await Promise.all(storePromises);
  }

  /**
   * Extracts a block from a matrix
   * @private
   * @param {Object} matrix - Matrix to extract from
   * @param {number} rowBlock - Row block index
   * @param {number} colBlock - Column block index
   * @returns {Array} Block data
   */
  _extractBlock(matrix, rowBlock, colBlock) {
    const startRow = rowBlock * this.options.blockSize;
    const startCol = colBlock * this.options.blockSize;
    const endRow = Math.min(startRow + this.options.blockSize, this.rows);
    const endCol = Math.min(startCol + this.options.blockSize, this.columns);
    
    const blockRows = endRow - startRow;
    const blockCols = endCol - startCol;
    
    // Create block data
    const blockData = new Array(blockRows);
    
    for (let i = 0; i < blockRows; i++) {
      blockData[i] = new Array(blockCols);
      for (let j = 0; j < blockCols; j++) {
        // Handle different matrix types for get operation
        if (typeof matrix.get === 'function') {
          blockData[i][j] = matrix.get(startRow + i, startCol + j);
        } else if (Array.isArray(matrix) && Array.isArray(matrix[startRow + i])) {
          blockData[i][j] = matrix[startRow + i][startCol + j];
        } else {
          throw new StorageError('Unsupported matrix format', { matrixType: typeof matrix });
        }
      }
    }
    
    return blockData;
  }

  /**
   * Gets the block ID for a row and column block
   * @private
   * @param {number} rowBlock - Row block index
   * @param {number} colBlock - Column block index
   * @returns {number} Block ID
   */
  _getBlockId(rowBlock, colBlock) {
    return rowBlock * this.columnBlocks + colBlock;
  }

  /**
   * Gets the block indices for a matrix position
   * @private
   * @param {number} row - Matrix row
   * @param {number} col - Matrix column
   * @returns {Object} Block indices
   */
  _getBlockIndices(row, col) {
    const rowBlock = Math.floor(row / this.options.blockSize);
    const colBlock = Math.floor(col / this.options.blockSize);
    const blockId = this._getBlockId(rowBlock, colBlock);
    
    return {
      rowBlock,
      colBlock,
      blockId,
      rowInBlock: row % this.options.blockSize,
      colInBlock: col % this.options.blockSize
    };
  }

  /**
   * Loads a block into memory
   * @private
   * @param {number} blockId - Block ID
   * @returns {Promise<Array>} Block data
   */
  async _loadBlock(blockId) {
    // If block is in cache, update access order and return it
    if (this.blockCache.has(blockId)) {
      this._updateAccessOrder(blockId);
      return this.blockCache.get(blockId);
    }
    
    // Load block from storage
    const blockData = await this.storageManager.load(`${this.id}_block_${blockId}`);
    
    // Evict blocks if cache is full
    if (this.blockCache.size >= this.options.maxCachedBlocks) {
      this._evictBlock();
    }
    
    // Add block to cache
    this.blockCache.set(blockId, blockData);
    this._updateAccessOrder(blockId);
    
    return blockData;
  }

  /**
   * Updates the access order for LRU eviction
   * @private
   * @param {number} blockId - Block ID
   */
  _updateAccessOrder(blockId) {
    // Remove from current position
    const index = this.accessOrder.indexOf(blockId);
    if (index !== -1) {
      this.accessOrder.splice(index, 1);
    }
    
    // Add to the end (most recently used)
    this.accessOrder.push(blockId);
  }

  /**
   * Evicts a block from the cache
   * @private
   */
  _evictBlock() {
    if (this.blockCache.size === 0) {
      return;
    }
    
    let blockToEvict;
    
    switch (this.options.evictionPolicy) {
      case 'lru':
        // Least Recently Used - evict first in access order
        blockToEvict = this.accessOrder.shift();
        break;
      case 'fifo':
        // First In, First Out - evict oldest added block
        blockToEvict = Array.from(this.blockCache.keys())[0];
        break;
      case 'random':
        // Random - evict a random block
        const keys = Array.from(this.blockCache.keys());
        blockToEvict = keys[Math.floor(Math.random() * keys.length)];
        break;
      default:
        // Default to LRU
        blockToEvict = this.accessOrder.shift();
    }
    
    // Remove from cache
    this.blockCache.delete(blockToEvict);
  }

  /**
   * Gets a value from the matrix
   * @param {number} row - Matrix row
   * @param {number} col - Matrix column
   * @returns {number} Matrix value
   */
  async get(row, col) {
    this._validateIndices(row, col);
    
    // Ensure initialization
    await this._ensureInitialized();
    
    // If we have the full matrix in memory, use it directly
    if (this.fullMatrix) {
      // Handle different matrix types for get operation
      if (typeof this.fullMatrix.get === 'function') {
        return this.fullMatrix.get(row, col);
      } else if (Array.isArray(this.fullMatrix) && Array.isArray(this.fullMatrix[row])) {
        return this.fullMatrix[row][col];
      } else {
        throw new StorageError('Unsupported matrix format', { matrixType: typeof this.fullMatrix });
      }
    }
    
    // Get block indices
    const { blockId, rowInBlock, colInBlock } = this._getBlockIndices(row, col);
    
    // Load block
    const blockData = await this._loadBlock(blockId);
    
    // Get value from block
    return blockData[rowInBlock][colInBlock];
  }

  /**
   * Sets a value in the matrix
   * @param {number} row - Matrix row
   * @param {number} col - Matrix column
   * @param {number} value - Value to set
   */
  async set(row, col, value) {
    this._validateIndices(row, col);
    
    // Ensure initialization
    await this._ensureInitialized();
    
    // If we have the full matrix in memory, update it directly
    if (this.fullMatrix) {
      // Handle different matrix types for set operation
      if (typeof this.fullMatrix.set === 'function') {
        this.fullMatrix.set(row, col, value);
      } else if (Array.isArray(this.fullMatrix) && Array.isArray(this.fullMatrix[row])) {
        this.fullMatrix[row][col] = value;
      } else {
        throw new StorageError('Unsupported matrix format for set operation', { matrixType: typeof this.fullMatrix });
      }
      
      // Update storage
      await this.storageManager.store(this.fullMatrix, this.id);
      return;
    }
    
    // Get block indices
    const { blockId, rowInBlock, colInBlock } = this._getBlockIndices(row, col);
    
    // Load block
    const blockData = await this._loadBlock(blockId);
    
    // Update value in block
    blockData[rowInBlock][colInBlock] = value;
    
    // Store updated block
    await this.storageManager.store(blockData, `${this.id}_block_${blockId}`);
  }

  /**
   * Validates row and column indices
   * @private
   * @param {number} row - Matrix row
   * @param {number} col - Matrix column
   */
  _validateIndices(row, col) {
    if (row < 0 || row >= this.rows || col < 0 || col >= this.columns) {
      throw new StorageError(
        `Invalid matrix indices: (${row}, ${col})`,
        { row, col, rows: this.rows, columns: this.columns },
        'STORAGE_INVALID_INDICES'
      );
    }
  }

  /**
   * Computes the trace of the matrix
   * @returns {Promise<number>} Matrix trace
   */
  async trace() {
    // Ensure initialization
    await this._ensureInitialized();
    
    if (this.fullMatrix) {
      // If the matrix has a trace method, use it
      if (typeof this.fullMatrix.trace === 'function') {
        return Promise.resolve(this.fullMatrix.trace());
      }
      
      // Otherwise compute manually from the full matrix
      let sum = 0;
      const minDim = Math.min(this.rows, this.columns);
      
      for (let i = 0; i < minDim; i++) {
        // Get diagonal elements
        if (typeof this.fullMatrix.get === 'function') {
          sum += this.fullMatrix.get(i, i);
        } else if (Array.isArray(this.fullMatrix) && Array.isArray(this.fullMatrix[i])) {
          sum += this.fullMatrix[i][i];
        }
      }
      
      return sum;
    }
    
    // Compute from blocks
    let sum = 0;
    const minDim = Math.min(this.rows, this.columns);
    
    for (let i = 0; i < minDim; i++) {
      sum += await this.get(i, i);
    }
    
    return sum;
  }

  /**
   * Gets all data as a standard matrix
   * @returns {Promise<Object>} Matrix object
   */
  async toMatrix() {
    // Ensure initialization
    await this._ensureInitialized();
    
    if (this.fullMatrix) {
      // Convert the fullMatrix to a Prime.Math.Matrix if it's not already
      if (this.fullMatrix.data && Prime.Math.Matrix.isMatrix(this.fullMatrix.data)) {
        return this.fullMatrix.data;
      } else if (Prime.Math.Matrix.isMatrix(this.fullMatrix)) {
        return this.fullMatrix;
      } else {
        // Create a new matrix if the stored format is different
        const matrix = Prime.Math.Matrix.create(this.rows, this.columns);
        
        for (let i = 0; i < this.rows; i++) {
          for (let j = 0; j < this.columns; j++) {
            if (typeof this.fullMatrix.get === 'function') {
              matrix[i][j] = this.fullMatrix.get(i, j);
            } else if (Array.isArray(this.fullMatrix) && Array.isArray(this.fullMatrix[i])) {
              matrix[i][j] = this.fullMatrix[i][j];
            }
          }
        }
        
        return matrix;
      }
    }
    
    // Create a new matrix using Prime.Math.Matrix.create
    const matrix = Prime.Math.Matrix.create(this.rows, this.columns);
    
    // Fill with data from blocks
    for (let i = 0; i < this.rows; i++) {
      for (let j = 0; j < this.columns; j++) {
        matrix[i][j] = await this.get(i, j);
      }
    }
    
    return matrix;
  }

  /**
   * Gets a submatrix
   * @param {number} startRow - Start row
   * @param {number} startCol - Start column
   * @param {number} endRow - End row (exclusive)
   * @param {number} endCol - End column (exclusive)
   * @returns {Promise<Object>} Submatrix
   */
  async submatrix(startRow, startCol, endRow, endCol) {
    // Validate indices
    if (startRow < 0 || startCol < 0 || endRow > this.rows || endCol > this.columns) {
      throw new StorageError(
        'Invalid submatrix indices',
        { startRow, startCol, endRow, endCol, rows: this.rows, columns: this.columns },
        'STORAGE_INVALID_INDICES'
      );
    }
    
    // Ensure initialization
    await this._ensureInitialized();
    
    const rows = endRow - startRow;
    const cols = endCol - startCol;
    
    // Create submatrix using Prime.Math.Matrix.create to ensure compatibility
    const submatrix = Prime.Math.Matrix.create(rows, cols);
    
    // Fill with data
    for (let i = 0; i < rows; i++) {
      for (let j = 0; j < cols; j++) {
        submatrix[i][j] = await this.get(startRow + i, startCol + j);
      }
    }
    
    return submatrix;
  }

  /**
   * Multiplies the matrix by another matrix
   * @param {Object|SwappableMatrix} other - Matrix to multiply by
   * @returns {Promise<Object>} Result matrix
   */
  async multiply(other) {
    // Ensure initialization
    await this._ensureInitialized();
    
    // Handle different matrix types
    let otherRows, otherCols;
    
    if (other.getRows && typeof other.getRows === 'function') {
      // SwappableMatrix or similar with getter methods
      otherRows = other.getRows();
      otherCols = other.getColumns();
    } else if (Prime.Math.Matrix.isMatrix(other)) {
      // Standard Prime.Math.Matrix
      const dimensions = Prime.Math.Matrix.dimensions(other);
      otherRows = dimensions.rows;
      otherCols = dimensions.cols || dimensions.columns;
    } else if (other.rows && other.columns) {
      // Object with rows/columns properties
      otherRows = other.rows;
      otherCols = other.columns;
    } else {
      // Assume array-like with length properties
      otherRows = other.length;
      otherCols = other[0].length;
    }
    
    // Validate dimensions
    if (this.columns !== otherRows) {
      throw new StorageError(
        'Invalid matrix dimensions for multiplication',
        { thisColumns: this.columns, otherRows: otherRows },
        'STORAGE_INVALID_DIMENSIONS'
      );
    }
    
    // Get dimensions of result matrix
    const resultRows = this.rows;
    const resultCols = otherCols;
    
    // Create result matrix using Prime.Math.Matrix.create
    const result = Prime.Math.Matrix.create(resultRows, resultCols);
    
    // If other is a SwappableMatrix or has a get method, use it
    const isSwappable = other.get && typeof other.get === 'function';
    
    // For performance, if both matrices are fully in memory, use direct multiplication
    if (this.fullMatrix && !isSwappable) {
      // Use Prime.Math.Matrix operations if available
      if (this.fullMatrix.multiply && typeof this.fullMatrix.multiply === 'function') {
        return this.fullMatrix.multiply(other);
      }
    }
    
    // Multiply matrices
    for (let i = 0; i < resultRows; i++) {
      for (let j = 0; j < resultCols; j++) {
        let sum = 0;
        
        for (let k = 0; k < this.columns; k++) {
          const thisVal = await this.get(i, k);
          const otherVal = isSwappable ? await other.get(k, j) : other[k][j];
          sum += thisVal * otherVal;
        }
        
        result[i][j] = sum;
      }
    }
    
    return result;
  }

  /**
   * Gets the number of rows
   * @returns {number} Number of rows
   */
  getRows() {
    return this.rows;
  }

  /**
   * Gets the number of columns
   * @returns {number} Number of columns
   */
  getColumns() {
    return this.columns;
  }
}

module.exports = SwappableMatrix;