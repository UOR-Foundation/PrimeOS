/**
 * PrimeOS JavaScript Library - Matrix Adapter Class
 * Provides an interface for working with matrices stored in storage
 */

const Prime = require("../../core");
const { StorageError } = require("../index");

/**
 * Matrix adapter for working with stored matrices
 */
class MatrixAdapter {
  /**
   * Creates a new matrix adapter
   * @param {StorageManager} storageManager - Storage manager to use
   * @param {string} storageId - ID of the stored matrix
   * @param {Object} options - Matrix adapter options
   */
  constructor(storageManager, storageId, options = {}) {
    this.storageManager = storageManager;
    this.storageId = storageId;
    this.options = {
      ...options,
    };

    this.rows = 0;
    this.columns = 0;
    this.matrix = null;
    this.modified = false;
    this.initialized = false;
  }

  /**
   * Initializes the matrix adapter
   * @returns {Promise<void>}
   */
  async init() {
    if (this.initialized) {
      return;
    }

    try {
      // Load the matrix
      this.matrix = await this.storageManager.load(this.storageId);

      if (!this.matrix) {
        throw new StorageError(
          "Matrix not found in storage",
          { id: this.storageId },
          "STORAGE_MATRIX_NOT_FOUND",
        );
      }

      // Get dimensions
      if (Array.isArray(this.matrix)) {
        this.rows = this.matrix.length;
        this.columns = Array.isArray(this.matrix[0])
          ? this.matrix[0].length
          : 0;
      } else if (this.matrix.rows && this.matrix.columns) {
        // Handle matrix object with dimensions
        this.rows = this.matrix.rows;
        this.columns = this.matrix.columns;
      } else if (this.matrix.getRows && this.matrix.getColumns) {
        // Handle matrix with getter methods
        this.rows = this.matrix.getRows();
        this.columns = this.matrix.getColumns();
      } else {
        throw new StorageError(
          "Invalid matrix format",
          { id: this.storageId },
          "STORAGE_INVALID_MATRIX",
        );
      }

      this.initialized = true;
    } catch (error) {
      if (error instanceof StorageError) {
        throw error;
      }

      throw new StorageError(
        `Failed to initialize matrix adapter: ${error.message}`,
        { id: this.storageId, originalError: error },
        "STORAGE_ADAPTER_INIT_FAILED",
        error,
      );
    }
  }

  /**
   * Gets a value from the matrix
   * @param {number} row - Row index
   * @param {number} col - Column index
   * @returns {Promise<number>} Matrix value
   */
  async get(row, col) {
    if (!this.initialized) {
      await this.init();
    }

    // Validate indices
    if (row < 0 || row >= this.rows || col < 0 || col >= this.columns) {
      throw new StorageError(
        `Invalid matrix indices: (${row}, ${col})`,
        { row, col, rows: this.rows, columns: this.columns },
        "STORAGE_INVALID_INDICES",
      );
    }

    // Get value
    if (Array.isArray(this.matrix)) {
      return this.matrix[row][col];
    } else if (typeof this.matrix.get === "function") {
      return this.matrix.get(row, col);
    } else {
      throw new StorageError(
        "Unsupported matrix format",
        { matrixType: typeof this.matrix },
        "STORAGE_UNSUPPORTED_MATRIX",
      );
    }
  }

  /**
   * Sets a value in the matrix
   * @param {number} row - Row index
   * @param {number} col - Column index
   * @param {number} value - Value to set
   * @returns {Promise<void>}
   */
  async set(row, col, value) {
    if (!this.initialized) {
      await this.init();
    }

    // Validate indices
    if (row < 0 || row >= this.rows || col < 0 || col >= this.columns) {
      throw new StorageError(
        `Invalid matrix indices: (${row}, ${col})`,
        { row, col, rows: this.rows, columns: this.columns },
        "STORAGE_INVALID_INDICES",
      );
    }

    // Create a deep copy of the original matrix to modify
    // This ensures the original matrix is not affected until saved (as expected by tests)
    if (Array.isArray(this.matrix) && !this._cloned) {
      this.originalMatrix = this.matrix; // Save reference to original

      // Create deep copy
      this.matrix = this.matrix.map((row) => [...row]);
      this._cloned = true;
    }

    // Set value
    if (Array.isArray(this.matrix)) {
      this.matrix[row][col] = value;
    } else if (typeof this.matrix.set === "function") {
      this.matrix.set(row, col, value);
    } else {
      throw new StorageError(
        "Unsupported matrix format for set operation",
        { matrixType: typeof this.matrix },
        "STORAGE_UNSUPPORTED_MATRIX",
      );
    }

    this.modified = true;
  }

  /**
   * Gets a row from the matrix
   * @param {number} row - Row index
   * @returns {Promise<Array>} Matrix row
   */
  async getRow(row) {
    if (!this.initialized) {
      await this.init();
    }

    // Validate row index
    if (row < 0 || row >= this.rows) {
      throw new StorageError(
        `Invalid row index: ${row}`,
        { row, rows: this.rows },
        "STORAGE_INVALID_INDEX",
      );
    }

    // Get row
    if (Array.isArray(this.matrix)) {
      return [...this.matrix[row]]; // Return a copy to prevent unintended modifications
    } else if (typeof this.matrix.getRow === "function") {
      return this.matrix.getRow(row);
    } else {
      // Construct row manually
      const row_data = new Array(this.columns);
      for (let j = 0; j < this.columns; j++) {
        row_data[j] = await this.get(row, j);
      }
      return row_data;
    }
  }

  /**
   * Gets a column from the matrix
   * @param {number} col - Column index
   * @returns {Promise<Array>} Matrix column
   */
  async getColumn(col) {
    if (!this.initialized) {
      await this.init();
    }

    // Validate column index
    if (col < 0 || col >= this.columns) {
      throw new StorageError(
        `Invalid column index: ${col}`,
        { col, columns: this.columns },
        "STORAGE_INVALID_INDEX",
      );
    }

    // Get column
    if (typeof this.matrix.getColumn === "function") {
      return this.matrix.getColumn(col);
    } else {
      // Construct column manually
      const col_data = new Array(this.rows);
      for (let i = 0; i < this.rows; i++) {
        if (Array.isArray(this.matrix)) {
          col_data[i] = this.matrix[i][col];
        } else {
          col_data[i] = await this.get(i, col);
        }
      }
      return col_data;
    }
  }

  /**
   * Sets a row in the matrix
   * @param {number} row - Row index
   * @param {Array} values - Row values
   * @returns {Promise<void>}
   */
  async setRow(row, values) {
    if (!this.initialized) {
      await this.init();
    }

    // Validate row index
    if (row < 0 || row >= this.rows) {
      throw new StorageError(
        `Invalid row index: ${row}`,
        { row, rows: this.rows },
        "STORAGE_INVALID_INDEX",
      );
    }

    // Validate values length
    if (!Array.isArray(values) || values.length !== this.columns) {
      throw new StorageError(
        `Invalid row values length: ${values.length}`,
        { values, columns: this.columns },
        "STORAGE_INVALID_SIZE",
      );
    }

    // Set row
    if (Array.isArray(this.matrix)) {
      this.matrix[row] = [...values]; // Set with a copy to prevent unintended side effects
    } else if (typeof this.matrix.setRow === "function") {
      this.matrix.setRow(row, values);
    } else {
      // Set row values individually
      for (let j = 0; j < this.columns; j++) {
        await this.set(row, j, values[j]);
      }
    }

    this.modified = true;
  }

  /**
   * Sets a column in the matrix
   * @param {number} col - Column index
   * @param {Array} values - Column values
   * @returns {Promise<void>}
   */
  async setColumn(col, values) {
    if (!this.initialized) {
      await this.init();
    }

    // Validate column index
    if (col < 0 || col >= this.columns) {
      throw new StorageError(
        `Invalid column index: ${col}`,
        { col, columns: this.columns },
        "STORAGE_INVALID_INDEX",
      );
    }

    // Validate values length
    if (!Array.isArray(values) || values.length !== this.rows) {
      throw new StorageError(
        `Invalid column values length: ${values.length}`,
        { values, rows: this.rows },
        "STORAGE_INVALID_SIZE",
      );
    }

    // Set column
    if (typeof this.matrix.setColumn === "function") {
      this.matrix.setColumn(col, values);
    } else {
      // Set column values individually
      for (let i = 0; i < this.rows; i++) {
        if (Array.isArray(this.matrix)) {
          this.matrix[i][col] = values[i];
        } else {
          await this.set(i, col, values[i]);
        }
      }
    }

    this.modified = true;
  }

  /**
   * Gets the entire matrix
   * @returns {Promise<Array>} Matrix data
   */
  async getMatrix() {
    if (!this.initialized) {
      await this.init();
    }

    // Return a deep copy of the matrix to prevent unintended modifications
    if (Array.isArray(this.matrix)) {
      return this.matrix.map((row) => [...row]);
    } else if (typeof this.matrix.toArray === "function") {
      return this.matrix.toArray();
    } else {
      // Construct matrix manually
      const matrix = new Array(this.rows);
      for (let i = 0; i < this.rows; i++) {
        matrix[i] = new Array(this.columns);
        for (let j = 0; j < this.columns; j++) {
          matrix[i][j] = await this.get(i, j);
        }
      }
      return matrix;
    }
  }

  /**
   * Sets the entire matrix
   * @param {Array} matrix - Matrix data
   * @returns {Promise<void>}
   */
  async setMatrix(matrix) {
    // Validate matrix
    if (!Array.isArray(matrix) || !Array.isArray(matrix[0])) {
      throw new StorageError(
        "Invalid matrix format",
        { matrixType: typeof matrix },
        "STORAGE_INVALID_MATRIX",
      );
    }

    const newRows = matrix.length;
    const newColumns = matrix[0].length;

    // If the dimensions are different, create a new matrix
    if (newRows !== this.rows || newColumns !== this.columns) {
      this.matrix = matrix.map((row) => [...row]);
      this.rows = newRows;
      this.columns = newColumns;
    } else {
      // Otherwise update the existing matrix
      if (Array.isArray(this.matrix)) {
        for (let i = 0; i < this.rows; i++) {
          this.matrix[i] = [...matrix[i]];
        }
      } else if (typeof this.matrix.setMatrix === "function") {
        this.matrix.setMatrix(matrix);
      } else {
        // Update values individually
        for (let i = 0; i < this.rows; i++) {
          for (let j = 0; j < this.columns; j++) {
            await this.set(i, j, matrix[i][j]);
          }
        }
      }
    }

    this.modified = true;
    await this.save();
  }

  /**
   * Saves changes back to storage
   * @returns {Promise<boolean>} Whether changes were saved
   */
  async save() {
    if (!this.initialized) {
      await this.init();
    }

    if (!this.modified) {
      return false;
    }

    try {
      // Save matrix back to storage
      await this.storageManager.store(this.matrix, this.storageId);
      this.modified = false;
      return true;
    } catch (error) {
      throw new StorageError(
        `Failed to save matrix: ${error.message}`,
        { id: this.storageId, originalError: error },
        "STORAGE_SAVE_FAILED",
        error,
      );
    }
  }
}

module.exports = MatrixAdapter;
