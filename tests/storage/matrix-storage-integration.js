/**
 * PrimeOS JavaScript Library - Matrix and Storage Integration Tests
 * Tests the integration between swappable Matrix and PrimeOS Matrix implementations
 */

const Prime = require('../../src');
// Make sure JEST_WORKER_ID is defined to avoid environment detection issues
process.env.JEST_WORKER_ID = process.env.JEST_WORKER_ID || '1';

describe('Matrix and Storage Integration', () => {
  let storageManager;

  beforeEach(async () => {
    storageManager = Prime.Storage.createManager();
    await storageManager.init();
    // Clean storage before each test
    await storageManager.clear();
  });

  afterEach(async () => {
    // Clean up after tests
    await storageManager.clear();
  });

  describe('SwappableMatrix and Prime.Math.Matrix', () => {
    it('should store and retrieve a standard Matrix from Prime.Math.Matrix', async () => {
      // Create a standard matrix using Prime.Math.Matrix
      const rows = 10;
      const cols = 10;
      const matrix = Prime.Math.Matrix.create(rows, cols);
      
      // Fill with test values
      for (let i = 0; i < rows; i++) {
        for (let j = 0; j < cols; j++) {
          matrix[i][j] = i * j;
        }
      }
      
      // Store the matrix
      const id = await storageManager.store(matrix, 'test-matrix');
      
      // Retrieve the matrix
      const retrievedMatrix = await storageManager.load(id);
      
      // Verify values
      for (let i = 0; i < rows; i++) {
        for (let j = 0; j < cols; j++) {
          expect(retrievedMatrix[i][j]).toBe(i * j);
        }
      }
    });

    it('should adapt SwappableMatrix to work with Prime.Math.Matrix methods', async () => {
      // Create a matrix using Prime.Math.Matrix
      const rows = 5;
      const cols = 5;
      const matrix = Prime.Math.Matrix.create(rows, cols);
      
      // Fill with test values
      for (let i = 0; i < rows; i++) {
        for (let j = 0; j < cols; j++) {
          matrix[i][j] = i * 10 + j;
        }
      }
      
      // Store the matrix
      const id = await storageManager.store(matrix, 'prime-matrix');
      
      // Create a swappable matrix
      const swappableMatrix = await Prime.Storage.createSwappableMatrix(storageManager, id, {
        blockSize: 2, // Use small blocks for testing
        maxCachedBlocks: 3
      });
      
      // Test Matrix adapter functionality
      const standardMatrix = await swappableMatrix.toMatrix();
      
      // Verify the matrix has correct values
      for (let i = 0; i < rows; i++) {
        for (let j = 0; j < cols; j++) {
          expect(standardMatrix[i][j]).toBe(i * 10 + j);
        }
      }
      
      // Test matrix operations using Prime.Math.Matrix functions
      const transposed = Prime.Math.Matrix.transpose(standardMatrix);
      
      // Verify transposition
      for (let i = 0; i < cols; i++) {
        for (let j = 0; j < rows; j++) {
          expect(transposed[i][j]).toBe(j * 10 + i);
        }
      }
    });

    it('should handle operations with both Matrix types', async () => {
      // Create two matrices using Prime.Math.Matrix
      const matrixA = Prime.Math.Matrix.create(3, 3);
      const matrixB = Prime.Math.Matrix.create(3, 3);
      
      // Fill matrices with test values
      for (let i = 0; i < 3; i++) {
        for (let j = 0; j < 3; j++) {
          matrixA[i][j] = i + j;
          matrixB[i][j] = i * j;
        }
      }
      
      // Store matrix A
      const idA = await storageManager.store(matrixA, 'matrix-a');
      
      // Create a swappable matrix for A
      const swappableA = await Prime.Storage.createSwappableMatrix(storageManager, idA, {
        blockSize: 2,
        maxCachedBlocks: 2
      });
      
      // Convert to standard matrix
      const standardA = await swappableA.toMatrix();
      
      // Add matrices
      const resultAdd = Prime.Math.Matrix.add(standardA, matrixB);
      
      // Verify addition
      for (let i = 0; i < 3; i++) {
        for (let j = 0; j < 3; j++) {
          expect(resultAdd[i][j]).toBe((i + j) + (i * j));
        }
      }
      
      // Multiply matrices
      const resultMult = Prime.Math.Matrix.multiply(standardA, matrixB);
      
      // Verify multiplication (manually calculate expected values)
      // For a 3x3 matrix multiplication
      const expected = [
        [0, 0, 0],
        [0, 1, 2],
        [0, 2, 6]
      ];
      
      for (let i = 0; i < 3; i++) {
        for (let j = 0; j < 3; j++) {
          let sum = 0;
          for (let k = 0; k < 3; k++) {
            sum += matrixA[i][k] * matrixB[k][j];
          }
          expect(resultMult[i][j]).toBeCloseTo(sum, 5);
          expect(resultMult[i][j]).toBeCloseTo(expected[i][j], 5);
        }
      }
    });

    it('should handle large matrices efficiently using SwappableMatrix', async () => {
      // Create a moderately sized matrix (not too large for the test)
      const rows = 100;
      const cols = 100;
      const matrix = Prime.Math.Matrix.create(rows, cols);
      
      // Fill with a pattern
      for (let i = 0; i < rows; i++) {
        for (let j = 0; j < cols; j++) {
          matrix[i][j] = (i * j) % 100;
        }
      }
      
      // Store the matrix
      const id = await storageManager.store(matrix, 'large-matrix');
      
      // Create a swappable matrix with small blocks to test swapping
      const swappableMatrix = await Prime.Storage.createSwappableMatrix(storageManager, id, {
        blockSize: 10,
        maxCachedBlocks: 3
      });
      
      // Access various blocks to test block loading/unloading
      const testPoints = [
        [0, 0], [5, 5], [15, 15], [25, 25], 
        [50, 50], [75, 75], [99, 99], [10, 90]
      ];
      
      // Verify all test points
      for (const [row, col] of testPoints) {
        const expected = (row * col) % 100;
        const actual = await swappableMatrix.get(row, col);
        expect(actual).toBe(expected);
      }
      
      // Modify a value and verify it persists
      await swappableMatrix.set(50, 50, 9999);
      const modified = await swappableMatrix.get(50, 50);
      expect(modified).toBe(9999);
      
      // Convert part of the matrix to standard matrix
      const subMatrix = await swappableMatrix.submatrix(40, 40, 60, 60);
      
      // Verify submatrix dimensions
      expect(subMatrix.length).toBe(20);
      expect(subMatrix[0].length).toBe(20);
      
      // Verify the modified value appears in the submatrix
      expect(subMatrix[10][10]).toBe(9999);
    });
  });
});