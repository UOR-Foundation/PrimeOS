/**
 * PrimeOS JavaScript Library - Browser Matrix Storage Tests
 * Tests the integration between Matrix and Storage in browser environments
 */

// This file will be included in the browser test environment
// Define tests that will run in the browser using the TestRunner global object

// Store a reference to the browser's TestRunner if available
const BrowserTestRunner = typeof TestRunner !== 'undefined' ? TestRunner : null;

// Define browser storage tests for Matrix operations
function defineStorageMatrixTests() {
  if (!BrowserTestRunner) {
    // Skip tests if not in browser or TestRunner not available
    return;
  }

  BrowserTestRunner.suite('Storage Matrix Integration (Browser)', function() {
    // Matrix integration test
    BrowserTestRunner.test('SwappableMatrix works with Prime.Math.Matrix in browser', async function() {
      // Basic validation
      BrowserTestRunner.assert(Prime.Storage !== undefined, 'Storage module should be available');
      BrowserTestRunner.assert(Prime.Math.Matrix !== undefined, 'Matrix module should be available');
      
      // Create storage manager with IndexedDB
      const storageManager = Prime.Storage.createManager({ provider: 'indexeddb' });
      await storageManager.init();
      await storageManager.clear(); // Clean up previous test data
      
      // Create a test matrix
      const rows = 20;
      const cols = 20;
      const matrix = Prime.Math.Matrix.create(rows, cols);
      
      // Fill with test data
      for (let i = 0; i < rows; i++) {
        for (let j = 0; j < cols; j++) {
          matrix[i][j] = i * j;
        }
      }
      
      // Store the matrix
      const matrixId = await storageManager.store(matrix, 'browser-test-matrix');
      
      // Create swappable matrix
      const swappableMatrix = await Prime.Storage.createSwappableMatrix(storageManager, matrixId, {
        blockSize: 5,
        maxCachedBlocks: 3
      });
      
      // Verify matrix dimensions
      BrowserTestRunner.assertEqual(swappableMatrix.getRows(), rows);
      BrowserTestRunner.assertEqual(swappableMatrix.getColumns(), cols);
      
      // Test retrieving values
      const testValue = await swappableMatrix.get(5, 10);
      BrowserTestRunner.assertEqual(testValue, 5 * 10);
      
      // Test setting values
      await swappableMatrix.set(5, 10, 999);
      const updatedValue = await swappableMatrix.get(5, 10);
      BrowserTestRunner.assertEqual(updatedValue, 999);
      
      // Convert to standard matrix
      const standardMatrix = await swappableMatrix.toMatrix();
      BrowserTestRunner.assert(standardMatrix !== undefined);
      BrowserTestRunner.assertEqual(standardMatrix.length, rows);
      BrowserTestRunner.assertEqual(standardMatrix[0].length, cols);
      BrowserTestRunner.assertEqual(standardMatrix[5][10], 999);
    });
    
    BrowserTestRunner.test('IndexedDB persistence with Matrix operations', async function() {
      // Create storage manager
      const storageManager = Prime.Storage.createManager({ provider: 'indexeddb' });
      await storageManager.init();
      
      // Create a small matrix
      const matrix = Prime.Math.Matrix.create(5, 5);
      for (let i = 0; i < 5; i++) {
        for (let j = 0; j < 5; j++) {
          matrix[i][j] = i + j * 10;
        }
      }
      
      // Store with a fixed key for retrieval
      const key = 'persistence-test-matrix';
      await storageManager.store(matrix, key);
      
      // Create a new storage manager to simulate page reload
      const newStorageManager = Prime.Storage.createManager({ provider: 'indexeddb' });
      await newStorageManager.init();
      
      // Retrieve the matrix
      const retrievedMatrix = await newStorageManager.load(key);
      
      // Verify the matrix was correctly persisted
      BrowserTestRunner.assert(retrievedMatrix !== undefined);
      BrowserTestRunner.assertEqual(retrievedMatrix.length, 5);
      BrowserTestRunner.assertEqual(retrievedMatrix[0].length, 5);
      
      // Check some values
      BrowserTestRunner.assertEqual(retrievedMatrix[2][3], 2 + 3 * 10);
      
      // Clean up
      await newStorageManager.remove(key);
    });
    
    BrowserTestRunner.test('Matrix operations with browser storage', async function() {
      // Create storage manager
      const storageManager = Prime.Storage.createManager({ provider: 'indexeddb' });
      await storageManager.init();
      await storageManager.clear(); // Clean up previous test data
      
      // Create two matrices
      const matrixA = Prime.Math.Matrix.create(3, 3);
      const matrixB = Prime.Math.Matrix.create(3, 3);
      
      // Fill with data
      for (let i = 0; i < 3; i++) {
        for (let j = 0; j < 3; j++) {
          matrixA[i][j] = i + j;
          matrixB[i][j] = i * j;
        }
      }
      
      // Store matrices
      const idA = await storageManager.store(matrixA, 'matrix-a');
      const idB = await storageManager.store(matrixB, 'matrix-b');
      
      // Create swappable matrices
      const swappableA = await Prime.Storage.createSwappableMatrix(storageManager, idA);
      const swappableB = await Prime.Storage.createSwappableMatrix(storageManager, idB);
      
      // Convert to standard matrices for operations
      const standardA = await swappableA.toMatrix();
      const standardB = await swappableB.toMatrix();
      
      // Perform operations
      const addResult = Prime.Math.Matrix.add(standardA, standardB);
      
      // Verify the result
      BrowserTestRunner.assert(addResult !== undefined);
      
      // Test some values in the result
      for (let i = 0; i < 3; i++) {
        for (let j = 0; j < 3; j++) {
          const expectedSum = (i + j) + (i * j);
          BrowserTestRunner.assertEqual(addResult[i][j], expectedSum);
        }
      }
      
      // Clean up
      await storageManager.remove(idA);
      await storageManager.remove(idB);
    });
  });
}

// Add the storage matrix tests to the runner if in browser
if (typeof document !== 'undefined' && BrowserTestRunner) {
  document.addEventListener('DOMContentLoaded', function() {
    // Define the storage matrix tests
    defineStorageMatrixTests();
    
    // Add to the run-all button handler
    const originalRunAll = document.getElementById('run-all').onclick;
    document.getElementById('run-all').onclick = async function() {
      if (typeof originalRunAll === 'function') {
        await originalRunAll();
      }
      defineStorageMatrixTests();
      await BrowserTestRunner.run({ suite: 'Storage Matrix Integration (Browser)' });
    };
    
    // Add a dedicated button for storage tests if it doesn't exist
    if (!document.getElementById('run-storage')) {
      const testRunner = document.getElementById('test-runner');
      if (testRunner) {
        const storageButton = document.createElement('button');
        storageButton.id = 'run-storage';
        storageButton.textContent = 'Run Storage Tests';
        storageButton.onclick = async function() {
          BrowserTestRunner.reset();
          defineStorageMatrixTests();
          await BrowserTestRunner.run({ suite: 'Storage Matrix Integration (Browser)' });
        };
        testRunner.appendChild(storageButton);
      }
    }
  });
}

// If not in a browser, provide a CommonJS export
if (typeof module !== 'undefined' && module.exports) {
  module.exports = {
    defineStorageMatrixTests
  };
}

// Add Jest test for Node.js environment
describe('Browser Matrix Storage Tests - Node.js Environment', () => {
  it('should skip browser-specific tests in Node.js environment', () => {
    // This test exists only to prevent the "no tests" error in Jest
    expect(true).toBe(true);
  });
});