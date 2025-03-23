/**
 * Simple test script for PrimeOS Storage
 * This script directly tests the storage functionality without Jest
 */

const Prime = require('../../src');

async function runTest() {
  console.log('Testing PrimeOS Storage...');
  
  // Verify the Storage module exists
  if (!Prime.Storage) {
    console.error('Error: Storage module not found in Prime object');
    process.exit(1);
  }
  
  console.log('✓ Storage module exists');
  
  // Create a storage manager
  const storageManager = Prime.Storage.createManager();
  
  try {
    // Initialize the storage manager
    await storageManager.init();
    console.log('✓ Storage manager initialized');
    
    // Store data
    const testData = { 
      test: 'value', 
      nested: { obj: true }, 
      array: [1, 2, 3, 4, 5] 
    };
    const id = await storageManager.store(testData, 'test-data');
    console.log(`✓ Data stored with ID: ${id}`);
    
    // Load data
    const loadedData = await storageManager.load(id);
    console.log('✓ Data loaded successfully');
    
    // Verify data is correct
    if (JSON.stringify(loadedData) !== JSON.stringify(testData)) {
      console.error('Error: Loaded data does not match stored data');
      console.log('Original:', testData);
      console.log('Loaded:', loadedData);
      process.exit(1);
    }
    console.log('✓ Loaded data matches stored data');
    
    // Test Matrix functionality
    if (Prime.Math && Prime.Math.Matrix) {
      console.log('\nTesting Matrix integration...');
      
      // Create a matrix
      const rows = 5;
      const cols = 5;
      const matrix = Prime.Math.Matrix.create(rows, cols);
      
      // Fill with test data
      for (let i = 0; i < rows; i++) {
        for (let j = 0; j < cols; j++) {
          matrix[i][j] = i * j;
        }
      }
      
      // Store the matrix
      const matrixId = await storageManager.store(matrix, 'test-matrix');
      console.log(`✓ Matrix stored with ID: ${matrixId}`);
      
      // Load the matrix
      const loadedMatrix = await storageManager.load(matrixId);
      console.log('✓ Matrix loaded successfully');
      
      // Verify matrix dimensions
      if (loadedMatrix.length !== rows || loadedMatrix[0].length !== cols) {
        console.error('Error: Loaded matrix dimensions do not match');
        console.log('Expected:', rows, 'x', cols);
        console.log('Got:', loadedMatrix.length, 'x', loadedMatrix[0].length);
        process.exit(1);
      }
      console.log('✓ Matrix dimensions correct');
      
      // Verify matrix values
      let valuesCorrect = true;
      for (let i = 0; i < rows; i++) {
        for (let j = 0; j < cols; j++) {
          if (loadedMatrix[i][j] !== i * j) {
            valuesCorrect = false;
            console.error(`Error: Matrix value at [${i}][${j}] is ${loadedMatrix[i][j]}, expected ${i * j}`);
          }
        }
      }
      
      if (valuesCorrect) {
        console.log('✓ Matrix values correct');
      } else {
        process.exit(1);
      }
      
      // Test SwappableMatrix if available
      if (Prime.Storage.createSwappableMatrix) {
        try {
          const swappableMatrix = await Prime.Storage.createSwappableMatrix(storageManager, matrixId, {
            blockSize: 2,
            maxCachedBlocks: 3
          });
          
          console.log('✓ SwappableMatrix created');
          
          // Test getting a value
          const testValue = await swappableMatrix.get(2, 3);
          if (testValue === 2 * 3) {
            console.log('✓ SwappableMatrix.get works correctly');
          } else {
            console.error(`Error: SwappableMatrix.get returned ${testValue}, expected ${2 * 3}`);
            process.exit(1);
          }
          
          // Test setting a value
          await swappableMatrix.set(2, 3, 999);
          const updatedValue = await swappableMatrix.get(2, 3);
          if (updatedValue === 999) {
            console.log('✓ SwappableMatrix.set works correctly');
          } else {
            console.error(`Error: SwappableMatrix.set didn't work, got ${updatedValue}, expected 999`);
            process.exit(1);
          }
        } catch (err) {
          console.error('Error testing SwappableMatrix:', err);
          process.exit(1);
        }
      } else {
        console.log('⚠ SwappableMatrix not available, skipping test');
      }
    } else {
      console.log('⚠ Matrix module not available, skipping Matrix tests');
    }
    
    // Clean up
    console.log('\nCleaning up...');
    await storageManager.clear();
    console.log('✓ Storage cleared');
    
    console.log('\n✅ All tests passed successfully!');
  } catch (error) {
    console.error('Error during test:', error);
    process.exit(1);
  }
}

// Run the tests
runTest();