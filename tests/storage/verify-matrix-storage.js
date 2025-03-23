/**
 * PrimeOS JavaScript Library - Verify Matrix Storage
 * Simple verification script for matrix storage functionality
 */

const Prime = require('../../src');

async function verifyMatrixStorage() {
  console.log('# Verifying Matrix Storage Integration');
  console.log('--------------------------------------');
  
  // Create storage manager
  console.log('1. Creating storage manager...');
  const storageManager = Prime.Storage.createManager();
  await storageManager.init();
  
  // Create test matrix
  console.log('2. Creating test matrix...');
  const rows = 100;
  const cols = 100;
  const matrix = Prime.Math.Matrix.create(rows, cols);
  
  // Fill with test data
  console.log('3. Filling matrix with test data...');
  for (let i = 0; i < rows; i++) {
    for (let j = 0; j < cols; j++) {
      matrix[i][j] = (i * j) % 100;
    }
  }
  
  // Store the matrix
  console.log('4. Storing matrix in storage...');
  const id = await storageManager.store(matrix, 'test-matrix');
  console.log(`   Matrix stored with ID: ${id}`);
  
  // Create swappable matrix
  console.log('5. Creating swappable matrix from stored matrix...');
  const swappableMatrix = await Prime.Storage.createSwappableMatrix(storageManager, id, {
    blockSize: 20,
    maxCachedBlocks: 5
  });
  
  console.log('6. Verifying values from swappable matrix...');
  
  // Check some sample values
  const testCoords = [
    [0, 0], // Top-left
    [50, 50], // Middle
    [99, 99], // Bottom-right
    [25, 75], // Mixed
    [75, 25]  // Mixed
  ];
  
  let success = true;
  
  for (const [row, col] of testCoords) {
    const expected = (row * col) % 100;
    const actual = await swappableMatrix.get(row, col);
    
    if (actual !== expected) {
      console.error(`   ERROR: Value mismatch at [${row}, ${col}] - Expected: ${expected}, Got: ${actual}`);
      success = false;
    } else {
      console.log(`   ✓ Value at [${row}, ${col}] matches expected: ${actual}`);
    }
  }
  
  // Calculate trace
  console.log('7. Computing matrix trace...');
  const trace = await swappableMatrix.trace();
  
  // Calculate expected trace
  let expectedTrace = 0;
  for (let i = 0; i < Math.min(rows, cols); i++) {
    expectedTrace += (i * i) % 100;
  }
  
  if (Math.abs(trace - expectedTrace) < 0.001) {
    console.log(`   ✓ Trace matches expected: ${trace}`);
  } else {
    console.error(`   ERROR: Trace mismatch - Expected: ${expectedTrace}, Got: ${trace}`);
    success = false;
  }
  
  // Convert back to Prime.Math.Matrix
  console.log('8. Converting swappable matrix back to Prime.Math.Matrix...');
  const convertedMatrix = await swappableMatrix.toMatrix();
  
  // Verify conversion
  console.log('9. Verifying converted matrix...');
  let conversionSuccess = true;
  
  for (const [row, col] of testCoords) {
    const expected = (row * col) % 100;
    // Handle different ways to access the value based on matrix implementation
    const actual = convertedMatrix[row] ? convertedMatrix[row][col] : 
                   (convertedMatrix.get ? convertedMatrix.get(row, col) : null);
    
    if (actual !== expected) {
      console.error(`   ERROR: Conversion mismatch at [${row}, ${col}] - Expected: ${expected}, Got: ${actual}`);
      conversionSuccess = false;
      success = false;
    }
  }
  
  if (conversionSuccess) {
    console.log('   ✓ Conversion successful - values match expected');
  }
  
  // Create from existing matrix
  console.log('10. Creating swappable matrix directly from Prime.Math.Matrix...');
  const newMatrix = Prime.Math.Matrix.create(50, 50);
  for (let i = 0; i < 50; i++) {
    for (let j = 0; j < 50; j++) {
      newMatrix[i][j] = i + j;
    }
  }
  
  const directSwappable = await Prime.Storage.createSwappableMatrixFromMatrix(
    storageManager,
    newMatrix,
    'direct-matrix',
    { blockSize: 10, maxCachedBlocks: 5 }
  );
  
  // Verify direct creation
  console.log('11. Verifying directly created swappable matrix...');
  let directSuccess = true;
  
  for (let i = 0; i < 3; i++) {
    for (let j = 0; j < 3; j++) {
      const row = i * 15;
      const col = j * 15;
      const expected = row + col;
      const actual = await directSwappable.get(row, col);
      
      if (actual !== expected) {
        console.error(`   ERROR: Direct creation mismatch at [${row}, ${col}] - Expected: ${expected}, Got: ${actual}`);
        directSuccess = false;
        success = false;
      }
    }
  }
  
  if (directSuccess) {
    console.log('   ✓ Direct creation successful - values match expected');
  }
  
  // Clean up
  console.log('12. Cleaning up...');
  await storageManager.clear();
  
  // Final result
  if (success) {
    console.log('\n✅ All tests passed! Matrix storage integration verified successfully.');
  } else {
    console.error('\n❌ Tests failed! Matrix storage integration has issues.');
  }
}

// Run the verification
verifyMatrixStorage().catch(error => {
  console.error('Verification failed with error:', error);
});