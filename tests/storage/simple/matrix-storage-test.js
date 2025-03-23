/**
 * PrimeOS JavaScript Library - Simple Matrix Storage Test
 * Simplified test that focuses on the matrix storage functionality
 */

const Prime = require('../../../src');

// Function to run tests
async function runMatrixStorageTests() {
  console.log('Running Matrix Storage Tests');
  console.log('---------------------------');
  
  // Create storage manager
  console.log('1. Creating storage manager...');
  const storageManager = Prime.Storage.createManager();
  await storageManager.init();
  await storageManager.clear();
  
  // Test 1: Store and retrieve matrix
  console.log('\n2. Testing matrix storage and retrieval...');
  
  // Create a simple test matrix
  const rows = 10;
  const cols = 10;
  const matrix = Prime.Math.Matrix.create(rows, cols);
  
  // Fill with deterministic values
  for (let i = 0; i < rows; i++) {
    for (let j = 0; j < cols; j++) {
      matrix[i][j] = i * j;
    }
  }
  
  // Store the matrix
  const id = await storageManager.store(matrix, 'test-matrix');
  console.log(`   Matrix stored with ID: ${id}`);
  
  // Retrieve the matrix
  const retrievedMatrix = await storageManager.load(id);
  
  // Verify dimensions
  const dimensionsMatch = retrievedMatrix.length === rows && retrievedMatrix[0].length === cols;
  console.log(`   Dimensions match: ${dimensionsMatch ? '✓' : '❌'}`);
  
  // Verify values (check a few points)
  let valuesMatch = true;
  const testPoints = [[0, 0], [5, 5], [9, 9]];
  
  for (const [r, c] of testPoints) {
    if (retrievedMatrix[r][c] !== r * c) {
      valuesMatch = false;
      console.error(`   ERROR: Value mismatch at [${r}, ${c}] - Expected: ${r * c}, Got: ${retrievedMatrix[r][c]}`);
    }
  }
  
  console.log(`   Values match: ${valuesMatch ? '✓' : '❌'}`);
  
  // Test 2: Create SwappableMatrix
  console.log('\n3. Testing SwappableMatrix creation from stored matrix...');
  
  // Create a simple test matrix
  const rows2 = 20;
  const cols2 = 20;
  const matrix2 = Prime.Math.Matrix.create(rows2, cols2);
  
  // Fill with deterministic values
  for (let i = 0; i < rows2; i++) {
    for (let j = 0; j < cols2; j++) {
      matrix2[i][j] = i + j;
    }
  }
  
  // Store the matrix
  const id2 = await storageManager.store(matrix2, 'swappable-test');
  console.log(`   Matrix stored with ID: ${id2}`);
  
  // Create a swappable matrix
  const swappableMatrix = await Prime.Storage.createSwappableMatrix(storageManager, id2, {
    blockSize: 5,
    maxCachedBlocks: 5
  });
  
  // Verify dimensions
  const dimensionsMatch2 = swappableMatrix.getRows() === rows2 && swappableMatrix.getColumns() === cols2;
  console.log(`   Dimensions match: ${dimensionsMatch2 ? '✓' : '❌'}`);
  
  // Verify values from different blocks
  const swapTestPoints = [[0, 0], [10, 10], [19, 19]];
  const swapExpectedValues = [0, 20, 38];
  let swapValuesMatch = true;
  
  for (let i = 0; i < swapTestPoints.length; i++) {
    const [r, c] = swapTestPoints[i];
    const expected = swapExpectedValues[i];
    const actual = await swappableMatrix.get(r, c);
    
    if (actual !== expected) {
      swapValuesMatch = false;
      console.error(`   ERROR: Value mismatch at [${r}, ${c}] - Expected: ${expected}, Got: ${actual}`);
    }
  }
  
  console.log(`   Values match: ${swapValuesMatch ? '✓' : '❌'}`);
  
  // Test trace calculation
  const trace = await swappableMatrix.trace();
  
  // Calculate expected trace
  let expectedTrace = 0;
  for (let i = 0; i < Math.min(rows2, cols2); i++) {
    expectedTrace += i + i;
  }
  
  const traceMatches = Math.abs(trace - expectedTrace) < 0.001;
  console.log(`   Trace calculation: ${traceMatches ? '✓' : '❌'} (Expected: ${expectedTrace}, Got: ${trace})`);
  
  // Test 3: Direct creation
  console.log('\n4. Testing direct SwappableMatrix creation...');
  
  // Create a simple test matrix
  const rows3 = 15;
  const cols3 = 15;
  const matrix3 = Prime.Math.Matrix.create(rows3, cols3);
  
  // Fill with deterministic values
  for (let i = 0; i < rows3; i++) {
    for (let j = 0; j < cols3; j++) {
      matrix3[i][j] = i * j;
    }
  }
  
  // Create swappable matrix directly
  const directSwappable = await Prime.Storage.createSwappableMatrixFromMatrix(
    storageManager,
    matrix3,
    'direct-swappable',
    {
      blockSize: 5,
      maxCachedBlocks: 5
    }
  );
  
  // Verify dimensions
  const dimensionsMatch3 = directSwappable.getRows() === rows3 && directSwappable.getColumns() === cols3;
  console.log(`   Dimensions match: ${dimensionsMatch3 ? '✓' : '❌'}`);
  
  // Verify values
  const directTestPoints = [[0, 0], [7, 7], [14, 14]];
  const directExpectedValues = [0, 49, 196];
  let directValuesMatch = true;
  
  for (let i = 0; i < directTestPoints.length; i++) {
    const [r, c] = directTestPoints[i];
    const expected = directExpectedValues[i];
    const actual = await directSwappable.get(r, c);
    
    if (actual !== expected) {
      directValuesMatch = false;
      console.error(`   ERROR: Value mismatch at [${r}, ${c}] - Expected: ${expected}, Got: ${actual}`);
    }
  }
  
  console.log(`   Values match: ${directValuesMatch ? '✓' : '❌'}`);
  
  // Convert back to matrix
  const convertedMatrix = await directSwappable.toMatrix();
  
  // Verify converted matrix dimensions
  const convDimensionsMatch = convertedMatrix.length === rows3 && convertedMatrix[0].length === cols3;
  console.log(`   Converted matrix dimensions match: ${convDimensionsMatch ? '✓' : '❌'}`);
  
  // Verify values in converted matrix (check a few points)
  let convValuesMatch = true;
  const convTestPoints = [[0, 0], [7, 7], [14, 14]];
  
  for (const [r, c] of convTestPoints) {
    const expected = r * c;
    const actual = convertedMatrix[r] ? convertedMatrix[r][c] : null;
    
    if (actual !== expected) {
      convValuesMatch = false;
      console.error(`   ERROR: Conversion mismatch at [${r}, ${c}] - Expected: ${expected}, Got: ${actual}`);
    }
  }
  
  console.log(`   Converted matrix values match: ${convValuesMatch ? '✓' : '❌'}`);
  
  // Clean up
  console.log('\n5. Cleaning up...');
  await storageManager.clear();
  
  // Final result
  const allPassed = dimensionsMatch && valuesMatch && 
                    dimensionsMatch2 && swapValuesMatch && traceMatches &&
                    dimensionsMatch3 && directValuesMatch && 
                    convDimensionsMatch && convValuesMatch;
  
  console.log('\n--------------------------');
  console.log(`Test ${allPassed ? 'PASSED ✅' : 'FAILED ❌'}`);
  
  return allPassed;
}

// Check if running as a module or directly
if (require.main === module) {
  // Running as a script
  runMatrixStorageTests().catch(error => {
    console.error('Tests failed with error:', error);
    process.exit(1);
  });
} else {
  // Running as a module, export test functions for jest
  module.exports = { runMatrixStorageTests };
}