/**
 * PrimeOS - SwappableTensor Example
 * 
 * This example demonstrates the use of SwappableTensor for large tensor operations.
 */

const Prime = require('../src');

async function runTensorExample() {
  console.log('=== PrimeOS SwappableTensor Example ===');
  
  // Create a storage manager
  const storageManager = Prime.Storage.createManager();
  await storageManager.init();
  
  console.log('Creating sample tensors...');
  
  // Create a 3D tensor (5x5x5)
  const size = 5;
  const tensorA = [];
  for (let i = 0; i < size; i++) {
    tensorA[i] = [];
    for (let j = 0; j < size; j++) {
      tensorA[i][j] = [];
      for (let k = 0; k < size; k++) {
        tensorA[i][j][k] = i * 100 + j * 10 + k;
      }
    }
  }
  
  // Create another tensor for operations
  const tensorB = [];
  for (let i = 0; i < size; i++) {
    tensorB[i] = [];
    for (let j = 0; j < size; j++) {
      tensorB[i][j] = [];
      for (let k = 0; k < size; k++) {
        tensorB[i][j][k] = i + j + k;
      }
    }
  }
  
  // Store the tensors
  const idA = await storageManager.store(tensorA, 'tensor-a');
  const idB = await storageManager.store(tensorB, 'tensor-b');
  
  // Create swappable tensors
  console.log('Creating SwappableTensor instances...');
  const swappableA = await Prime.Storage.createSwappableTensor(storageManager, idA, {
    blockSize: 2,  // 2x2x2 blocks
    maxCachedBlocks: 3  // Keep only 3 blocks in memory at once
  });
  
  const swappableB = await Prime.Storage.createSwappableTensor(storageManager, idB, {
    blockSize: 2,
    maxCachedBlocks: 3
  });
  
  // Display tensor information
  console.log('\nTensor A Shape:', swappableA.getShape());
  console.log('Tensor B Shape:', swappableB.getShape());
  
  // Perform operations
  console.log('\nPerforming tensor operations...');
  
  // 1. Element access
  console.log('\n1. Element access:');
  console.log('Tensor A[1,2,3] =', await swappableA.get(1, 2, 3));
  console.log('Tensor B[1,2,3] =', await swappableB.get(1, 2, 3));
  
  // 2. Element-wise operations
  console.log('\n2. Element-wise operations:');
  console.log('Adding tensors...');
  const sumTensor = await swappableA.add(swappableB);
  console.log('Sum[1,2,3] =', sumTensor[1][2][3], '(Expected:', tensorA[1][2][3] + tensorB[1][2][3], ')');
  
  console.log('Multiplying tensors...');
  const productTensor = await swappableA.multiply(swappableB);
  console.log('Product[1,2,3] =', productTensor[1][2][3], '(Expected:', tensorA[1][2][3] * tensorB[1][2][3], ')');
  
  // 3. Subtensor extraction
  console.log('\n3. Subtensor extraction:');
  const subtensor = await swappableA.getSubtensor([[1, 3], [1, 3], [1, 3]]);
  console.log('Subtensor shape:', [subtensor.length, subtensor[0].length, subtensor[0][0].length]);
  console.log('Subtensor[0,0,0] =', subtensor[0][0][0], '(Expected:', tensorA[1][1][1], ')');
  
  // 4. Tensor contraction
  console.log('\n4. Tensor contraction:');
  const contracted = await swappableA.contract(2); // Contract last dimension
  console.log('Contracted tensor shape:', [contracted.length, contracted[0].length]);
  
  // Calculate expected value for comparison
  let expectedSum = 0;
  for (let k = 0; k < size; k++) {
    expectedSum += tensorA[1][2][k];
  }
  console.log('Contracted[1,2] =', contracted[1][2], '(Expected:', expectedSum, ')');
  
  // 5. Tensor reshaping
  console.log('\n5. Tensor reshaping:');
  const reshaped = await swappableA.reshape([5, 25]);
  console.log('Reshaped tensor shape:', [reshaped.length, reshaped[0].length]);
  console.log('Reshaped[1,12] =', reshaped[1][12], '(Original position in 3D tensor)');
  
  // 6. Matrix multiplication
  console.log('\n6. Matrix multiplication:');
  // Create tensors suitable for matrix multiplication
  const matrixA = [];
  const matrixB = [];
  
  // A: 2x3x4
  for (let i = 0; i < 2; i++) {
    matrixA[i] = [];
    for (let j = 0; j < 3; j++) {
      matrixA[i][j] = [];
      for (let k = 0; k < 4; k++) {
        matrixA[i][j][k] = i * 100 + j * 10 + k;
      }
    }
  }
  
  // B: 2x4x2
  for (let i = 0; i < 2; i++) {
    matrixB[i] = [];
    for (let j = 0; j < 4; j++) {
      matrixB[i][j] = [];
      for (let k = 0; k < 2; k++) {
        matrixB[i][j][k] = i * 10 + j * 2 + k;
      }
    }
  }
  
  const idMatA = await storageManager.store(matrixA, 'matrix-a');
  const idMatB = await storageManager.store(matrixB, 'matrix-b');
  
  const swappableMatA = await Prime.Storage.createSwappableTensor(storageManager, idMatA);
  const swappableMatB = await Prime.Storage.createSwappableTensor(storageManager, idMatB);
  
  const matmulResult = await swappableMatA.matmul(swappableMatB);
  console.log('Matrix multiplication result shape:', [
    matmulResult.length, 
    matmulResult[0].length, 
    matmulResult[0][0].length
  ]);
  console.log('Result[0,1,0] =', matmulResult[0][1][0]);
  
  // 7. Performance metrics
  console.log('\n7. Cache statistics:');
  console.log('Tensor A cache stats:', swappableA.getCacheStats());
  console.log('Tensor B cache stats:', swappableB.getCacheStats());
  
  console.log('\nExample completed successfully!');
}

// Run the example
runTensorExample().catch(error => {
  console.error('Error in tensor example:', error);
});