/**
 * PrimeOS Unit Tests - Tensor Storage Adapter
 * 
 * Tests for the SwappableTensor adapter in the Storage module.
 */

const Prime = require('../../../src');
const { Assertions } = require('../../utils');

describe('Swappable Tensor', () => {
  let storageManager;
  let swappableTensor;
  
  beforeEach(async () => {
    // Create storage manager and initialize
    storageManager = Prime.Storage.createManager();
    await storageManager.init();
    
    // Create a 3D tensor
    const dim1 = 10;
    const dim2 = 10;
    const dim3 = 10;
    const tensor = [];
    
    for (let i = 0; i < dim1; i++) {
      tensor[i] = [];
      for (let j = 0; j < dim2; j++) {
        tensor[i][j] = [];
        for (let k = 0; k < dim3; k++) {
          tensor[i][j][k] = i * 100 + j * 10 + k;
        }
      }
    }
    
    // Store the tensor
    const id = await storageManager.store(tensor, 'test-tensor');
    
    // Create swappable tensor
    swappableTensor = await Prime.Storage.createSwappableTensor(storageManager, id, {
      blockSize: 4,  // 4x4x4 blocks
      maxCachedBlocks: 5  // Keep only 5 blocks in memory at once
    });
  });
  
  test('should provide tensor shape', () => {
    const shape = swappableTensor.getShape();
    expect(shape).toEqual([10, 10, 10]);
  });
  
  test('should get individual tensor elements', async () => {
    expect(await swappableTensor.get(0, 0, 0)).toBe(0);
    expect(await swappableTensor.get(1, 2, 3)).toBe(123);
    expect(await swappableTensor.get(9, 9, 9)).toBe(999);
  });
  
  test('should get tensor blocks efficiently', async () => {
    // Get elements from the same block
    const val1 = await swappableTensor.get(1, 1, 1);
    const val2 = await swappableTensor.get(1, 1, 2);
    const val3 = await swappableTensor.get(1, 2, 1);
    
    expect(val1).toBe(111);
    expect(val2).toBe(112);
    expect(val3).toBe(121);
    
    // Check block cache stats
    expect(swappableTensor.getCacheStats().hits).toBeGreaterThan(0);
  });
  
  test('should handle cache eviction when accessing different blocks', async () => {
    // Access elements in different blocks to trigger cache eviction
    for (let i = 0; i < 3; i++) {
      for (let j = 0; j < 3; j++) {
        for (let k = 0; k < 3; k++) {
          const blockX = i * 4;
          const blockY = j * 4;
          const blockZ = k * 4;
          // Ensure coordinates are within bounds
          if (blockX < 10 && blockY < 10 && blockZ < 10) {
            await swappableTensor.get(blockX, blockY, blockZ);
          }
        }
      }
    }
    
    // Should have had some cache misses
    expect(swappableTensor.getCacheStats().misses).toBeGreaterThan(0);
    
    // Cache should not exceed max size
    expect(swappableTensor.getCacheStats().size).toBeLessThanOrEqual(5);
  });
  
  test('should set individual tensor elements', async () => {
    await swappableTensor.set([5, 5, 5], 999);
    
    expect(await swappableTensor.get(5, 5, 5)).toBe(999);
  });
  
  test('should perform tensor operations correctly', async () => {
    // Calculate partial sum of a small block
    let sum = 0;
    for (let i = 0; i < 3; i++) {
      for (let j = 0; j < 3; j++) {
        for (let k = 0; k < 3; k++) {
          sum += await swappableTensor.get(i, j, k);
        }
      }
    }
    
    // Expected sum calculation
    let expectedSum = 0;
    for (let i = 0; i < 3; i++) {
      for (let j = 0; j < 3; j++) {
        for (let k = 0; k < 3; k++) {
          expectedSum += i * 100 + j * 10 + k;
        }
      }
    }
    
    expect(sum).toBe(expectedSum);
  });
  
  test('should get subtensor', async () => {
    const ranges = [[2, 4], [3, 5], [1, 3]];
    const subtensor = await swappableTensor.getSubtensor(ranges);
    
    // Check dimensions
    expect(subtensor.length).toBe(2);
    expect(subtensor[0].length).toBe(2);
    expect(subtensor[0][0].length).toBe(2);
    
    // Check values
    expect(subtensor[0][0][0]).toBe(231);
    expect(subtensor[1][1][1]).toBe(342);
  });
  
  test('should map function over tensor elements', async () => {
    // Map function to double all values in a small section
    const mappedTensor = await swappableTensor.map((value) => value * 2);
    
    // Check a few values
    expect(mappedTensor[1][2][3]).toBe(246); // 123 * 2
    expect(mappedTensor[5][5][5]).toBe(1110); // 555 * 2
  });
  
  test('should perform element-wise operations between tensors', async () => {
    // Create another tensor with the same shape but different values
    const otherTensor = [];
    for (let i = 0; i < 10; i++) {
      otherTensor[i] = [];
      for (let j = 0; j < 10; j++) {
        otherTensor[i][j] = [];
        for (let k = 0; k < 10; k++) {
          otherTensor[i][j][k] = i + j + k;
        }
      }
    }
    
    // Store the other tensor
    const otherId = await storageManager.store(otherTensor, 'other-tensor');
    const otherSwappableTensor = await Prime.Storage.createSwappableTensor(storageManager, otherId);
    
    // Perform element-wise addition
    const sumTensor = await swappableTensor.add(otherSwappableTensor);
    
    // Check a few values
    expect(sumTensor[1][2][3]).toBe(123 + 6); // 1 + 2 + 3 = 6
    expect(sumTensor[5][5][5]).toBe(555 + 15); // 5 + 5 + 5 = 15
  });
  
  test('should support tensor contraction', async () => {
    // Contract dimension 2 of a small subtensor
    const smallTensor = await swappableTensor.getSubtensor([[0, 3], [0, 3], [0, 3]]);
    const otherSwappableTensor = await Prime.Storage.createSwappableTensor(
      storageManager, 
      await storageManager.store(smallTensor, 'small-tensor')
    );
    
    // Contract last dimension
    const contracted = await otherSwappableTensor.contract(2);
    
    // Check shape and values
    expect(contracted.length).toBe(3);
    expect(contracted[0].length).toBe(3);
    
    // Verify sums for a few values
    // Sum of [0,0,0], [0,0,1], [0,0,2] = 0 + 1 + 2 = 3
    expect(contracted[0][0]).toBe(3);
    
    // Sum of [1,1,0], [1,1,1], [1,1,2] = 110 + 111 + 112 = 333
    expect(contracted[1][1]).toBe(333);
  });
  
  test('should reshape tensor to different dimensions', async () => {
    // Reshape a subtensor from [3,3,3] to [9,3]
    const smallTensor = await swappableTensor.getSubtensor([[0, 3], [0, 3], [0, 3]]);
    const otherSwappableTensor = await Prime.Storage.createSwappableTensor(
      storageManager, 
      await storageManager.store(smallTensor, 'small-tensor')
    );
    
    const reshaped = await otherSwappableTensor.reshape([9, 3]);
    
    // Check shape
    expect(reshaped.length).toBe(9);
    expect(reshaped[0].length).toBe(3);
    
    // Check that values are correctly placed
    // First row should be the flattened version of [0,0,0], [0,0,1], [0,0,2]
    expect(reshaped[0]).toEqual([0, 1, 2]);
    
    // Last row should be the flattened version of [2,2,0], [2,2,1], [2,2,2]
    expect(reshaped[8]).toEqual([220, 221, 222]);
  });
  
  test('should transpose tensor dimensions', async () => {
    // Create a small asymmetric tensor for clearer testing
    const asymTensor = [
      [
        [1, 2, 3],
        [4, 5, 6]
      ],
      [
        [7, 8, 9],
        [10, 11, 12]
      ]
    ];
    
    const asymId = await storageManager.store(asymTensor, 'asym-tensor');
    const asymSwappableTensor = await Prime.Storage.createSwappableTensor(storageManager, asymId);
    
    // Transpose dimensions 0 and 2
    const transposed = await asymSwappableTensor.transpose([2, 1, 0]);
    
    // Check shape
    expect(transposed.length).toBe(3);
    expect(transposed[0].length).toBe(2);
    expect(transposed[0][0].length).toBe(2);
    
    // Check values
    expect(transposed[0][0][0]).toBe(1); // Was [0,0,0]
    expect(transposed[0][0][1]).toBe(7); // Was [1,0,0]
    expect(transposed[0][1][0]).toBe(4); // Was [0,1,0]
    expect(transposed[2][1][1]).toBe(12); // Was [1,1,2]
  });
  
  test('should calculate matrix multiplication along last dimensions', async () => {
    // Create tensor A with shape [2,3,4]
    const tensorA = [];
    for (let i = 0; i < 2; i++) {
      tensorA[i] = [];
      for (let j = 0; j < 3; j++) {
        tensorA[i][j] = [];
        for (let k = 0; k < 4; k++) {
          tensorA[i][j][k] = i * 100 + j * 10 + k;
        }
      }
    }
    
    // Create tensor B with shape [2,4,2]
    const tensorB = [];
    for (let i = 0; i < 2; i++) {
      tensorB[i] = [];
      for (let j = 0; j < 4; j++) {
        tensorB[i][j] = [];
        for (let k = 0; k < 2; k++) {
          tensorB[i][j][k] = i * 10 + j * 2 + k;
        }
      }
    }
    
    const idA = await storageManager.store(tensorA, 'tensor-a');
    const idB = await storageManager.store(tensorB, 'tensor-b');
    
    const swappableA = await Prime.Storage.createSwappableTensor(storageManager, idA);
    const swappableB = await Prime.Storage.createSwappableTensor(storageManager, idB);
    
    // Perform matrix multiplication along last dimensions
    const resultTensor = await swappableA.matmul(swappableB);
    
    // Check shape of result
    expect(resultTensor.length).toBe(2);
    expect(resultTensor[0].length).toBe(3);
    expect(resultTensor[0][0].length).toBe(2);
    
    // Manually calculate one value as verification
    // resultTensor[0][1][0] = sum(tensorA[0][1][k] * tensorB[0][k][0]) for k=0..3
    const expected = 
      tensorA[0][1][0] * tensorB[0][0][0] +
      tensorA[0][1][1] * tensorB[0][1][0] +
      tensorA[0][1][2] * tensorB[0][2][0] +
      tensorA[0][1][3] * tensorB[0][3][0];
    
    expect(resultTensor[0][1][0]).toBe(expected);
  });
});