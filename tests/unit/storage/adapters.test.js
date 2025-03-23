/**
 * PrimeOS Unit Tests - Storage Adapters
 *
 * Tests for the storage adapter components in the Storage module.
 */

const Prime = require("../../../src");
const { Assertions } = require("../../utils");

describe("Storage Adapters", () => {
  describe("Data Provider", () => {
    let storageManager;
    let dataProvider;

    beforeEach(async () => {
      // Create storage manager and initialize
      storageManager = Prime.Storage.createManager();
      await storageManager.init();

      // Create and store test data
      const inputs = [
        [1, 2, 3],
        [4, 5, 6],
        [7, 8, 9],
        [10, 11, 12],
        [13, 14, 15],
      ];

      const outputs = [
        [0.1, 0.2],
        [0.3, 0.4],
        [0.5, 0.6],
        [0.7, 0.8],
        [0.9, 1.0],
      ];

      const inputId = await storageManager.store(inputs, "test-inputs");
      const outputId = await storageManager.store(outputs, "test-outputs");

      // Create data provider
      dataProvider = Prime.Storage.createDataProvider(storageManager, {
        inputId,
        outputId,
        batchSize: 2,
      });

      await dataProvider.init();
    });

    test("should return correct data shapes", async () => {
      expect(dataProvider.getInputShape()).toEqual([3]);
      expect(dataProvider.getOutputShape()).toEqual([2]);
      expect(dataProvider.getDatasetSize()).toBe(5);
      expect(dataProvider.getBatchCount()).toBe(3); // 5 items with batch size 2 = 3 batches
    });

    test("should iterate through batches correctly", async () => {
      const batches = [];

      for (let i = 0; i < dataProvider.getBatchCount(); i++) {
        const batch = await dataProvider.getBatch(i);
        batches.push(batch);
      }

      // Check first batch
      expect(batches[0].inputs.length).toBe(2);
      expect(batches[0].outputs.length).toBe(2);
      expect(batches[0].inputs[0]).toEqual([1, 2, 3]);
      expect(batches[0].outputs[0]).toEqual([0.1, 0.2]);

      // Check last batch
      expect(batches[2].inputs.length).toBe(1); // Last batch has only 1 item
      expect(batches[2].inputs[0]).toEqual([13, 14, 15]);
      expect(batches[2].outputs[0]).toEqual([0.9, 1.0]);
    });

    test("should reset iteration state", async () => {
      await dataProvider.getBatch(0);
      await dataProvider.getBatch(1);

      // Reset
      await dataProvider.reset();

      // Get first batch again
      const batch = await dataProvider.getBatch(0);
      expect(batch.inputs[0]).toEqual([1, 2, 3]);
    });

    test("should provide random batches", async () => {
      const batch = await dataProvider.getRandomBatch();

      // Should return a valid batch
      expect(batch.inputs.length).toBe(2);
      expect(batch.outputs.length).toBe(2);

      // Each item should be from the original dataset
      const validInputs = [
        [1, 2, 3],
        [4, 5, 6],
        [7, 8, 9],
        [10, 11, 12],
        [13, 14, 15],
      ];

      for (const input of batch.inputs) {
        // Check if input is one of the valid inputs
        const foundMatch = validInputs.some((validInput) =>
          validInput.every((val, idx) => val === input[idx]),
        );
        expect(foundMatch).toBe(true);
      }
    });
  });

  describe("Matrix Adapter", () => {
    let storageManager;
    let matrix;
    let matrixAdapter;

    beforeEach(async () => {
      // Create storage manager and initialize
      storageManager = Prime.Storage.createManager();
      await storageManager.init();

      // Create a test matrix
      matrix = [
        [1, 2, 3, 4],
        [5, 6, 7, 8],
        [9, 10, 11, 12],
      ];

      // Store the matrix
      const id = await storageManager.store(matrix, "test-matrix");

      // Create matrix adapter
      matrixAdapter = await Prime.Storage.createMatrixAdapter(
        storageManager,
        id,
      );
    });

    test("should provide matrix dimensions", () => {
      expect(matrixAdapter.rows).toBe(3);
      expect(matrixAdapter.columns).toBe(4);
    });

    test("should get individual matrix elements", async () => {
      expect(await matrixAdapter.get(0, 0)).toBe(1);
      expect(await matrixAdapter.get(1, 2)).toBe(7);
      expect(await matrixAdapter.get(2, 3)).toBe(12);
    });

    test("should get matrix rows", async () => {
      const row0 = await matrixAdapter.getRow(0);
      const row2 = await matrixAdapter.getRow(2);

      expect(row0).toEqual([1, 2, 3, 4]);
      expect(row2).toEqual([9, 10, 11, 12]);
    });

    test("should get matrix columns", async () => {
      const col1 = await matrixAdapter.getColumn(1);
      const col3 = await matrixAdapter.getColumn(3);

      expect(col1).toEqual([2, 6, 10]);
      expect(col3).toEqual([4, 8, 12]);
    });

    test("should set individual matrix elements", async () => {
      await matrixAdapter.set(1, 1, 42);

      expect(await matrixAdapter.get(1, 1)).toBe(42);

      // Original matrix should be unaffected (until saved)
      expect(matrix[1][1]).toBe(6);
    });

    test("should save changes back to storage", async () => {
      // Make changes
      await matrixAdapter.set(0, 0, 99);
      await matrixAdapter.set(2, 3, 88);

      // Save changes
      await matrixAdapter.save();

      // Create a new adapter to the same matrix
      const newAdapter = await Prime.Storage.createMatrixAdapter(
        storageManager,
        matrixAdapter.storageId,
      );

      // Check that changes were persisted
      expect(await newAdapter.get(0, 0)).toBe(99);
      expect(await newAdapter.get(2, 3)).toBe(88);
    });
  });

  describe("Swappable Matrix", () => {
    let storageManager;
    let swappableMatrix;

    beforeEach(async () => {
      // Create storage manager and initialize
      storageManager = Prime.Storage.createManager();
      await storageManager.init();

      // Create a larger matrix
      const rows = 100;
      const cols = 100;
      const matrix = [];

      for (let i = 0; i < rows; i++) {
        matrix[i] = [];
        for (let j = 0; j < cols; j++) {
          matrix[i][j] = i * cols + j;
        }
      }

      // Store the matrix
      const id = await storageManager.store(matrix, "large-matrix");

      // Create swappable matrix
      swappableMatrix = await Prime.Storage.createSwappableMatrix(
        storageManager,
        id,
        {
          blockSize: 20, // 20x20 blocks
          maxCachedBlocks: 4, // Keep only 4 blocks in memory at once
        },
      );
    });

    test("should provide matrix dimensions", () => {
      expect(swappableMatrix.rows).toBe(100);
      expect(swappableMatrix.columns).toBe(100);
    });

    test("should get individual matrix elements", async () => {
      expect(await swappableMatrix.get(0, 0)).toBe(0);
      expect(await swappableMatrix.get(5, 5)).toBe(505);
      expect(await swappableMatrix.get(99, 99)).toBe(9999);
    });

    test("should get matrix blocks efficiently", async () => {
      // Get elements from the same block
      const val1 = await swappableMatrix.get(10, 10);
      const val2 = await swappableMatrix.get(10, 11);
      const val3 = await swappableMatrix.get(11, 10);

      expect(val1).toBe(1010);
      expect(val2).toBe(1011);
      expect(val3).toBe(1110);

      // Check block cache stats
      expect(swappableMatrix.getCacheStats().hits).toBeGreaterThan(0);
    });

    test("should handle cache eviction when accessing different blocks", async () => {
      // Access elements in different blocks to trigger cache eviction
      // But only use valid coordinates within the 100x100 matrix
      for (let i = 0; i < 5; i++) {
        for (let j = 0; j < 5; j++) {
          const blockX = i * 20;
          const blockY = j * 20;
          // Ensure coordinates are within bounds
          if (blockX < 100 && blockY < 100) {
            await swappableMatrix.get(blockX, blockY);
          }
        }
      }

      // Should have had some cache misses
      expect(swappableMatrix.getCacheStats().misses).toBeGreaterThan(0);

      // Cache should not exceed max size
      expect(swappableMatrix.getCacheStats().size).toBeLessThanOrEqual(4);
    });

    test("should set individual matrix elements", async () => {
      await swappableMatrix.set(50, 50, 9999);

      expect(await swappableMatrix.get(50, 50)).toBe(9999);
    });

    test("should perform matrix operations correctly", async () => {
      // Calculate partial sum of a row
      let sum = 0;
      for (let j = 0; j < 10; j++) {
        sum += await swappableMatrix.get(5, j);
      }

      // Re-calculate the expected sum based on the actual matrix values in the test
      // The test creates a 100x100 matrix where each element is row*cols + col
      // So for row 5, the sum of the first 10 elements is the sum from 500 to 509
      let expectedSum = 0;
      for (let j = 0; j < 10; j++) {
        expectedSum += 5 * 100 + j;
      }
      // or we can compute it directly: 5*100*10 + (0+1+2+...+9) = 5000 + 45 = 5045

      expect(sum).toBe(5045); // 5*100*10 + 45
    });
  });

  describe("Virtual Array", () => {
    let storageManager;
    let virtualArray;
    const arraySize = 10000;

    beforeEach(async () => {
      // Create storage manager and initialize
      storageManager = Prime.Storage.createManager();
      await storageManager.init();

      // Create virtual array of a specific size
      virtualArray = await Prime.Storage.createVirtualArray(storageManager, {
        length: arraySize,
        defaultValue: 0,
        chunkSize: 1000,
      });

      await virtualArray.init();
    });

    test("should have correct array length", () => {
      expect(virtualArray.length).toBe(arraySize);
    });

    test("should get and set individual elements", async () => {
      await virtualArray.set(5, 42);
      await virtualArray.set(9999, 100);

      expect(await virtualArray.get(5)).toBe(42);
      expect(await virtualArray.get(9999)).toBe(100);
      expect(await virtualArray.get(1000)).toBe(0); // Default value
    });

    test("should set values in bulk", async () => {
      const values = [10, 20, 30, 40, 50];
      await virtualArray.setBulk(500, values);

      // Read individual values
      expect(await virtualArray.get(500)).toBe(10);
      expect(await virtualArray.get(501)).toBe(20);
      expect(await virtualArray.get(504)).toBe(50);

      // Read in bulk
      const retrieved = await virtualArray.getBulk(500, 5);
      expect(retrieved).toEqual(values);
    });

    test("should efficiently handle data in chunks", async () => {
      // Write to different chunks
      await virtualArray.set(500, 1);
      await virtualArray.set(1500, 2);
      await virtualArray.set(2500, 3);

      // Read from different chunks
      expect(await virtualArray.get(500)).toBe(1);
      expect(await virtualArray.get(1500)).toBe(2);
      expect(await virtualArray.get(2500)).toBe(3);

      // Check chunk stats
      const stats = virtualArray.getChunkStats();
      expect(stats.loadedChunks).toBeGreaterThanOrEqual(3);
    });

    test("should iterate over elements", async () => {
      // Set some values
      await virtualArray.setBulk(0, [1, 2, 3, 4, 5]);

      // Use forEach to iterate
      const values = [];
      await virtualArray.forEach(0, 5, (value, index) => {
        values.push({ value, index });
      });

      expect(values).toEqual([
        { value: 1, index: 0 },
        { value: 2, index: 1 },
        { value: 3, index: 2 },
        { value: 4, index: 3 },
        { value: 5, index: 4 },
      ]);
    });

    test("should handle mapped operations", async () => {
      // Set some values
      await virtualArray.setBulk(0, [1, 2, 3, 4, 5]);

      // Use map to transform values
      const doubledValues = await virtualArray.map(0, 5, (value) => value * 2);

      expect(doubledValues).toEqual([2, 4, 6, 8, 10]);

      // Original array should be unchanged
      expect(await virtualArray.get(2)).toBe(3);
    });

    test("should persist changes", async () => {
      // Make changes
      await virtualArray.set(42, 999);

      // Flush to storage
      await virtualArray.flush();

      // Create a new virtual array with the same ID
      const newArray = await Prime.Storage.createVirtualArray(storageManager, {
        id: virtualArray.id,
        length: arraySize,
        chunkSize: 1000,
      });

      await newArray.init();

      // Check the value was persisted
      expect(await newArray.get(42)).toBe(999);
    });
  });
});
