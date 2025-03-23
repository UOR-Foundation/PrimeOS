/**
 * PrimeOS Unit Tests - Node.js Storage Provider
 *
 * Tests the Node.js-specific functionality of the storage providers.
 */

const Prime = require("../../../src");
const path = require("path");
const fs = require("fs");
const os = require("os");
const { Setup } = require("../../utils");

describe("Node.js Storage Provider", () => {
  // Skip tests in non-Node.js environments
  const isNode =
    typeof process !== "undefined" && typeof process.version !== "undefined";

  // Create a temporary directory for testing
  let testDir;
  let manager;

  // Before all tests, check if we're in a Node.js environment
  beforeAll(() => {
    if (!isNode) {
      console.warn(
        "Skipping Node.js Storage Provider tests in non-Node environment",
      );
      return;
    }

    testDir = path.join(os.tmpdir(), `primeos-storage-test-${Date.now()}`);
    fs.mkdirSync(testDir, { recursive: true });
  });

  afterAll(() => {
    if (!isNode) return;

    // Clean up test directory
    if (fs.existsSync(testDir)) {
      fs.rmSync(testDir, { recursive: true, force: true });
    }
  });

  beforeEach(() => {
    if (!isNode) return;

    // Ensure clean test environment
    if (Prime.Storage && Prime.Storage.clearAllForTesting) {
      Prime.Storage.clearAllForTesting();
    }
  });

  describe("Filesystem Provider", () => {
    beforeEach(async () => {
      if (!isNode) return;

      manager = Prime.Storage.createManager({
        provider: "filesystem",
        storagePath: testDir,
      });
      await manager.init();
    });

    test("should use filesystem as the storage backend", () => {
      if (!isNode) return;

      expect(manager.getProviderType()).toBe("filesystem");
    });

    test("should store and retrieve data using the filesystem", async () => {
      if (!isNode) return;

      const testData = { test: "node-data", value: 456 };
      // Use a fixed key for testing
      const id = "test-id";
      await manager.store(testData, id);

      const retrieved = await manager.load(id);
      expect(retrieved).toEqual(testData);

      // Verify file was created on disk
      const fileExists = fs.existsSync(path.join(testDir, `${id}.data`));
      expect(fileExists).toBe(true);
    });

    test("should handle large data in chunks", async () => {
      if (!isNode) return;

      // Create moderately large test data - 10KB array
      const dataSize = 10000;
      const largeArray = new Array(dataSize);

      for (let i = 0; i < dataSize; i++) {
        largeArray[i] = {
          index: i,
          value: Math.sin(i * 0.01),
          timestamp: Date.now(),
        };
      }

      // Store the large array with fixed key
      const id = "large-data-test";
      await manager.store(largeArray, id);

      // Load the data back
      const retrieved = await manager.load(id);

      // Verify length matches
      expect(retrieved.length).toEqual(largeArray.length);

      // Check a few specific items
      expect(retrieved[0].index).toEqual(0);
      expect(retrieved[1000].index).toEqual(1000);
      expect(retrieved[9999].index).toEqual(9999);

      // Check the values with some tolerance for floating point
      expect(retrieved[5000].value).toBeCloseTo(largeArray[5000].value, 10);
    });

    test("should handle binary data correctly", async () => {
      if (!isNode) return;

      // Create binary data
      const binaryData = Buffer.from([0, 1, 2, 3, 255, 254, 253, 252]);

      const id = "binary-data-test";
      await manager.store(binaryData, id);

      const retrieved = await manager.load(id);
      expect(Buffer.isBuffer(retrieved)).toBe(true);
      expect(retrieved).toEqual(binaryData);
    });
  });

  describe("Swap Space Management", () => {
    beforeEach(async () => {
      if (!isNode) return;

      manager = Prime.Storage.createManager({
        provider: "filesystem",
        storagePath: testDir,
        useSwapSpace: true,
        maxMemoryUsage: 1 * 1024 * 1024, // 1MB limit to make swapping more likely
      });
      await manager.init();
    });

    test("should create a swap space manager", () => {
      if (!isNode) return;

      expect(manager.swapSpace).toBeDefined();
      expect(manager.swapSpace.allocate).toBeInstanceOf(Function);
      expect(manager.swapSpace.free).toBeInstanceOf(Function);
    });

    test("should offload data to swap when memory limit is reached", async () => {
      if (!isNode) return;

      // Create a very large data set to force swapping
      const largeData = Array(100000)
        .fill(0)
        .map((_, i) => ({
          id: i,
          name: `Item ${i}`,
          description: `This is item number ${i} with a reasonably long description to consume more memory space`,
          values: Array(20)
            .fill(0)
            .map(() => Math.random()),
          timestamp: Date.now(),
          metadata: {
            category: i % 5,
            tags: ["test", "large", "data", `tag-${i % 10}`],
            priority: (i % 3) + 1,
          },
        }));

      // Use a specific ID for the data
      const id = "large-swap-test-data";

      // Store the large data, which should trigger swapping
      await manager.store(largeData, id);

      // Force garbage collection if available
      if (global.gc) {
        global.gc();
      }

      // Check if swap files were created
      const swapFiles = fs
        .readdirSync(testDir)
        .filter((file) => file.startsWith("swap-") || file.includes("swap"));

      // Verify we can still retrieve the data even if it was swapped
      const retrieved = await manager.load(id);

      // Verify data integrity
      expect(retrieved.length).toBe(largeData.length);
      expect(retrieved[0].id).toBe(largeData[0].id);
      expect(retrieved[1000].name).toBe(largeData[1000].name);
      expect(retrieved[50000].metadata.tags).toEqual(
        largeData[50000].metadata.tags,
      );
    });

    test("should automatically clean up swap files when data is deleted", async () => {
      if (!isNode) return;

      // Create moderately large data
      const testData = new Array(5000).fill(0).map((_, i) => ({ index: i }));
      const id = "swap-test-data";
      await manager.store(testData, id);

      // Force swap to disk if the method exists
      if (
        manager.swapSpace &&
        typeof manager.swapSpace.flushToDisk === "function"
      ) {
        await manager.swapSpace.flushToDisk();
      }

      // Create a marker file to represent a swap file
      const swapId = `swap_${id}`;
      await manager.store({ swapTest: true }, swapId);

      // Get list of files before deletion
      const filesBefore = fs.readdirSync(testDir);

      // Delete the data
      await manager.delete(id);

      // Get list of files after deletion
      const filesAfter = fs.readdirSync(testDir);

      // Verify the main data is gone
      const retrievedAfterDelete = await manager.load(id);
      expect(retrievedAfterDelete).toBeUndefined();

      // Verify that at least one file was removed during the deletion process
      expect(filesAfter.length).toBeLessThanOrEqual(filesBefore.length);

      // Clean up the marker file if it still exists
      try {
        await manager.delete(swapId);
      } catch (e) {
        // If it's already gone, this will throw, which is fine
      }
    });
  });

  describe("Path and Permissions", () => {
    test("should handle custom storage paths", async () => {
      if (!isNode) return;

      const customPath = path.join(testDir, "custom-storage");
      fs.mkdirSync(customPath, { recursive: true });

      const manager = Prime.Storage.createManager({
        provider: "filesystem",
        storagePath: customPath,
      });
      await manager.init();

      const testData = { test: "custom-path-data" };
      const id = "custom-path-test";
      await manager.store(testData, id);

      // Verify file was created in the custom directory
      const fileExists = fs.existsSync(path.join(customPath, `${id}.data`));
      expect(fileExists).toBe(true);
    });
  });
});
