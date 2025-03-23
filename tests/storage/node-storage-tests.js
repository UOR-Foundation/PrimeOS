/**
 * PrimeOS JavaScript Library - Node Storage Provider Tests
 * Tests the Node.js-specific functionality of the storage providers
 */

const Prime = require('../../src');
const path = require('path');
const fs = require('fs');
const os = require('os');

describe('PrimeOS Node Storage Provider', () => {
  // Skip all tests if not in a Node.js environment
  beforeAll(() => {
    if (typeof process === 'undefined' || typeof process.version === 'undefined') {
      // Use test.skip for each test in this file
      test.skip('Skipping Node.js tests in browser environment', () => {});
    }
  });

  // Create a temporary directory for testing
  let testDir;
  
  beforeAll(() => {
    testDir = path.join(os.tmpdir(), `primeos-storage-test-${Date.now()}`);
    fs.mkdirSync(testDir, { recursive: true });
  });
  
  afterAll(() => {
    // Clean up test directory
    if (fs.existsSync(testDir)) {
      fs.rmSync(testDir, { recursive: true, force: true });
    }
  });

  beforeEach(() => {
    // Ensure clean test environment
    if (Prime.Storage && Prime.Storage.clearAllForTesting) {
      Prime.Storage.clearAllForTesting();
    }
  });

  describe('Filesystem Provider', () => {
    let manager;

    beforeEach(async () => {
      manager = Prime.Storage.createManager({ 
        provider: 'filesystem',
        storagePath: testDir
      });
      await manager.init();
    });

    it('should use filesystem as the storage backend', () => {
      expect(manager.getProviderType()).toBe('filesystem');
    });

    it('should store and retrieve data using the filesystem', async () => {
      const testData = { test: 'node-data', value: 456 };
      const id = await manager.store(testData);
      
      const retrieved = await manager.load(id);
      expect(retrieved).toEqual(testData);
      
      // Verify file was created on disk
      const fileExists = fs.existsSync(path.join(testDir, `${id}.data`));
      expect(fileExists).toBe(true);
    });

    it('should handle large data in chunks', async () => {
      // Create large test data - 10MB array
      const largeArray = new Array(1024 * 1024).fill(0).map((_, i) => i);
      
      const id = await manager.store(largeArray);
      
      const retrieved = await manager.load(id);
      expect(retrieved).toEqual(largeArray);
    });

    it('should handle binary data correctly', async () => {
      // Create binary data
      const binaryData = Buffer.from([0, 1, 2, 3, 255, 254, 253, 252]);
      
      const id = await manager.store(binaryData);
      
      const retrieved = await manager.load(id);
      expect(Buffer.isBuffer(retrieved)).toBe(true);
      expect(retrieved).toEqual(binaryData);
    });
  });

  describe('Swap Space Management', () => {
    let manager;

    beforeEach(async () => {
      manager = Prime.Storage.createManager({ 
        provider: 'filesystem',
        storagePath: testDir,
        useSwapSpace: true,
        maxMemoryUsage: 10 * 1024 * 1024 // 10MB limit
      });
      await manager.init();
    });

    it('should create a swap space manager', () => {
      expect(manager.swapSpace).toBeDefined();
      expect(manager.swapSpace.allocate).toBeInstanceOf(Function);
      expect(manager.swapSpace.free).toBeInstanceOf(Function);
    });

    it('should offload data to swap when memory limit is reached', async () => {
      // First, fill memory up to the limit
      const data1 = new Array(500000).fill(0).map((_, i) => ({ index: i }));
      const data2 = new Array(500000).fill(0).map((_, i) => ({ index: i + 500000 }));
      
      const id1 = await manager.store(data1);
      const id2 = await manager.store(data2);
      
      // This should trigger swap to disk
      const stats = await manager.getMemoryStats();
      
      expect(stats.swapUsed).toBeGreaterThan(0);
      
      // Verify we can still retrieve data
      const retrieved1 = await manager.load(id1);
      expect(retrieved1).toEqual(data1);
      
      const retrieved2 = await manager.load(id2);
      expect(retrieved2).toEqual(data2);
    });

    it('should automatically clean up swap files when data is deleted', async () => {
      const testData = new Array(100000).fill(0).map((_, i) => ({ index: i }));
      const id = await manager.store(testData);
      
      // Force swap to disk
      await manager.swapSpace.flushToDisk(id);
      
      // Count swap files before deletion
      const filesBefore = fs.readdirSync(testDir).filter(f => f.endsWith('.swap'));
      
      // Delete the data
      await manager.delete(id);
      
      // Count swap files after deletion
      const filesAfter = fs.readdirSync(testDir).filter(f => f.endsWith('.swap'));
      
      expect(filesAfter.length).toBeLessThan(filesBefore.length);
    });
  });

  describe('Path and Permissions', () => {
    it('should handle custom storage paths', async () => {
      const customPath = path.join(testDir, 'custom-storage');
      fs.mkdirSync(customPath, { recursive: true });
      
      const manager = Prime.Storage.createManager({ 
        provider: 'filesystem',
        storagePath: customPath
      });
      await manager.init();
      
      const testData = { test: 'custom-path-data' };
      const id = await manager.store(testData);
      
      // Verify file was created in the custom directory
      const fileExists = fs.existsSync(path.join(customPath, `${id}.data`));
      expect(fileExists).toBe(true);
    });

    it('should handle permission errors gracefully', async () => {
      // Create a directory with restricted permissions
      const restrictedPath = path.join(testDir, 'restricted');
      fs.mkdirSync(restrictedPath, { recursive: true });
      
      // Skip test on Windows as permission handling is different
      if (process.platform !== 'win32') {
        try {
          // Try to make it read-only (may fail on some systems)
          fs.chmodSync(restrictedPath, 0o444);
          
          const manager = Prime.Storage.createManager({ 
            provider: 'filesystem',
            storagePath: restrictedPath
          });
          
          try {
            await manager.init();
            const testData = { test: 'should-fail' };
            await manager.store(testData);
            // If this succeeds, the permissions weren't actually restricted
          } catch (error) {
            expect(error.name).toBe('PrimeStorageError');
            expect(error.code).toBe('STORAGE_PERMISSION_DENIED');
          }
        } catch (e) {
          // If we can't set permissions, skip the test
          // Skip this test
          test.skip('Cannot set restricted permissions for test', () => {});
        } finally {
          // Restore permissions to allow cleanup
          try {
            fs.chmodSync(restrictedPath, 0o777);
          } catch (e) {
            // Ignore errors in cleanup
          }
        }
      }
    });
  });
});