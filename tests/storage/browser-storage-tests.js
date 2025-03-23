/**
 * PrimeOS JavaScript Library - Browser Storage Provider Tests
 * Tests the browser-specific functionality of the storage providers
 */

const Prime = require('../../src');

// Skip tests in non-browser environments
const isBrowser = typeof window !== 'undefined' && typeof window.indexedDB !== 'undefined';

// Only run these tests in a browser environment
(isBrowser ? describe : describe.skip)('PrimeOS Browser Storage Provider', () => {

  beforeEach(() => {
    // Ensure clean test environment
    if (Prime.Storage && Prime.Storage.clearAllForTesting) {
      Prime.Storage.clearAllForTesting();
    }
  });

  describe('IndexedDB Provider', () => {
    let manager;

    beforeEach(async () => {
      manager = Prime.Storage.createManager({ provider: 'indexeddb' });
      await manager.init();
    });

    it('should use IndexedDB as the storage backend', () => {
      expect(manager.getProviderType()).toBe('indexeddb');
    });

    it('should store and retrieve data using IndexedDB', async () => {
      const testData = { test: 'browser-data', value: 123 };
      const id = await manager.store(testData);
      
      const retrieved = await manager.load(id);
      expect(retrieved).toEqual(testData);
    });

    it('should handle large data in chunks', async () => {
      // Create large test data - 10MB array
      const largeArray = new Uint8Array(10 * 1024 * 1024);
      for (let i = 0; i < largeArray.length; i++) {
        largeArray[i] = i % 256;
      }
      
      const id = await manager.store(largeArray);
      
      const retrieved = await manager.load(id);
      expect(retrieved).toEqual(largeArray);
    });

    it('should persist data across page reloads', async () => {
      // Store a unique value with a timestamp to verify persistence
      const timestamp = Date.now();
      const testData = { test: 'persistent-data', timestamp };
      const id = await manager.store(testData, 'persistence-test');
      
      // Simulate a page reload by creating a new manager
      const newManager = Prime.Storage.createManager({ provider: 'indexeddb' });
      await newManager.init();
      
      // Load the data with the new manager
      const retrieved = await newManager.load('persistence-test');
      expect(retrieved).toEqual(testData);
    });
  });

  describe('Fallback Behavior', () => {
    let originalIndexedDB;

    beforeEach(() => {
      // Save original IndexedDB
      if (typeof window !== 'undefined') {
        originalIndexedDB = window.indexedDB;
      }
    });

    afterEach(() => {
      // Restore original IndexedDB
      if (typeof window !== 'undefined') {
        window.indexedDB = originalIndexedDB;
      }
    });

    it('should fall back to memory storage if IndexedDB is unavailable', async () => {
      // Mock IndexedDB as undefined
      if (typeof window !== 'undefined') {
        window.indexedDB = undefined;
      }
      
      const manager = Prime.Storage.createManager();
      await manager.init();
      
      expect(manager.getProviderType()).toBe('memory');
      
      // Test basic functionality with memory fallback
      const testData = { test: 'fallback-data' };
      const id = await manager.store(testData);
      
      const retrieved = await manager.load(id);
      expect(retrieved).toEqual(testData);
    });
  });

  describe('Browser Storage Limits', () => {
    let manager;

    beforeEach(async () => {
      manager = Prime.Storage.createManager({ provider: 'indexeddb' });
      await manager.init();
    });

    it('should report available storage space', async () => {
      const storageInfo = await manager.getStorageInfo();
      expect(storageInfo).toBeDefined();
      expect(storageInfo.available).toBeGreaterThan(0);
      expect(storageInfo.used).toBeGreaterThanOrEqual(0);
    });

    it('should handle storage quota errors gracefully', async () => {
      // This test attempts to exceed storage quota and checks error handling
      // Only run this test if we can create very large arrays
      try {
        // Try to create a massive array (may fail on some browsers)
        const hugeSize = 500 * 1024 * 1024; // 500MB
        const hugeArray = new Uint8Array(hugeSize);
        
        try {
          await manager.store(hugeArray);
          // If the store succeeded, we'll check if what we stored is retrievable
          const id = 'huge-array-test';
          const retrieved = await manager.load(id);
          expect(retrieved.length).toEqual(hugeArray.length);
        } catch (error) {
          // We expect a quota error
          expect(error.name).toContain('Quota');
          expect(error.code).toBe('STORAGE_QUOTA_EXCEEDED');
        }
      } catch (e) {
        // If we can't even create the array, skip the test
        pending('Cannot allocate large array for storage quota test');
      }
    });
  });
});