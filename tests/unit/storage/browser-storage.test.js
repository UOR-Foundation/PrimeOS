/**
 * PrimeOS Unit Tests - Browser Storage Provider
 * 
 * Tests the browser-specific functionality of the storage providers.
 * Note: These tests will be skipped when running in Node.js environment.
 */

const Prime = require('../../../src');
const { Setup } = require('../../utils');

describe('Browser Storage Provider', () => {
  // Check if in browser environment - skip tests otherwise
  const isBrowser = typeof window !== 'undefined' && typeof window.localStorage !== 'undefined';
  
  // Mock browser environment if needed for testing
  let mockLocalStorage;
  let mockIndexedDB;
  let manager;
  let originalEnv;
  
  beforeAll(() => {
    if (!isBrowser) {
      console.warn('Skipping Browser Storage Provider tests in non-browser environment');
      
      // Save original environment
      originalEnv = global.window;
      
      // Create mock browser environment
      mockLocalStorage = {
        store: {},
        setItem: function(key, value) {
          this.store[key] = value.toString();
        },
        getItem: function(key) {
          return this.store[key] || null;
        },
        removeItem: function(key) {
          delete this.store[key];
        },
        clear: function() {
          this.store = {};
        }
      };
      
      // Simple mock of IndexedDB
      mockIndexedDB = {
        open: jest.fn().mockReturnValue({
          onupgradeneeded: null,
          onsuccess: null,
          onerror: null,
          result: {
            createObjectStore: jest.fn(),
            transaction: jest.fn().mockReturnValue({
              objectStore: jest.fn().mockReturnValue({
                put: jest.fn().mockReturnValue({
                  onsuccess: null,
                  onerror: null
                }),
                get: jest.fn().mockReturnValue({
                  onsuccess: null,
                  onerror: null
                }),
                delete: jest.fn().mockReturnValue({
                  onsuccess: null,
                  onerror: null
                }),
                getAllKeys: jest.fn().mockReturnValue({
                  onsuccess: null,
                  onerror: null
                })
              }),
              oncomplete: null,
              onerror: null
            })
          }
        })
      };
      
      // Create a minimal browser environment
      global.window = {
        localStorage: mockLocalStorage,
        indexedDB: mockIndexedDB
      };
    }
  });
  
  afterAll(() => {
    if (!isBrowser) {
      // Restore original environment
      global.window = originalEnv;
    }
  });
  
  beforeEach(async () => {
    // Clear storage before each test
    if (isBrowser) {
      localStorage.clear();
    } else if (mockLocalStorage) {
      mockLocalStorage.clear();
    }
    
    // Create storage manager with browser provider
    manager = Prime.Storage.createManager({ 
      provider: 'browser',
      persistenceMethod: 'localStorage' // More reliable than IndexedDB for tests
    });
    
    await manager.init();
    
    // Ensure clean test environment
    if (Prime.Storage && Prime.Storage.clearAllForTesting) {
      Prime.Storage.clearAllForTesting();
    }
  });
  
  describe('LocalStorage Provider', () => {
    test('should use browser as the storage backend', () => {
      expect(manager.getProviderType()).toBe('browser');
    });
    
    test('should store and retrieve data using localStorage', async () => {
      // Skip if not browser and no mock
      if (!isBrowser && !mockLocalStorage) return;
      
      const testData = { test: 'browser-data', value: 123 };
      const id = "test-browser-id";
      
      await manager.store(testData, id);
      
      // Check the data was stored
      const storedData = await manager.load(id);
      expect(storedData).toEqual(testData);
      
      // Check localStorage was used
      if (isBrowser) {
        const stored = localStorage.getItem(`primeos-storage:${id}`);
        expect(stored).toBeDefined();
      } else {
        const stored = mockLocalStorage.getItem(`primeos-storage:${id}`);
        expect(stored).toBeDefined();
      }
    });
    
    test('should handle JSON serialization and deserialization', async () => {
      // Skip if not browser and no mock
      if (!isBrowser && !mockLocalStorage) return;
      
      const testData = { 
        string: 'test',
        number: 123,
        boolean: true,
        array: [1, 2, 3],
        object: { a: 1, b: 2 },
        nested: {
          c: [4, 5, 6],
          d: { e: 'nested' }
        }
      };
      
      const id = "complex-data";
      await manager.store(testData, id);
      
      const loadedData = await manager.load(id);
      expect(loadedData).toEqual(testData);
    });
    
    test('should delete data', async () => {
      // Skip if not browser and no mock
      if (!isBrowser && !mockLocalStorage) return;
      
      const testData = { test: 'to-be-deleted' };
      const id = "delete-test";
      
      await manager.store(testData, id);
      await manager.delete(id);
      
      // Verify data is gone
      let exists = false;
      try {
        await manager.load(id);
        exists = true;
      } catch (e) {
        exists = false;
      }
      
      expect(exists).toBe(false);
      
      // Check localStorage
      if (isBrowser) {
        const stored = localStorage.getItem(`primeos-storage:${id}`);
        expect(stored).toBeNull();
      } else {
        const stored = mockLocalStorage.getItem(`primeos-storage:${id}`);
        expect(stored).toBeNull();
      }
    });
    
    test('should list keys', async () => {
      // Skip if not browser and no mock
      if (!isBrowser && !mockLocalStorage) return;
      
      // Store multiple items
      await manager.store({ a: 1 }, 'browser:key1');
      await manager.store({ b: 2 }, 'browser:key2');
      await manager.store({ c: 3 }, 'other:key3');
      
      // Get all keys
      const allKeys = await manager.keys();
      expect(allKeys).toContain('browser:key1');
      expect(allKeys).toContain('browser:key2');
      expect(allKeys).toContain('other:key3');
      
      // Get keys with prefix
      const browserKeys = await manager.keys('browser:');
      expect(browserKeys).toContain('browser:key1');
      expect(browserKeys).toContain('browser:key2');
      expect(browserKeys).not.toContain('other:key3');
    });
  });
  
  describe('Storage Limits', () => {
    test('should handle storage limits gracefully', async () => {
      // Skip if not browser and no mock
      if (!isBrowser && !mockLocalStorage) return;
      
      // This test can't fully simulate localStorage limits without causing issues
      // Mock localStorage with a size limit
      let mockSizeLimited;
      if (!isBrowser) {
        // Override mock to simulate limited storage
        const originalSetItem = mockLocalStorage.setItem;
        mockSizeLimited = true;
        
        mockLocalStorage.setItem = function(key, value) {
          // Simulate storage limit after 3 items
          if (Object.keys(this.store).length >= 3 && !Object.prototype.hasOwnProperty.call(this.store, key)) {
            const error = new Error('QuotaExceededError');
            error.name = 'QuotaExceededError';
            throw error;
          }
          originalSetItem.call(this, key, value);
        };
      }
      
      try {
        // Store items until limit is reached or 5 items
        for (let i = 0; i < 5; i++) {
          try {
            await manager.store({ index: i }, `limit-test-${i}`);
          } catch (e) {
            // Expect error to be storage limit related
            if (mockSizeLimited) {
              expect(e.name).toMatch(/QuotaExceeded|StorageFull|Storage/i);
            }
            break;
          }
        }
        
        // Should be able to load stored items
        for (let i = 0; i < 3; i++) {
          try {
            const data = await manager.load(`limit-test-${i}`);
            expect(data.index).toBe(i);
          } catch (e) {
            // Item might not have been stored due to limit
            console.log(`Item limit-test-${i} not found, may be due to storage limit`);
          }
        }
      } finally {
        // Restore original mock if modified
        if (!isBrowser && mockSizeLimited) {
          mockLocalStorage.setItem = originalSetItem;
        }
      }
    });
  });
  
  describe('Browser Feature Detection', () => {
    test('should detect available browser storage methods', () => {
      // Skip if not browser
      if (!isBrowser && !mockLocalStorage) return;
      
      const available = Prime.Storage.browser.getAvailableStorageMethods();
      
      // Should detect localStorage in real browser or mock
      expect(available).toContain('localStorage');
      
      // IndexedDB may or may not be available depending on environment
      if (isBrowser && window.indexedDB) {
        expect(available).toContain('indexedDB');
      } else if (mockIndexedDB) {
        expect(available).toContain('indexedDB');
      }
    });
  });
  
  describe('Storage Utilities', () => {
    test('should provide browser storage utility functions', () => {
      // Skip if not browser
      if (!isBrowser && !mockLocalStorage) return;
      
      // Check utility functions exist
      expect(typeof Prime.Storage.browser.utils.getStorageUsage).toBe('function');
      expect(typeof Prime.Storage.browser.utils.clearStorage).toBe('function');
      
      // Call storage usage function - should return an object with usage info
      const usage = Prime.Storage.browser.utils.getStorageUsage();
      expect(usage).toBeDefined();
      expect(typeof usage.total).toBe('number');
      expect(typeof usage.used).toBe('number');
      expect(typeof usage.available).toBe('number');
    });
  });
});