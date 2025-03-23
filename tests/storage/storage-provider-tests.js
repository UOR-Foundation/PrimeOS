/**
 * PrimeOS JavaScript Library - Storage Provider Tests
 * Tests the core functionality of the storage providers
 */

const Prime = require('../../src');

describe('PrimeOS Storage Provider', () => {
  beforeEach(() => {
    // Ensure clean test environment
    if (Prime.Storage && Prime.Storage.clearAllForTesting) {
      Prime.Storage.clearAllForTesting();
    }
  });

  describe('Core API', () => {
    it('should export the Storage module', () => {
      expect(Prime.Storage).toBeDefined();
      expect(Prime.Storage.createManager).toBeInstanceOf(Function);
    });

    it('should create a storage manager', async () => {
      const manager = Prime.Storage.createManager();
      expect(manager).toBeDefined();
      expect(manager.init).toBeInstanceOf(Function);
      expect(manager.store).toBeInstanceOf(Function);
      expect(manager.load).toBeInstanceOf(Function);
      expect(manager.delete).toBeInstanceOf(Function);
      expect(manager.clear).toBeInstanceOf(Function);
    });

    it('should detect the current environment', () => {
      expect(Prime.Storage.getEnvironment).toBeInstanceOf(Function);
      const env = Prime.Storage.getEnvironment();
      expect(['browser', 'node', 'unknown']).toContain(env);
    });
  });
});