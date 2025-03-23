/**
 * PrimeOS Unit Tests - Storage Core
 *
 * Tests for the core functionality of the Storage module.
 */

const Prime = require("../../../src");
const { Assertions } = require("../../utils");

describe("Storage Core", () => {
  let storageManager;

  beforeEach(async () => {
    storageManager = Prime.Storage.createManager({
      provider: "memory", // Use memory provider for tests
    });
    await storageManager.init();
  });

  afterEach(async () => {
    if (Prime.Storage.clearAllForTesting) {
      Prime.Storage.clearAllForTesting();
    }
  });

  describe("Manager", () => {
    test("should create with default settings", () => {
      expect(storageManager).toBeDefined();
      expect(storageManager.getProviderType()).toBe("memory");
    });

    test("should store and retrieve data", async () => {
      const testData = { test: true, value: 123 };
      const id = await storageManager.store(testData);

      expect(id).toBeDefined();
      expect(typeof id).toBe("string");

      const retrieved = await storageManager.load(id);
      expect(retrieved).toEqual(testData);
    });

    test("should store and retrieve data with custom ID", async () => {
      const testData = { test: true, value: 456 };
      const customId = "custom-id-123";

      await storageManager.store(testData, customId);

      const retrieved = await storageManager.load(customId);
      expect(retrieved).toEqual(testData);
    });

    test("should overwrite data with same ID", async () => {
      const testData1 = { value: "original" };
      const testData2 = { value: "updated" };
      const id = "test-overwrite";

      await storageManager.store(testData1, id);
      await storageManager.store(testData2, id);

      const retrieved = await storageManager.load(id);
      expect(retrieved).toEqual(testData2);
    });

    test("should delete data", async () => {
      const testData = { test: true };
      const id = await storageManager.store(testData);

      await storageManager.delete(id);

      // Trying to load should throw
      await expect(storageManager.load(id)).rejects.toThrow();
    });

    test("should check if data exists", async () => {
      const testData = { test: true };
      const id = await storageManager.store(testData);

      const exists = await storageManager.exists(id);
      expect(exists).toBe(true);

      const nonExistent = await storageManager.exists("non-existent-id");
      expect(nonExistent).toBe(false);
    });

    test("should list stored keys", async () => {
      await storageManager.store({ a: 1 }, "key1");
      await storageManager.store({ b: 2 }, "key2");
      await storageManager.store({ c: 3 }, "key3");

      const keys = await storageManager.keys();
      expect(keys).toContain("key1");
      expect(keys).toContain("key2");
      expect(keys).toContain("key3");
    });

    test("should list keys with prefix", async () => {
      await storageManager.store({ a: 1 }, "test:key1");
      await storageManager.store({ b: 2 }, "test:key2");
      await storageManager.store({ c: 3 }, "other:key3");

      const testKeys = await storageManager.keys("test:");
      expect(testKeys).toContain("test:key1");
      expect(testKeys).toContain("test:key2");
      expect(testKeys).not.toContain("other:key3");
    });
  });

  describe("Serializer", () => {
    test("should serialize and deserialize basic types", () => {
      const serializer = Prime.Storage.Serializer;

      // Number
      const num = 123.456;
      const numSerialized = serializer.serialize(num);
      const numDeserialized = serializer.deserialize(numSerialized);
      expect(numDeserialized).toBe(num);

      // String
      const str = "test string";
      const strSerialized = serializer.serialize(str);
      const strDeserialized = serializer.deserialize(strSerialized);
      expect(strDeserialized).toBe(str);

      // Boolean
      const bool = true;
      const boolSerialized = serializer.serialize(bool);
      const boolDeserialized = serializer.deserialize(boolSerialized);
      expect(boolDeserialized).toBe(bool);

      // Null
      const nullVal = null;
      const nullSerialized = serializer.serialize(nullVal);
      const nullDeserialized = serializer.deserialize(nullSerialized);
      expect(nullDeserialized).toBe(nullVal);
    });

    test("should serialize and deserialize complex objects", () => {
      const serializer = Prime.Storage.Serializer;

      const complex = {
        name: "Test Object",
        values: [1, 2, 3, 4, 5],
        nested: {
          a: 1,
          b: "test",
          c: true,
          d: null,
          e: undefined,
        },
        date: new Date(2023, 0, 1),
      };

      const serialized = serializer.serialize(complex);
      const deserialized = serializer.deserialize(serialized);

      // Date objects should be serialized as ISO strings
      expect(deserialized.date).toEqual(complex.date.toISOString());

      // Check other properties match
      expect(deserialized.name).toBe(complex.name);
      expect(deserialized.values).toEqual(complex.values);
      expect(deserialized.nested.a).toBe(complex.nested.a);
      expect(deserialized.nested.b).toBe(complex.nested.b);
      expect(deserialized.nested.c).toBe(complex.nested.c);
      expect(deserialized.nested.d).toBe(complex.nested.d);
      // Undefined values are not serialized
      expect(deserialized.nested.e).toBeUndefined();
    });

    test("should handle circular references", () => {
      const serializer = Prime.Storage.Serializer;

      const circular = { name: "Circular" };
      circular.self = circular;

      // Should not throw
      const serialized = serializer.serialize(circular);
      const deserialized = serializer.deserialize(serialized);

      expect(deserialized.name).toBe("Circular");
      // Circular reference is replaced with a reference marker
      expect(typeof deserialized.self).toBe("string");
      expect(deserialized.self).toContain("[Circular Reference]");
    });

    test("should handle typed arrays and buffers", () => {
      const serializer = Prime.Storage.Serializer;

      // Int32Array
      const int32Array = new Int32Array([1, 2, 3, 4, 5]);
      const int32Serialized = serializer.serialize(int32Array);
      const int32Deserialized = serializer.deserialize(int32Serialized);

      // The result should be a regular array since typed arrays are serialized as regular arrays
      expect(Array.isArray(int32Deserialized)).toBe(true);
      expect(int32Deserialized).toEqual([1, 2, 3, 4, 5]);

      // Float64Array
      const float64Array = new Float64Array([1.1, 2.2, 3.3]);
      const float64Serialized = serializer.serialize(float64Array);
      const float64Deserialized = serializer.deserialize(float64Serialized);

      expect(Array.isArray(float64Deserialized)).toBe(true);
      expect(float64Deserialized).toEqual([1.1, 2.2, 3.3]);

      // ArrayBuffer
      const buffer = new ArrayBuffer(4);
      const view = new Uint8Array(buffer);
      view[0] = 1;
      view[1] = 2;
      view[2] = 3;
      view[3] = 4;

      const bufferSerialized = serializer.serialize(buffer);
      const bufferDeserialized = serializer.deserialize(bufferSerialized);

      // ArrayBuffers are serialized as base64 strings and deserialized as regular arrays
      expect(Array.isArray(bufferDeserialized)).toBe(true);
      expect(bufferDeserialized).toEqual([1, 2, 3, 4]);
    });
  });

  describe("Chunk Management", () => {
    test("should create and manage chunks", () => {
      const chunkManager = new Prime.Storage.Chunk.Manager({
        chunkSize: 100,
        serializer: Prime.Storage.Serializer,
      });

      // Create a large array
      const largeArray = new Array(250).fill(0).map((_, i) => i);

      // Split into chunks
      const chunks = chunkManager.createChunks(largeArray);

      // Should have 3 chunks (first 2 with 100 items, last with 50)
      expect(chunks.length).toBe(3);
      expect(chunks[0].data.length).toBe(100);
      expect(chunks[1].data.length).toBe(100);
      expect(chunks[2].data.length).toBe(50);

      // Reconstruct the array
      const reconstructed = chunkManager.combineChunks(chunks);
      expect(reconstructed).toEqual(largeArray);
    });

    test("should handle object chunking", () => {
      const chunkManager = new Prime.Storage.Chunk.Manager({
        chunkSize: 10000, // Byte size limit
        serializer: Prime.Storage.Serializer,
      });

      // Create objects that should split across multiple chunks
      const objects = [];
      for (let i = 0; i < 50; i++) {
        objects.push({
          id: i,
          // Large string to force chunking
          data: "A".repeat(1000),
        });
      }

      // Split into chunks
      const chunks = chunkManager.createChunks(objects);

      // Should have multiple chunks
      expect(chunks.length).toBeGreaterThan(1);

      // Reconstruct the objects
      const reconstructed = chunkManager.combineChunks(chunks);
      expect(reconstructed).toEqual(objects);
    });
  });

  describe("Memory Management", () => {
    test("should track memory usage", () => {
      const memoryManager = new Prime.Storage.Memory.Manager({
        maxMemoryUsage: 1024 * 1024, // 1MB
      });

      // Allocate some memory
      memoryManager.track("item1", 1000);
      memoryManager.track("item2", 2000);

      // Check usage
      const usage = memoryManager.getUsage();
      expect(usage.total).toBe(3000);
      expect(usage.items.item1).toBe(1000);
      expect(usage.items.item2).toBe(2000);

      // Update an item
      memoryManager.track("item1", 1500);
      expect(memoryManager.getUsage().items.item1).toBe(1500);
      expect(memoryManager.getUsage().total).toBe(3500);

      // Release an item
      memoryManager.release("item2");
      expect(memoryManager.getUsage().items.item2).toBeUndefined();
      expect(memoryManager.getUsage().total).toBe(1500);
    });

    test("should calculate memory for objects", () => {
      const memoryManager = new Prime.Storage.Memory.Manager();

      // Simple object
      const simpleObj = { a: 1, b: 2, c: "test" };
      const simpleSize = memoryManager.calculateSize(simpleObj);

      // Array
      const array = [1, 2, 3, 4, 5];
      const arraySize = memoryManager.calculateSize(array);

      // String
      const string = "test string";
      const stringSize = memoryManager.calculateSize(string);

      // All sizes should be reasonable
      expect(simpleSize).toBeGreaterThan(0);
      expect(arraySize).toBeGreaterThan(0);
      expect(stringSize).toBeGreaterThan(0);

      // More complex structures should use more memory
      const complexObj = {
        a: [1, 2, 3, 4, 5],
        b: { x: 1, y: 2, z: 3 },
        c: "test string".repeat(10),
      };

      const complexSize = memoryManager.calculateSize(complexObj);
      expect(complexSize).toBeGreaterThan(simpleSize);
    });

    test("should detect memory pressure", () => {
      const memoryManager = new Prime.Storage.Memory.Manager({
        maxMemoryUsage: 1000,
      });

      // Start with no pressure
      expect(memoryManager.isUnderPressure()).toBe(false);

      // Add items close to the limit
      memoryManager.track("item1", 500);
      memoryManager.track("item2", 300);

      // Should be under pressure when over threshold
      expect(memoryManager.isUnderPressure()).toBe(false);

      // Add more to go over the threshold
      memoryManager.track("item3", 300);
      expect(memoryManager.isUnderPressure()).toBe(true);

      // Release to go under the threshold
      memoryManager.release("item3");
      expect(memoryManager.isUnderPressure()).toBe(false);
    });
  });

  describe("Provider Management", () => {
    let providerManager;

    beforeEach(() => {
      providerManager = new Prime.Storage.Provider.Manager();
    });

    test("should register and retrieve providers", () => {
      // Create a custom provider
      const customProvider = {
        type: "custom",
        init: jest.fn().mockResolvedValue(true),
        store: jest.fn().mockResolvedValue("id"),
        load: jest.fn().mockResolvedValue({}),
        delete: jest.fn().mockResolvedValue(true),
        exists: jest.fn().mockResolvedValue(true),
        keys: jest.fn().mockResolvedValue([]),
      };

      // Register provider
      providerManager.register(customProvider);

      // Get provider
      const provider = providerManager.getProvider("custom");
      expect(provider).toBe(customProvider);
    });

    test("should throw for invalid providers", () => {
      // Missing required methods
      const invalidProvider = {
        type: "invalid",
      };

      expect(() => providerManager.register(invalidProvider)).toThrow();
    });

    test("should list available providers", () => {
      // Register some providers
      const provider1 = {
        type: "custom1",
        init: jest.fn().mockResolvedValue(true),
        store: jest.fn().mockResolvedValue("id"),
        load: jest.fn().mockResolvedValue({}),
        delete: jest.fn().mockResolvedValue(true),
        exists: jest.fn().mockResolvedValue(true),
        keys: jest.fn().mockResolvedValue([]),
      };

      const provider2 = {
        type: "custom2",
        init: jest.fn().mockResolvedValue(true),
        store: jest.fn().mockResolvedValue("id"),
        load: jest.fn().mockResolvedValue({}),
        delete: jest.fn().mockResolvedValue(true),
        exists: jest.fn().mockResolvedValue(true),
        keys: jest.fn().mockResolvedValue([]),
      };

      providerManager.register(provider1);
      providerManager.register(provider2);

      const providers = providerManager.getAvailableProviders();
      expect(providers).toContain("custom1");
      expect(providers).toContain("custom2");
    });

    test("should throw for unknown providers", () => {
      expect(() => providerManager.getProvider("unknown")).toThrow();
    });
  });
});
