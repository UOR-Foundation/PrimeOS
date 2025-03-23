/**
 * Unit tests for PrimeOS Framework - Base0 components
 */

const Prime = require("../../../src");
const { assertions, mocking } = require("../../utils");

describe("PrimeOS Framework - Base0", () => {
  describe("EmbeddingModel", () => {
    test("creates an embedding model with correct properties", () => {
      const embedding = Prime.Base0.createEmbeddingModel({
        dimensions: 5,
        metric: "euclidean",
      });

      // Test properties
      expect(embedding.type).toBe("embedding");
      expect(embedding.dimensions).toBe(5);
      expect(embedding.metric).toBe("euclidean");

      // Test embed function
      const embeddingVector = embedding.embed("test");
      expect(Array.isArray(embeddingVector)).toBe(true);
      expect(embeddingVector.length).toBe(5);

      // Test distance function
      const distance = embedding.distance([1, 2, 3, 4, 5], [5, 4, 3, 2, 1]);
      expect(distance).toBeGreaterThan(0);
    });
  });

  describe("LogicModel", () => {
    test("creates a logic model with correct properties", () => {
      // Create rules and constraints
      const rules = [
        (data) => ({ ...data, processed: true }),
        (data) => ({ ...data, timestamp: 123 }),
      ];

      const constraints = [
        (data) => data.value > 0,
        (data) => data.processed === true,
      ];

      const logic = Prime.Base0.createLogicModel({
        rules,
        constraints,
      });

      // Test properties
      expect(logic.type).toBe("logic");
      expect(logic.rules.length).toBe(2);
      expect(logic.constraints.length).toBe(2);

      // Test apply function
      const data = { value: 5 };
      const processed = logic.apply(data);

      expect(processed.processed).toBe(true);
      expect(processed.timestamp).toBe(123);

      // Test validate function
      const validData = { value: 10, processed: true };
      expect(logic.validate(validData)).toBe(true);

      const invalidData = { value: -5, processed: true };
      expect(logic.validate(invalidData)).toBe(false);
    });
  });

  describe("RepresentationModel", () => {
    test("creates a representation model with correct properties", () => {
      // Create transformations and formats
      const transformations = [
        { name: "uppercase", apply: (data) => data.toUpperCase() },
        { name: "reverse", apply: (data) => data.split("").reverse().join("") },
      ];

      const formats = {
        json: (data) => JSON.stringify(data),
        html: (data) => `<div>${data}</div>`,
      };

      const representation = Prime.Base0.createRepresentationModel({
        transformations,
        formats,
      });

      // Test properties
      expect(representation.type).toBe("representation");
      expect(representation.transformations.length).toBe(2);
      expect(Object.keys(representation.formats).length).toBe(2);

      // Test transform function
      const transformed = representation.transform("hello", "uppercase");
      expect(transformed).toBe("HELLO");

      // Test represent function
      const represented = representation.represent({ value: "test" }, "json");
      expect(represented).toBe('{"value":"test"}');

      // Test transform throws for invalid transformation
      expect(() => {
        representation.transform("hello", "nonexistent");
      }).toThrow(Prime.InvalidOperationError);

      // Test represent throws for invalid format
      expect(() => {
        representation.represent({}, "nonexistent");
      }).toThrow(Prime.InvalidOperationError);
    });
  });

  describe("Processor", () => {
    test("creates a processor with correct properties", () => {
      // Create operations
      const operations = [
        { name: "add5", apply: (x) => x + 5 },
        { name: "double", apply: (x) => x * 2 },
      ];

      const processor = Prime.Base0.createProcessor({
        operations,
      });

      // Test properties
      expect(processor.type).toBe("processor");
      expect(processor.operations.length).toBe(2);

      // Test process function
      const result1 = processor.process(10, "add5");
      expect(result1).toBe(15);

      const result2 = processor.process(10, "double");
      expect(result2).toBe(20);

      // Test compose function
      const composed = processor.compose("add5", "double");
      const result3 = composed(10);
      expect(result3).toBe(30);

      // Test process throws for invalid operation
      expect(() => {
        processor.process(10, "nonexistent");
      }).toThrow(Prime.InvalidOperationError);
    });
  });

  describe("Base0Components", () => {
    test("creates all Base0 components correctly", () => {
      const components = Prime.Base0.createBase0Components();

      // Test all components exist
      expect(components.embedding).toBeDefined();
      expect(components.logic).toBeDefined();
      expect(components.representation).toBeDefined();
      expect(components.processor).toBeDefined();

      // Test components are connected
      expect(components.embedding._components).toBeDefined();
      expect(components.logic._components).toBeDefined();
      expect(components.representation._components).toBeDefined();
      expect(components.processor._components).toBeDefined();
    });
  });
});
