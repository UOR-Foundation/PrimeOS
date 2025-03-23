/**
 * Unit tests for PrimeOS Framework - Base1 components
 */

const Prime = require("../../../src");
const { assertions, mocking } = require("../../utils");

describe("PrimeOS Framework - Base1", () => {
  let base0;
  
  beforeEach(() => {
    // Create Base 0 components for testing
    base0 = Prime.Base0.createBase0Components();
  });
  
  describe("RuntimeModel", () => {
    test("creates a runtime model with correct properties", () => {
      // Create Runtime Model
      const runtime = Prime.Base1.createRuntimeModel({}).connectToBase0(base0);

      // Test properties
      expect(runtime.type).toBe("runtime");
      expect(runtime.embedding).toBeDefined();
      expect(runtime.logic).toBeDefined();
      expect(runtime.representation).toBeDefined();
      expect(runtime.processor).toBeDefined();

      // Create a test model
      const model = {
        process: (data) => data * 2,
        initialize: function () {
          this.initialized = true;
        },
        cleanup: function () {
          this.cleaned = true;
        },
      };

      // Test start function
      const started = runtime.start(model);
      expect(started._running).toBeTruthy();
      expect(started.initialized).toBeTruthy();

      // Test run function
      const result = runtime.run(model, 5);
      expect(result).toBe(10);

      // Test stop function
      const stopped = runtime.stop(model);
      expect(model._running).toBeFalsy();
      expect(model.cleaned).toBeTruthy();
      expect(stopped).toBe(true);
    });
  });

  describe("ObservationModel", () => {
    test("creates an observation model with correct properties", () => {
      // Create data sources
      const sources = [
        {
          id: "source1",
          data: [
            { id: 1, value: "one" },
            { id: 2, value: "two" },
          ],
        },
        {
          id: "source2",
          data: [{ id: 3, value: "three" }],
          subscribe: (options) => ({
            unsubscribe: () => {},
          }),
        },
      ];

      // Create Observation Model
      const observation = Prime.Base1.createObservationModel({
        sources,
      });

      // Test properties
      expect(observation.type).toBe("observation");
      expect(observation.sources.length).toBe(2);

      // Test fetch function
      const results = observation.fetch({ id: 1 });
      expect(results.length).toBe(1);
      expect(results[0].value).toBe("one");

      // Test observe function
      const subscription = observation.observe("source2");
      expect(subscription).toBeDefined();
      expect(typeof subscription.unsubscribe).toBe("function");

      // Test resolve function returns null for unknown reference
      const resolved = observation.resolve("unknown");
      expect(resolved).toBeNull();

      // Test observe throws for invalid source
      expect(() => {
        observation.observe("nonexistent");
      }).toThrow(Prime.InvalidOperationError);
    });
  });

  describe("InteractionModel", () => {
    test("creates an interaction model with correct properties", () => {
      // Create mutations and validators
      const mutations = [
        {
          name: "increment",
          apply: (obj) => ({ ...obj, value: obj.value + 1 }),
        },
        {
          name: "decrement",
          apply: (obj) => ({ ...obj, value: obj.value - 1 }),
        },
      ];

      const validators = [(obj) => obj.value >= 0, (obj) => obj.value <= 100];

      // Create Interaction Model
      const interaction = Prime.Base1.createInteractionModel({
        mutations,
        validators,
      });

      // Test properties
      expect(interaction.type).toBe("interaction");
      expect(interaction.mutations.length).toBe(2);
      expect(interaction.validators.length).toBe(2);

      // Test mutate function
      const obj = { value: 5 };
      const mutated = interaction.mutate(obj, "increment");
      expect(mutated.value).toBe(6);

      // Test validate function
      expect(interaction.validate({ value: 50 })).toBe(true);

      // Test validate throws for invalid object
      expect(() => {
        interaction.validate({ value: -1 });
      }).toThrow(Prime.ValidationError);

      // Test mutate throws for invalid mutation
      expect(() => {
        interaction.mutate(obj, "nonexistent");
      }).toThrow(Prime.InvalidOperationError);
    });
  });

  describe("RepresentationModel", () => {
    test("creates a representation model with correct properties", () => {
      // Create renderers
      const renderers = [
        {
          canRender: (obj, target) =>
            typeof obj === "string" && target && target.innerHTML !== undefined,
          render: (obj, target) => {
            target.innerHTML = obj;
            return true;
          },
        },
      ];

      // Create Representation Model
      const representation = Prime.Base1.createRepresentationModel({
        renderers,
      });

      // Test properties
      expect(representation.type).toBe("representation");
      expect(representation.renderers.length).toBe(1);

      // Test present function
      const obj = { name: "Test", value: 42 };
      const presented = representation.present(obj, "string");
      expect(typeof presented).toBe("string");
      expect(presented.includes("Test")).toBe(true);

      // Test render function
      const target = { innerHTML: "" };
      const rendered = representation.render("Hello World", target);
      expect(target.innerHTML).toBe("Hello World");
      expect(rendered).toBe(true);

      // Test render throws for no suitable renderer
      expect(() => {
        representation.render({}, {});
      }).toThrow(Prime.InvalidOperationError);
    });
  });

  describe("ConnectToBase0", () => {
    test("connects base1 components to base0 correctly", () => {
      // Connect Base 1 to Base 0
      const base1 = Prime.Base1.connectToBase0(base0);

      // Test all components exist
      expect(base1.runtime).toBeDefined();
      expect(base1.observation).toBeDefined();
      expect(base1.interaction).toBeDefined();
      expect(base1.representation).toBeDefined();

      // Test connections
      expect(base1.runtime.embedding).toBe(base0.embedding);
      expect(base1.runtime.logic).toBe(base0.logic);
      expect(base1.runtime.representation).toBe(base0.representation);
      expect(base1.runtime.processor).toBe(base0.processor);
    });
  });
});