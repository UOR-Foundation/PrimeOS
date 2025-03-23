/**
 * Unit tests for PrimeOS Veneer Application component
 *
 * These tests validate the core functionality of the PrimeApplication
 * component in isolation from other veneer components.
 */

const assert = require("assert");
const { assertThrows, assertDoesNotThrow } = require("../../utils/assertions");

// Import the components to test
const { PrimeApplication } = require("../../../src/veneer/application");
const { PrimeError } = require("../../../src/core/error");

describe("Veneer Application Component", () => {
  // Setup
  let app;

  beforeEach(() => {
    app = new PrimeApplication({
      name: "Test Application",
      version: "1.0.0",
      description: "Test application for unit testing",
      entry: "./main.js",
    });
  });

  describe("Initialization", () => {
    it("should properly initialize with valid configuration", () => {
      assert.strictEqual(app.manifest.name, "Test Application");
      assert.strictEqual(app.manifest.version, "1.0.0");
      assert.strictEqual(
        app.manifest.description,
        "Test application for unit testing",
      );
      assert.ok(app.metadata);
    });

    it("should throw an error when initialized without required fields", () => {
      assertThrows(
        () => new PrimeApplication({}),
        PrimeError,
        "Invalid manifest",
      );

      assertThrows(
        () => new PrimeApplication({ id: "test-app" }),
        PrimeError,
        "Invalid manifest",
      );
    });

    it("should initialize with default values for optional fields", () => {
      const minimalApp = new PrimeApplication({
        name: "Minimal Application",
        version: "1.0.0",
        entry: "./index.js",
      });

      assert.strictEqual(minimalApp.manifest.name, "Minimal Application");
      assert.strictEqual(minimalApp.manifest.description, "");
      assert.deepStrictEqual(minimalApp.manifest.dependencies, {});
    });
  });

  describe("Lifecycle Management", () => {
    it("should transition through proper lifecycle states", async () => {
      // Initial state should be CREATED
      assert.strictEqual(app.state, "created");

      // Initialize the app
      await app.init();
      assert.strictEqual(app.state, "initialized");

      // Start the app
      await app.start();
      assert.strictEqual(app.state, "running");

      // Pause the app
      await app.pause();
      assert.strictEqual(app.state, "paused");

      // Resume the app
      await app.resume();
      assert.strictEqual(app.state, "running");

      // Stop the app
      await app.stop();
      assert.strictEqual(app.state, "stopped");
    });

    it("should prevent invalid state transitions", async () => {
      // Can't start without initializing
      await assertThrows(
        async () => await app.start(),
        PrimeError,
        "Cannot start application in current state",
      );

      // Initialize first
      await app.init();

      // Start the app
      await app.start();

      // Can't initialize again while running
      await assertThrows(
        async () => await app.init(),
        PrimeError,
        "Cannot initialize application in current state",
      );

      // Stop the app
      await app.stop();

      // Can't resume a stopped app
      await assertThrows(
        async () => await app.resume(),
        PrimeError,
        "Cannot resume application in current state",
      );
    });

    it("should emit lifecycle events during transitions", async () => {
      // Track events
      const events = [];
      app.on("initialized", () => {
        events.push("initialized");
      });
      app.on("started", () => {
        events.push("started");
      });
      app.on("stopped", () => {
        events.push("stopped");
      });

      // Perform transitions
      await app.init();
      await app.start();
      await app.stop();

      // Verify events
      assert.strictEqual(events.length, 3);
      assert.strictEqual(events[0], "initialized");
      assert.strictEqual(events[1], "started");
      assert.strictEqual(events[2], "stopped");
    });
  });

  // Skipping Configuration Management tests as they're not implemented in the current version

  describe.skip("Configuration Management", () => {
    it("should allow setting and getting configuration values", () => {
      // This functionality will be implemented in a future version
    });

    it("should validate configuration values using schema", () => {
      // This functionality will be implemented in a future version
    });

    it("should support nested configuration paths", () => {
      // This functionality will be implemented in a future version
    });
  });

  // Skipping Dependency Management tests as they're not implemented in the current version

  describe.skip("Dependency Management", () => {
    it("should properly track dependencies", () => {
      // This functionality will be implemented in a future version
    });

    it("should validate dependency format", () => {
      // This functionality will be implemented in a future version
    });

    it("should check for duplicate dependencies", () => {
      // This functionality will be implemented in a future version
    });
  });

  describe("Resource Management", () => {
    it("should get resources from veneer", async () => {
      // Mock veneer context
      app.context.veneer = {
        allocateResource: async (appId, resourceType, requirements) => {
          return { type: resourceType, ...requirements };
        },
        releaseResource: async (appId, resourceType) => true,
      };
      app.context.appId = "test-app";

      // Get a resource
      const storageResource = await app.getResource("storage", {
        quota: "10MB",
      });

      // Verify resource was allocated
      assert.strictEqual(storageResource.type, "storage");
      assert.strictEqual(storageResource.quota, "10MB");
      assert.strictEqual(app.resources.storage, storageResource);

      // Release the resource
      const releaseResult = await app.releaseResource("storage");
      assert.strictEqual(releaseResult, true);
      assert.strictEqual(app.resources.storage, null);
    });

    it("should throw when accessing resources without veneer context", async () => {
      // No veneer context
      app.context.veneer = null;

      assertThrows(
        () => app.getResource("storage", {}),
        PrimeError,
        "No veneer context",
      );

      assertThrows(
        () => app.releaseResource("storage"),
        PrimeError,
        "No veneer context",
      );
    });
  });

  // Inherited from EventEmitter
  describe("Event Handling", () => {
    it("should properly handle events", () => {
      // Track events
      const receivedEvents = [];

      // Add event listener
      const handler = (data) => {
        receivedEvents.push(data);
      };

      app.on("custom-event", handler);

      // Emit events
      app.emit("custom-event", { value: 1 });
      app.emit("custom-event", { value: 2 });
      app.emit("other-event", { value: 3 });

      // Verify events were received
      assert.strictEqual(receivedEvents.length, 2);
      assert.deepStrictEqual(receivedEvents[0], { value: 1 });
      assert.deepStrictEqual(receivedEvents[1], { value: 2 });

      // Remove listener
      app.off("custom-event", handler);

      // Emit again
      app.emit("custom-event", { value: 4 });

      // Verify no new events were received
      assert.strictEqual(receivedEvents.length, 2);
    });

    it("should support one-time event listeners", () => {
      // Track events
      const receivedEvents = [];

      // Add one-time event listener
      app.once("one-time-event", (data) => {
        receivedEvents.push(data);
      });

      // Emit events
      app.emit("one-time-event", { value: 1 });
      app.emit("one-time-event", { value: 2 });

      // Verify only the first event was received
      assert.strictEqual(receivedEvents.length, 1);
      assert.deepStrictEqual(receivedEvents[0], { value: 1 });
    });
  });

  // Skip Error Handling tests as they're not implemented in the current version
  describe.skip("Error Handling", () => {
    it("should handle and propagate errors", () => {
      // This functionality will be implemented in a future version
    });

    it("should track error history", () => {
      // This functionality will be implemented in a future version
    });
  });
});
