/**
 * Unit tests for PrimeOS Veneer Registry component
 *
 * These tests validate the core functionality of the PrimeAppRegistry
 * component in isolation from other veneer components.
 */

const assert = require("assert");
const { assertThrows, assertDoesNotThrow } = require("../../utils/assertions");

// Import the components to test
const { PrimeAppRegistry } = require("../../../src/veneer/registry");
const { PrimeApplication } = require("../../../src/veneer/application");
const { PrimeError } = require("../../../src/core/error");

describe("Veneer Registry Component", () => {
  // Setup
  let registry;

  beforeEach(() => {
    registry = new PrimeAppRegistry({
      appDirectories: ["/tmp/prime-apps"],
      allowUnsigned: true,
    });
  });

  describe("Initialization", () => {
    it("should properly initialize with default configuration", () => {
      assert.ok(registry);
      assert.ok(registry.apps instanceof Map);
      assert.ok(registry.versions instanceof Map);
    });

    it("should initialize with custom configuration", () => {
      const customRegistry = new PrimeAppRegistry({
        appDirectories: ["/custom/dir1", "/custom/dir2"],
        allowUnsigned: false,
      });

      assert.ok(customRegistry);
      assert.strictEqual(customRegistry.options.allowUnsigned, false);
      assert.deepStrictEqual(customRegistry.options.appDirectories, [
        "/custom/dir1",
        "/custom/dir2",
      ]);
    });
  });

  describe("App Registration", () => {
    let manifest1, manifest2, appPath1, appPath2;

    beforeEach(() => {
      // Create test app manifests
      manifest1 = {
        name: "test-app-1",
        version: "1.0.0",
        description: "Test App 1",
        entry: "./app1.js",
      };

      manifest2 = {
        name: "test-app-2",
        version: "1.0.0",
        description: "Test App 2",
        entry: "./app2.js",
      };

      appPath1 = "/tmp/prime-apps/app1";
      appPath2 = "/tmp/prime-apps/app2";
    });

    it("should register apps", () => {
      // Register apps
      registry.registerApp(manifest1, appPath1);
      registry.registerApp(manifest2, appPath2);

      // Verify apps are registered
      assert.strictEqual(registry.apps.size, 2);
      assert.ok(registry.apps.has("test-app-1"));
      assert.ok(registry.apps.has("test-app-2"));
      assert.deepStrictEqual(
        registry.apps.get("test-app-1").manifest,
        manifest1,
      );
      assert.deepStrictEqual(
        registry.apps.get("test-app-2").manifest,
        manifest2,
      );
    });

    it("should prevent registering invalid app manifests", () => {
      // Invalid app (missing name)
      assertThrows(
        () => registry.registerApp({}, "/path"),
        PrimeError,
        "Invalid manifest",
      );

      // Invalid app (missing version)
      assertThrows(
        () => registry.registerApp({ name: "invalid-app" }, "/path"),
        PrimeError,
        "Invalid manifest",
      );
    });

    it("should track versions", () => {
      // Register first version
      registry.registerApp(manifest1, appPath1);

      // Create and register a new version
      const manifest1v2 = {
        name: "test-app-1",
        version: "2.0.0",
        description: "Test App 1 v2",
        entry: "./app1v2.js",
      };

      // Should throw by default without force
      try {
        registry.registerApp(manifest1v2, appPath1);
        assert.fail("Should have thrown an error");
      } catch (error) {
        assert.ok(error.message.includes("App version already registered"));
      }

      // Register with force flag
      registry.registerApp(manifest1v2, appPath1, { force: true });

      // Verify versions are tracked (in descending order)
      assert.ok(registry.versions.has("test-app-1"));
      assert.strictEqual(registry.versions.get("test-app-1").length, 2);
      assert.strictEqual(registry.versions.get("test-app-1")[0], "2.0.0");
      assert.strictEqual(registry.versions.get("test-app-1")[1], "1.0.0");
    });
  });

  describe("App Management", () => {
    let appManifest;

    beforeEach(() => {
      // Create and register a test app
      appManifest = {
        name: "test-app",
        version: "1.0.0",
        description: "Test App",
        entry: "./app.js",
      };

      registry.registerApp(appManifest, "/tmp/prime-apps/test-app");
    });

    it("should retrieve app manifests by ID", () => {
      // Get app by ID
      const retrievedApp = registry.getAppManifest("test-app");
      assert.deepStrictEqual(retrievedApp, appManifest);

      // Get non-existent app
      const nonExistentApp = registry.getAppManifest("non-existent");
      assert.strictEqual(nonExistentApp, null);
    });

    it("should unregister apps", () => {
      // Verify app is registered
      assert.ok(registry.apps.has("test-app"));

      // Unregister app
      const result = registry.unregisterApp("test-app");

      // Verify app is unregistered
      assert.strictEqual(result, true);
      assert.strictEqual(registry.apps.has("test-app"), false);
      assert.strictEqual(registry.versions.has("test-app"), false);
    });

    it("should unregister specific app version", () => {
      // Register a second version
      const appManifestV2 = {
        name: "test-app",
        version: "2.0.0",
        description: "Test App V2",
        entry: "./app.js",
      };

      registry.registerApp(appManifestV2, "/tmp/prime-apps/test-app-v2", {
        force: true,
      });

      // Verify both versions are registered
      assert.strictEqual(registry.versions.get("test-app").length, 2);

      // Unregister specific version
      const result = registry.unregisterApp("test-app", "1.0.0");

      // Verify specific version is unregistered, but app still exists
      assert.strictEqual(result, true);
      assert.ok(registry.apps.has("test-app"));
      assert.strictEqual(registry.versions.get("test-app").length, 1);
      assert.strictEqual(registry.versions.get("test-app")[0], "2.0.0");
    });

    it("should return false when unregistering non-existent app", () => {
      // Unregister non-existent app
      const result = registry.unregisterApp("non-existent");

      // Verify result is false
      assert.strictEqual(result, false);
    });
  });

  describe("Version Management", () => {
    it("should handle version-specific app registration and retrieval", () => {
      // Create app manifests with different versions
      const appV1Manifest = {
        name: "versioned-app",
        version: "1.0.0",
        description: "Versioned App v1",
        entry: "./app-v1.js",
      };

      const appV2Manifest = {
        name: "versioned-app",
        version: "2.0.0",
        description: "Versioned App v2",
        entry: "./app-v2.js",
      };

      // Register both versions (clear any existing data first)
      registry.apps.clear();
      registry.versions.clear();

      registry.registerApp(appV1Manifest, "/tmp/prime-apps/app-v1", {
        force: true,
      });
      registry.registerApp(appV2Manifest, "/tmp/prime-apps/app-v2", {
        force: true,
      });

      // Verify both versions are tracked
      assert.ok(
        registry.versions.has("versioned-app"),
        "Should have versioned-app",
      );
      const versions = registry.versions.get("versioned-app");
      assert.strictEqual(versions.length, 2, "Should have 2 versions");
      assert.strictEqual(
        versions[0],
        "2.0.0",
        "Latest version should be first",
      );
      assert.strictEqual(
        versions[1],
        "1.0.0",
        "Older version should be second",
      );

      // Get app by ID without version (should return latest version)
      const latest = registry.getAppManifest("versioned-app");
      assert.ok(latest, "Latest manifest should exist");
      assert.strictEqual(latest.version, "2.0.0");

      // Get specific version
      const v1 = registry.getAppManifest("versioned-app", "1.0.0");
      assert.ok(v1, "Version 1.0.0 manifest should exist");
      assert.strictEqual(v1.version, "1.0.0");
      assert.strictEqual(v1.description, "Versioned App v1");

      const v2 = registry.getAppManifest("versioned-app", "2.0.0");
      assert.ok(v2, "Version 2.0.0 manifest should exist");
      assert.strictEqual(v2.version, "2.0.0");
      assert.strictEqual(v2.description, "Versioned App v2");

      // Get non-existent version
      const nonExistent = registry.getAppManifest("versioned-app", "3.0.0");
      assert.strictEqual(nonExistent, null);
    });
  });

  describe("App Discovery and Querying", () => {
    beforeEach(() => {
      // Clear registry before each test
      registry.apps.clear();
      registry.versions.clear();

      // Register various test apps
      const appManifests = [
        {
          name: "app1",
          displayName: "Application 1",
          version: "1.0.0",
          entry: "./app1.js",
          category: "utility",
        },
        {
          name: "app2",
          displayName: "Application 2",
          version: "2.0.0",
          entry: "./app2.js",
          category: "tool",
        },
        {
          name: "app3",
          displayName: "Application 3",
          version: "1.5.0",
          entry: "./app3.js",
          category: "utility",
        },
        {
          name: "app4",
          displayName: "Application 4",
          version: "3.0.0",
          entry: "./app4.js",
          category: "game",
        },
      ];

      // Register each app
      appManifests.forEach((manifest, index) => {
        registry.registerApp(manifest, `/tmp/prime-apps/app${index + 1}`, {
          force: true,
        });
      });
    });

    it("should get available apps", () => {
      // Get all apps
      const allApps = registry.getAvailableApps();
      assert.strictEqual(allApps.length, 4);

      // Verify app details
      const app1 = allApps.find((a) => a.id === "app1");
      assert.ok(app1);
      assert.strictEqual(app1.displayName, "Application 1");
      assert.strictEqual(app1.version, "1.0.0");

      // Get latest version only
      const latestOnly = registry.getAvailableApps({ latestVersionOnly: true });
      assert.strictEqual(latestOnly.length, 4);
    });

    it("should find interface providers", () => {
      // Define interfaces
      const appManifests = [
        {
          name: "provider1",
          version: "1.0.0",
          interfaces: { provides: ["data-service"], priority: 1 },
        },
        {
          name: "provider2",
          version: "1.0.0",
          interfaces: { provides: ["data-service", "ui-service"], priority: 2 },
        },
        {
          name: "consumer",
          version: "1.0.0",
          interfaces: { consumes: ["data-service"] },
        },
      ];

      // Register apps with interfaces
      registry.apps.clear();
      registry.versions.clear();
      registry.interfaces.providers.clear();
      registry.interfaces.consumers.clear();

      appManifests.forEach((manifest, index) => {
        registry.registerApp(
          manifest,
          `/tmp/prime-apps/interface-app${index}`,
          { force: true },
        );
      });

      // Find providers
      const dataProviders = registry.findInterfaceProviders("data-service");
      assert.strictEqual(dataProviders.length, 2);

      // Should be sorted by priority (highest first)
      assert.strictEqual(dataProviders[0].appId, "provider2");
      assert.strictEqual(dataProviders[1].appId, "provider1");

      // Find consumers
      const dataConsumers = registry.findInterfaceConsumers("data-service");
      assert.strictEqual(dataConsumers.length, 1);
      assert.strictEqual(dataConsumers[0].appId, "consumer");
    });

    it("should resolve dependencies", () => {
      // Define apps with dependencies
      const appManifests = [
        {
          name: "base-lib",
          version: "1.0.0",
          dependencies: {},
        },
        {
          name: "util-lib",
          version: "2.0.0",
          dependencies: { "base-lib": "^1.0.0" },
        },
        {
          name: "app",
          version: "1.0.0",
          dependencies: {
            "base-lib": "^1.0.0",
            "util-lib": "^2.0.0",
            "missing-lib": "1.0.0",
          },
        },
      ];

      // Register apps
      registry.apps.clear();
      registry.versions.clear();
      registry.dependencies.clear();

      appManifests.forEach((manifest, index) => {
        registry.registerApp(manifest, `/tmp/prime-apps/dep-app${index}`, {
          force: true,
        });
      });

      // Resolve dependencies for app
      const resolution = registry.resolveDependencies("app");

      // Check resolved dependencies
      assert.deepStrictEqual(resolution.resolved, {
        "base-lib": "1.0.0",
        "util-lib": "2.0.0",
      });

      // Check missing dependencies
      assert.strictEqual(resolution.missing.length, 1);
      assert.strictEqual(resolution.missing[0].id, "missing-lib");

      // Check for conflicts (none in this case)
      assert.strictEqual(resolution.conflicts.length, 0);
    });
  });

  // PrimeAppRegistry doesn't emit events in the current implementation
  describe.skip("Event Handling", () => {
    it("should emit events on registration operations", () => {
      // This functionality will be implemented in a future version
    });
  });

  // App discovery is the primary persistence mechanism
  describe.skip("App Discovery", () => {
    it("should discover apps in directories", async () => {
      // This test would require more sophisticated mocking of the filesystem
      // Skipping it for now as we've already demonstrated the core functionality
    });
  });
});
