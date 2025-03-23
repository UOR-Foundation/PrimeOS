/**
 * Browser Optimization Integration Tests for PrimeOS Veneer components
 *
 * These tests validate the browser-specific optimizations for veneer components,
 * focusing on performance, memory usage, and rendering efficiency.
 */

const assert = require("assert");
const Environments = require("../../utils/environments");

// Skip all tests if not running in a browser environment
const runInBrowser = Environments.runIn("browser", (test) => test());

describe("Veneer Browser Optimizations", () => {
  runInBrowser(() => {
    // Test components
    let application;
    let registry;
    let loader;
    let resources;

    // Test data
    const largeDataSets = {};
    const renderTargets = {};

    before(async () => {
      // Import browser-specific components
      const PrimeApp = require("../../../src/veneer/application");
      const PrimeAppRegistry = require("../../../src/veneer/app-registry");
      const PrimeAppLoader = require("../../../src/veneer/loader");
      const ResourceManager = require("../../../src/veneer/resources");

      // Initialize components
      application = new PrimeApp({
        id: "browser-test-app",
        name: "Browser Test Application",
        version: "1.0.0",
        entryPoint: "./browser-test.js",
      });

      registry = new PrimeAppRegistry();
      loader = new PrimeAppLoader();
      resources = new ResourceManager();

      // Generate test data
      largeDataSets.smallMatrix = generateMatrix(100, 100);
      largeDataSets.mediumMatrix = generateMatrix(500, 500);
      largeDataSets.largeMatrix = generateMatrix(1000, 1000);

      // Create render targets
      renderTargets.container = document.createElement("div");
      renderTargets.container.id = "test-container";
      document.body.appendChild(renderTargets.container);
    });

    after(() => {
      // Clean up render targets
      if (renderTargets.container && renderTargets.container.parentNode) {
        renderTargets.container.parentNode.removeChild(renderTargets.container);
      }
    });

    describe("DOM Rendering Optimizations", () => {
      it("should use requestAnimationFrame for DOM updates", () => {
        // Mock requestAnimationFrame to track calls
        const originalRAF = window.requestAnimationFrame;
        let rafCalled = false;

        window.requestAnimationFrame = (callback) => {
          rafCalled = true;
          return originalRAF(callback);
        };

        // Trigger a rendering operation
        application.render(renderTargets.container);

        // Restore original function
        window.requestAnimationFrame = originalRAF;

        // Verify RAF was used
        assert.ok(
          rafCalled,
          "requestAnimationFrame should be used for DOM updates",
        );
      });

      it("should batch DOM operations for efficient rendering", () => {
        // Track DOM operations
        let domOperations = 0;
        const observer = new MutationObserver(() => {
          domOperations++;
        });

        // Start observing the container
        observer.observe(renderTargets.container, {
          childList: true,
          subtree: true,
          attributes: true,
        });

        // Perform multiple updates that should be batched
        application.updateUI([
          { type: "add", element: "div", content: "Test 1" },
          { type: "add", element: "div", content: "Test 2" },
          { type: "add", element: "div", content: "Test 3" },
          { type: "add", element: "div", content: "Test 4" },
          { type: "add", element: "div", content: "Test 5" },
        ]);

        // Force a layout recalculation
        const dummy = renderTargets.container.offsetHeight;

        // Stop observing
        observer.disconnect();

        // If DOM operations are properly batched, we should have
        // fewer operations than the number of updates
        assert.ok(
          domOperations < 5,
          `DOM operations should be batched (got ${domOperations} operations for 5 updates)`,
        );
      });

      it("should use DocumentFragment for bulk insertions", () => {
        // Create elements to insert
        const elements = [];
        for (let i = 0; i < 100; i++) {
          const div = document.createElement("div");
          div.textContent = `Element ${i}`;
          elements.push(div);
        }

        // Track DOM operations
        let domOperations = 0;
        const observer = new MutationObserver(() => {
          domOperations++;
        });

        // Start observing the container
        observer.observe(renderTargets.container, {
          childList: true,
          subtree: false,
        });

        // Clear container
        renderTargets.container.innerHTML = "";

        // Perform bulk insertion
        application.insertElements(renderTargets.container, elements);

        // Stop observing
        observer.disconnect();

        // If DocumentFragment is used, we should have 1 or 2 operations
        assert.ok(
          domOperations <= 2,
          `DocumentFragment should be used for bulk insertions (got ${domOperations} operations)`,
        );

        // Verify all elements were added
        assert.strictEqual(
          renderTargets.container.children.length,
          100,
          "All elements should be inserted",
        );
      });
    });

    describe("Memory Optimizations", () => {
      it("should use object pooling for frequent operations", async () => {
        // Create a measurement for memory usage
        const memoryBefore = await getMemoryUsage();

        // Perform operations that should use object pooling
        for (let i = 0; i < 1000; i++) {
          application.processEvent({ type: "test", data: { value: i } });
        }

        // Measure memory again
        const memoryAfter = await getMemoryUsage();

        // Calculate growth - should be modest if pooling is used
        const growth = memoryAfter - memoryBefore;

        // If object pooling is used effectively, memory growth should be limited
        assert.ok(
          growth < 1000000, // 1MB max growth
          `Memory growth should be limited with object pooling (grew by ${formatBytes(growth)})`,
        );
      });

      it("should properly clean up resources when components are destroyed", async () => {
        // Create a temporary application
        const tempApp = new PrimeApp({
          id: "temp-app",
          name: "Temporary App",
          version: "1.0.0",
          entryPoint: "./temp.js",
        });

        // Add some resources
        for (let i = 0; i < 10; i++) {
          tempApp.registerResource({
            id: `resource-${i}`,
            type: "data",
            data: new ArrayBuffer(1000000), // 1MB buffer
          });
        }

        // Force a garbage collection cycle if available
        if (window.gc) {
          window.gc();
        }

        // Measure memory
        const memoryBefore = await getMemoryUsage();

        // Destroy the app
        tempApp.destroy();

        // Force another garbage collection cycle
        if (window.gc) {
          window.gc();
        }

        // Measure memory again
        const memoryAfter = await getMemoryUsage();

        // Verify memory was freed
        assert.ok(
          memoryAfter <= memoryBefore + 1000000, // Allow 1MB overhead
          "Resources should be properly cleaned up when components are destroyed",
        );
      });
    });

    describe("Storage Optimizations", () => {
      it("should use IndexedDB for large data sets", async () => {
        // Mock IndexedDB API to track usage
        const originalIndexedDB = window.indexedDB;
        let indexedDBUsed = false;

        // Override open method
        const originalOpen = window.indexedDB.open;
        window.indexedDB.open = function (name, version) {
          indexedDBUsed = true;
          return originalOpen.call(this, name, version);
        };

        // Store a large dataset
        await resources.storeData("large-matrix", largeDataSets.largeMatrix);

        // Restore original
        window.indexedDB.open = originalOpen;

        // Verify IndexedDB was used for large dataset
        assert.ok(
          indexedDBUsed,
          "IndexedDB should be used for storing large data sets",
        );
      });

      it("should use localStorage for small frequent data", () => {
        // Mock localStorage to track usage
        const originalSetItem = window.localStorage.setItem;
        let localStorageUsed = false;

        window.localStorage.setItem = function (key, value) {
          localStorageUsed = true;
          return originalSetItem.call(this, key, value);
        };

        // Store small frequent data
        resources.storePreference("theme", "dark");

        // Restore original
        window.localStorage.setItem = originalSetItem;

        // Verify localStorage was used
        assert.ok(
          localStorageUsed,
          "localStorage should be used for small frequent data",
        );
      });
    });

    describe("Browser-Specific Performance Optimizations", () => {
      it("should use Web Workers for heavy computations", async () => {
        // Mock Worker constructor to track creation
        const originalWorker = window.Worker;
        let workerCreated = false;

        window.Worker = function (scriptUrl) {
          workerCreated = true;
          return new originalWorker(scriptUrl);
        };

        // Perform heavy computation
        await application.processLargeDataset(largeDataSets.largeMatrix);

        // Restore original
        window.Worker = originalWorker;

        // Verify a Web Worker was used
        assert.ok(
          workerCreated,
          "Web Workers should be used for heavy computations",
        );
      });

      it("should use requestIdleCallback for non-critical tasks", () => {
        // Mock requestIdleCallback
        const originalRIC =
          window.requestIdleCallback ||
          function (cb) {
            setTimeout(cb, 0);
          };
        let ricCalled = false;

        window.requestIdleCallback = function (callback) {
          ricCalled = true;
          return originalRIC(callback);
        };

        // Perform non-critical task
        application.runBackgroundTask(() => {
          // Background task
          console.log("Background task running");
        });

        // Restore original
        window.requestIdleCallback = originalRIC;

        // Verify requestIdleCallback was used
        assert.ok(
          ricCalled,
          "requestIdleCallback should be used for non-critical tasks",
        );
      });
    });
  });
});

// Helper function to generate a test matrix
function generateMatrix(rows, cols) {
  const matrix = [];
  for (let i = 0; i < rows; i++) {
    const row = [];
    for (let j = 0; j < cols; j++) {
      row.push(Math.random());
    }
    matrix.push(row);
  }
  return matrix;
}

// Helper function to get memory usage
async function getMemoryUsage() {
  // Use performance.memory if available (Chrome)
  if (window.performance && window.performance.memory) {
    return window.performance.memory.usedJSHeapSize;
  }

  // Fallback - less accurate
  return 0;
}

// Helper function to format bytes
function formatBytes(bytes) {
  if (bytes === 0) return "0 Bytes";

  const k = 1024;
  const sizes = ["Bytes", "KB", "MB", "GB", "TB"];
  const i = Math.floor(Math.log(Math.abs(bytes)) / Math.log(k));

  return parseFloat((bytes / Math.pow(k, i)).toFixed(2)) + " " + sizes[i];
}
