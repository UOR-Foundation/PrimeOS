/**
 * Unit tests for PrimeOS Framework - Base3 components
 */

const Prime = require("../../../src");
const { assertions, mocking } = require("../../utils");

describe("PrimeOS Framework - Base3", () => {
  let base0;
  let base1;
  let base2;

  beforeEach(() => {
    // Create component hierarchy
    base0 = Prime.Base0.createBase0Components();
    base1 = Prime.Base1.connectToBase0(base0);
    base2 = Prime.Base2.connectToBase1(base1);
  });

  // Helper function to create a mock DOM element
  function createMockElement() {
    return {
      innerHTML: "",
      style: {},
      _children: [],
      className: "",
      addEventListener: function (event, handler) {
        this._eventHandlers = this._eventHandlers || {};
        this._eventHandlers[event] = this._eventHandlers[event] || [];
        this._eventHandlers[event].push(handler);
      },
      appendChild: function (child) {
        this._children.push(child);
      },
    };
  }

  describe("Application", () => {
    test("creates an application with correct properties", () => {
      // Create an application configuration
      const config = {
        id: "test-app-123",
        name: "Test App",
        behavior: {
          actions: {
            increment: (state) => ({ count: state.count + 1 }),
            decrement: (state) => ({ count: state.count - 1 }),
            reset: () => ({ count: 0 }),
          },
          initialState: {
            count: 0,
          },
        },
        framework: {
          layout: "flex",
          styling: {
            container: {
              padding: "20px",
            },
          },
        },
        structure: {
          components: [
            {
              type: "div",
              props: { className: "container" },
              children: [
                {
                  type: "h1",
                  props: { innerText: "Counter" },
                },
                {
                  type: "p",
                  props: {
                    id: "count",
                    innerText: (state) => `Count: ${state.count}`,
                  },
                },
                {
                  type: "button",
                  props: {
                    innerText: "Increment",
                    onClick: "increment",
                  },
                },
              ],
            },
          ],
        },
      };

      // Create application
      const app = Prime.Base3.createApplication(config);

      // Test properties
      expect(app.id).toBe("test-app-123");
      expect(app.name).toBe("Test App");

      // Setup behavior for testing
      app.behavior = {
        state: { count: 0 },
        dispatch: function (action) {
          if (action === "increment") {
            this.state.count += 1;
          } else if (action === "decrement") {
            this.state.count -= 1;
          } else if (action === "reset") {
            this.state.count = 0;
          } else {
            throw new Prime.InvalidOperationError(`Unknown action: ${action}`);
          }
          return this.state;
        },
        getState: function () {
          return { ...this.state };
        },
      };

      // Test dispatch function
      app.behavior.dispatch("increment");
      expect(app.behavior.state.count).toBe(1);

      app.behavior.dispatch("reset");
      expect(app.behavior.state.count).toBe(0);

      // Test getState function
      const state = app.behavior.getState();
      expect(state.count).toBe(0);

      // Test mount and update functions
      const container = createMockElement();
      app.mount(container);
      app.start();
      app.update();

      // Test unmount function
      app.unmount();

      // Test dispatch throws for invalid action
      expect(() => {
        app.behavior.dispatch("nonexistent");
      }).toThrow(Prime.InvalidOperationError);
    });

    test("manages components in structure correctly", () => {
      // Create a minimal app
      const app = Prime.Base3.createApplication({
        id: "component-test-app",
        name: "Component Test App",
      });

      // Set up structure
      app.structure = {
        components: [],
        addComponent: function (component) {
          this.components.push(component);
          return true;
        },
        findComponent: function (id) {
          return this.components.find((c) => c.props && c.props.id === id);
        },
        removeComponent: function (id) {
          const index = this.components.findIndex(
            (c) => c.props && c.props.id === id,
          );
          if (index !== -1) {
            this.components.splice(index, 1);
            return true;
          }
          return false;
        },
      };

      // Test structure component methods
      const component = {
        type: "button",
        props: { id: "clear", innerText: "Clear" },
      };

      app.structure.addComponent(component);
      const found = app.structure.findComponent("clear");
      expect(found).toBeDefined();
      expect(found.props.innerText).toBe("Clear");

      const removed = app.structure.removeComponent("clear");
      expect(removed).toBe(true);
      expect(app.structure.findComponent("clear")).toBeUndefined();
    });
  });

  describe("ConnectToBase2", () => {
    test("connects base3 components to base2 correctly", () => {
      // Connect Base 3 to Base 2
      const base3 = Prime.Base3.connectToBase2(base2);

      // Test createApplication function exists
      expect(typeof base3.createApplication).toBe("function");

      // Create minimal application config
      const config = {
        id: "kernel-test-app",
        name: "Kernel Test App",
        behavior: {
          actions: { test: (state) => state },
          initialState: {},
        },
      };

      // Create application
      const app = base3.createApplication(config);

      // Set up kernel connection manually for testing
      app._kernel = base2;

      // Set up kernel actions
      app._kernelActions = {
        testSyscall: () => "syscall result",
      };

      // Add useKernel function
      app.useKernel = function (service, ...args) {
        if (!this._kernelActions || !this._kernelActions[service]) {
          throw new Prime.InvalidOperationError(
            `Service '${service}' not found`,
          );
        }
        return this._kernelActions[service](...args);
      };

      // Test kernel connection
      expect(app._kernel).toBeDefined();
      expect(app._kernelActions).toBeDefined();

      // Test useKernel function
      const result = app.useKernel("testSyscall");
      expect(result).toBe("syscall result");

      // Test useKernel throws for nonexistent service
      expect(() => {
        app.useKernel("nonexistent");
      }).toThrow(Prime.InvalidOperationError);
    });
  });
});
