/**
 * Base3 - Connection to Base2
 *
 * This module connects the Application Layer (Base3) to the Kernel (Base2).
 * It provides:
 * - Application Layer integration with Base2 resources
 * - Syscall access for applications
 * - Resource binding and access control
 */

const Prime = require("../../core/prime.js");
const { Utils } = Prime;
// Import Base3 modules directly to avoid circular imports
const createApplication = require("./application");
const createComponent = require("./component");
const createFramework = require("./framework");

/**
 * Connect Base3 (Application) to Base2 (Kernel)
 * @param {Object} base2 - Base2 components
 * @returns {Object} Integrated Base3 components
 */
function connectToBase2(base2) {
  // Basic validation
  if (
    !base2 ||
    !base2.systemManager ||
    !base2.resourceClient ||
    !base2.applicationManager
  ) {
    throw new Prime.ValidationError("Invalid Base2 components", {
      context: { base2 },
    });
  }

  // Create Base3 components directly
  const base3 = {
    createApplication: function (options) {
      return createApplication(options);
    },

    createComponent: function (options) {
      return createComponent(options);
    },

    createFramework: function (options) {
      return createFramework(options);
    },
  };

  // Create application wrapper with resource access
  const createApplicationWithResources = function (options) {
    // Ensure application has an ID
    if (!options.id) {
      options.id = `app-${Utils.uuid().substring(0, 8)}`;
    }

    // Create the base application
    const app = base3.createApplication(options);

    // Set up kernel connection
    app._kernel = base2;

    // Set up kernel actions
    app._kernelActions = {
      // Resource actions
      startModel: (model, modelOptions) =>
        base2.resourceClient.startModel(model, modelOptions),
      stopModel: (model, modelOptions) =>
        base2.resourceClient.stopModel(model, modelOptions),
      getModel: (modelId) => base2.resourceClient.getModel(modelId),
      runModel: (model, input, runOptions) =>
        base2.resourceClient.runModel(model, input, runOptions),

      // Application actions
      loadBundle: (bundle) => base2.applicationManager.loadBundle(bundle),
      unloadBundle: (bundleId) =>
        base2.applicationManager.unloadBundle(bundleId),
      getBundle: (bundleId) => base2.applicationManager.getBundle(bundleId),

      // System actions
      allocateResource: (type, config) =>
        base2.systemManager.allocateResource(type, config),
      freeResource: (address) => base2.systemManager.freeResource(address),
      getResourceUsage: () => base2.systemManager.getResourceUsage(),
    };

    // Enhance with resource access methods
    app.allocateMemory = function (size, allocOptions = {}) {
      // Require syscall permissions
      if (!options.permissions || !options.permissions.includes("memory")) {
        throw new Prime.SecurityError(
          "Application does not have memory allocation permission",
          {
            context: { appId: app.id, permissions: options.permissions },
          },
        );
      }

      // Add application context to allocation
      const enhancedOptions = {
        ...allocOptions,
        processId: app.id,
        purpose: allocOptions.purpose || "application",
      };

      // Use system manager to allocate memory
      return base2.systemManager.allocateMemory(size, enhancedOptions);
    };

    // Add syscall capability
    app.syscall = function (name, ...args) {
      // Validate syscall permissions
      if (!options.permissions || !options.permissions.includes("syscall")) {
        throw new Prime.SecurityError(
          "Application does not have syscall permission",
          {
            context: { appId: app.id, permissions: options.permissions },
          },
        );
      }

      // Add application context to syscall
      return base2.syscall(name, { appId: app.id }, ...args);
    };

    // Add resource client access
    app.getResourceClient = function () {
      // Validate resource access permissions
      if (!options.permissions || !options.permissions.includes("resources")) {
        throw new Prime.SecurityError(
          "Application does not have resource access permission",
          {
            context: { appId: app.id, permissions: options.permissions },
          },
        );
      }

      // Return the resource client with application context
      return {
        startModel: (model) =>
          base2.resourceClient.startModel(model, { appId: app.id }),
        stopModel: (modelId) =>
          base2.resourceClient.stopModel(modelId, { appId: app.id }),
        getModel: (modelId) =>
          base2.resourceClient.getModel(modelId, { appId: app.id }),
        queryModels: (query) =>
          base2.resourceClient.queryModels(query, { appId: app.id }),
      };
    };

    return app;
  };

  // Create component with resource access
  const createComponentWithResources = function (options) {
    // Create the base component
    const component = base3.createComponent(options);

    // Attach resource utilities if component has appropriate permissions
    if (options.permissions && options.permissions.includes("resources")) {
      component.bindResource = function (resourceId) {
        // Retrieve the resource
        const resource = base2.resourceClient.getResource(resourceId);
        if (!resource) {
          throw new Prime.InvalidOperationError(
            `Resource ${resourceId} not found`,
          );
        }

        // Bind resource to component
        component._boundResources = component._boundResources || new Map();
        component._boundResources.set(resourceId, resource);

        return true;
      };

      component.getResource = function (resourceId) {
        if (
          !component._boundResources ||
          !component._boundResources.has(resourceId)
        ) {
          throw new Prime.InvalidOperationError(
            `Resource ${resourceId} not bound to component`,
          );
        }

        return component._boundResources.get(resourceId);
      };
    }

    return component;
  };

  // Return enhanced Base3 with Base2 integration
  return {
    ...base3,

    // Override with enhanced versions
    createApplication: createApplicationWithResources,
    createComponent: createComponentWithResources,

    // Add direct system access methods
    connectToSystem: function (application) {
      // Security check
      if (
        !application.permissions ||
        !application.permissions.includes("system")
      ) {
        throw new Prime.SecurityError(
          "Application does not have system access permission",
          {
            context: {
              appId: application.id,
              permissions: application.permissions,
            },
          },
        );
      }

      // Connect the application to system manager with restricted access
      application.system = {
        getMemoryStats: () => base2.systemManager.getMemoryStats(),
        getPerfMetrics: () => base2.systemManager.getPerformanceMetrics(),
        getResourceStats: () => base2.resourceClient.getResourceStats(),
      };

      return true;
    },

    // Base2 integration helper methods
    registerWithKernel: function (component) {
      return base2.registerComponent(component);
    },

    createBundle: function (bundleConfig) {
      // Validation
      if (
        !bundleConfig ||
        !bundleConfig.id ||
        !bundleConfig.name ||
        !bundleConfig.version
      ) {
        throw new Prime.ValidationError("Invalid bundle configuration", {
          context: { bundleConfig, required: ["id", "name", "version"] },
        });
      }

      // Register bundle with application manager
      return base2.applicationManager.loadBundle(bundleConfig);
    },
  };
}

module.exports = connectToBase2;
