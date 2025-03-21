/**
 * PrimeOS JavaScript Library - Framework
 * Base 2: Kernel
 * Orchestrator of the system
 */

// Import core
const Prime = require("../../core.js");
const MathUtils = require("../math");

// Import component modules
const ResourceClient = require("./resource-client");
const ApplicationManager = require("./application-manager");
const SystemManager = require("./system-manager");

/**
 * Base 2: Kernel
 * Orchestrator of the system
 */
const Base2 = {
  // Syscall registry
  syscalls: {},

  /**
   * Register syscalls
   * @param {Array} syscalls - Syscalls to register
   */
  registerSyscalls: function (syscalls) {
    for (const syscall of syscalls) {
      if (!syscall.name || typeof syscall.handler !== "function") {
        throw new Prime.ValidationError(
          "Syscall must have a name and handler function",
        );
      }

      this.syscalls[syscall.name] = syscall.handler;
    }
  },

  /**
   * Execute a syscall with enhanced validation and error handling
   * @param {string} name - Syscall name
   * @param  {...any} args - Syscall arguments
   * @returns {*} Syscall result
   */
  syscall: function (name, ...args) {
    // Check if syscall exists
    if (!this.syscalls[name]) {
      throw new Prime.InvalidOperationError(`Syscall ${name} not found`, {
        context: {
          availableSyscalls: Object.keys(this.syscalls),
        },
      });
    }

    // Enhanced error handling and instrumentation
    try {
      // Track execution time for performance monitoring
      const startTime = performance.now();

      // Execute the syscall
      const result = this.syscalls[name](...args);

      // Track execution time
      const executionTime = performance.now() - startTime;

      // Log slow syscalls for performance tuning
      if (executionTime > 100) {
        Prime.Logger.warn(
          `Slow syscall ${name} detected: ${executionTime.toFixed(2)}ms`,
        );
      }

      return result;
    } catch (error) {
      // Enhanced error handling with context
      Prime.Logger.error(`Error executing syscall ${name}:`, error);

      // If it's already a Prime error, add additional context and re-throw
      if (error instanceof Error && error.name.startsWith("Prime")) {
        error.context = error.context || {};
        error.context.syscall = name;
        error.context.syscallArgs = args;
        throw error;
      }

      // Otherwise, wrap in a Prime error for consistent handling
      throw new Prime.InvalidOperationError(
        `Syscall ${name} execution failed: ${error.message}`,
        {
          context: {
            syscall: name,
            syscallArgs: args,
            originalError: error.message,
            originalStack: error.stack,
          },
          cause: error,
        },
      );
    }
  },

  /**
   * Create a resource client
   * @param {Object} config - Configuration object
   * @returns {Object} Resource client
   */
  createResourceClient: function (config = {}) {
    return ResourceClient.create(config);
  },

  /**
   * Create an application manager
   * @param {Object} config - Configuration object
   * @returns {Object} Application manager
   */
  createApplicationManager: function (config = {}) {
    return ApplicationManager(config);
  },

  /**
   * Create a system manager
   * @param {Object} config - Configuration object
   * @returns {Object} System manager
   */
  createSystemManager: function (config = {}) {
    return SystemManager.create(config);
  },

  /**
   * Connect to Base 1
   * @param {Object} base1Resources - Base 1 resources
   * @returns {Object} Connected Base 2 components
   */
  connectToBase1: function (base1Resources) {
    const resourceClient = this.createResourceClient({
      runtime: base1Resources.runtime,
      observation: base1Resources.observation,
      interaction: base1Resources.interaction,
      representation: base1Resources.representation,
    });

    const applicationManager = this.createApplicationManager({
      resourceClient,
    });

    const systemManager = this.createSystemManager({});

    return {
      resourceClient,
      applicationManager,
      systemManager,
      syscall: this.syscall.bind(this),
    };
  },
};

module.exports = Base2;
