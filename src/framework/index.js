/**
 * PrimeOS JavaScript Library - Framework
 * Prime Framework four-tier architecture
 * Version 1.0.0
 */

// Import Prime using CommonJS to avoid circular dependency
const Prime = require("../core/prime.js");
// Ensure mathematics and coherence modules are loaded
require("../mathematics.js");
require("../coherence.js");

// Import framework components
const Base0 = require("./base0");
const Base1 = require("./base1");
const Base2 = require("./base2");
const Base3 = require("./base3");
const MathUtils = require("./math");

// Base0 is loaded by the require('./base0') above, we don't need a separate import

// Error classes are now properly defined in core/error.js
// and automatically attached to Prime

/**
 * Create a fully integrated Prime Framework instance
 * @param {Object} config - Framework configuration
 * @returns {Object} Prime Framework instance
 */
const createPrimeFramework = function (config = {}) {
  // Create and connect all components

  // Base 0: Neural Network Specification
  const base0 = Base0.createBase0Components(config.base0 || {});

  // Connect Base 0 to coherence
  if (Prime.coherence && Prime.coherence.systemCoherence) {
    Base0.connectToCoherence(base0);
  }

  // Base 1: Resource - Connect to Base 0
  const base1 = Base1.connectToBase0(base0);

  // Base 2: Kernel - Connect to Base 1
  const base2 = Base2.connectToBase1(base1);

  // Base 3: Application - Connect to Base 2
  const base3 = Base3.connectToBase2(base2);

  // Create framework instance
  const framework = {
    // Base components
    base0,
    base1,
    base2,
    base3,

    /**
     * Get global coherence of the framework
     * @returns {number} Global coherence norm
     */
    getCoherence: function () {
      if (Prime.coherence && Prime.coherence.systemCoherence) {
        return Prime.coherence.systemCoherence.calculateGlobalCoherence();
      }
      return 1.0; // Default coherence if system not available
    },

    /**
     * Optimize global coherence
     * @param {Object} options - Optimization options
     * @returns {number} Optimized coherence norm
     */
    optimizeCoherence: function (options = {}) {
      if (Prime.coherence && Prime.coherence.systemCoherence) {
        return Prime.coherence.systemCoherence.optimizeGlobal(options);
      }
      return 1.0; // Default coherence if system not available
    },

    /**
     * Create an application
     * @param {Object} config - Application configuration
     * @returns {Object} Application
     */
    createApplication: function (config) {
      // Give the app a default ID if not provided
      if (!config.id) {
        config.id = `app-${Prime.Utils.uuid().substring(0, 8)}`;
      }

      // Ensure behavior exists
      if (!config.behavior) {
        config.behavior = {};
      }

      // Set default actions
      if (!config.behavior.actions) {
        config.behavior.actions = {};
      }

      // Set default initialState
      if (!config.behavior.initialState) {
        config.behavior.initialState = {};
      }

      // Create the application through Base3
      const app = base3.createApplication(config);

      // Register with coherence system if available
      if (Prime.coherence && Prime.coherence.systemCoherence) {
        Prime.coherence.systemCoherence.register(app);
      }

      return app;
    },

    /**
     * Start an application from a bundle
     * @param {string} bundleId - Bundle identifier
     * @param {Object} options - Application options
     * @returns {Object} Running application
     */
    startApplicationFromBundle: function (bundleId, options = {}) {
      return base2.applicationManager.startApplication(bundleId, options);
    },

    /**
     * Stop an application
     * @param {string} appId - Application identifier
     * @returns {boolean} Success
     */
    stopApplication: function (appId) {
      return base2.applicationManager.stopApplication(appId);
    },

    /**
     * Register a syscall
     * @param {Object} syscall - Syscall to register
     * @returns {boolean} Success
     */
    registerSyscall: function (syscall) {
      Base2.registerSyscalls([syscall]);
      return true;
    },

    /**
     * Execute a syscall
     * @param {string} name - Syscall name
     * @param  {...any} args - Syscall arguments
     * @returns {*} Syscall result
     */
    syscall: function (name, ...args) {
      return Base2.syscall(name, ...args);
    },
  };

  return framework;
};

// Extend Prime with framework capabilities
Prime.Base0 = Base0;
Prime.Base1 = Base1;
Prime.Base2 = Base2;
Prime.Base3 = Base3;
Prime.MathUtils = MathUtils;
Prime.createPrimeFramework = createPrimeFramework;

// CommonJS export (no ES module export to avoid circular dependency)
if (typeof module !== "undefined" && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== "undefined") {
  window.Prime = Prime;
}
