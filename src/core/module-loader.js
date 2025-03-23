/**
 * PrimeOS JavaScript Library - Module Loader
 * Module management system for dynamic module loading and environment detection
 * Version 1.0.0
 */

// Import Prime object from prime.js
const Prime = require("./prime.js");

(function (Prime) {
  /**
   * ModuleLoader implementation
   * Provides facilities for registering and requiring modules
   */
  const ModuleLoader = {
    /**
     * Detects the current JavaScript environment
     * @returns {string} Environment identifier ('node', 'browser', etc.)
     */
    detectEnvironment: function () {
      if (
        typeof process !== "undefined" &&
        process.versions &&
        process.versions.node
      ) {
        return "node";
      } else if (typeof window !== "undefined") {
        return "browser";
      } else if (typeof self !== "undefined" && self.WorkerGlobalScope) {
        return "worker";
      } else {
        return "unknown";
      }
    },

    /**
     * Registers a module on the Prime object
     * @param {string} name - Name of the module
     * @param {Object} module - Module object to register
     * @returns {boolean} True if successful, false if module already exists
     * @throws {ValidationError} If name is not a string or module is not an object
     */
    register: function (name, module) {
      // Get the appropriate error class (handle both namespaces for backwards compatibility)
      const ValidationError =
        Prime.Errors && Prime.Errors.ValidationError
          ? Prime.Errors.ValidationError
          : Prime.ValidationError;

      // Validate parameters
      if (!Prime.Utils.isString(name)) {
        throw new ValidationError("Module name must be a string");
      }

      if (name === "" || name.trim() === "") {
        throw new ValidationError("Module name must not be empty");
      }

      if (module === null) {
        throw new ValidationError("Module must not be null");
      }

      if (!Prime.Utils.isObject(module)) {
        throw new ValidationError("Module must be an object");
      }

      // No special case handling - treat all modules equally

      // Check if module already exists
      if (Prime[name] !== undefined) {
        return false;
      }

      // Register the module
      Prime[name] = module;
      return true;
    },

    /**
     * Requires an already registered module
     * @param {string} name - Name of the module to require
     * @returns {Object} The requested module
     * @throws {ValidationError} If name is not a string
     * @throws {ConfigurationError} If module is not found
     */
    require: function (name) {
      // Get the appropriate error classes (handle both namespaces for backwards compatibility)
      const ValidationError =
        Prime.Errors && Prime.Errors.ValidationError
          ? Prime.Errors.ValidationError
          : Prime.ValidationError;

      const ConfigurationError =
        Prime.Errors && Prime.Errors.ConfigurationError
          ? Prime.Errors.ConfigurationError
          : Prime.ConfigurationError;

      // Validate parameter
      if (!Prime.Utils.isString(name)) {
        throw new ValidationError("Module name must be a string");
      }

      // Check if module exists
      if (Prime[name] === undefined) {
        throw new ConfigurationError(`Module '${name}' is not registered`);
      }

      return Prime[name];
    },

    /**
     * Unregisters a module from the Prime object
     * @param {string} name - Name of the module to unregister
     * @returns {boolean} True if successful, false if module doesn't exist
     * @throws {ValidationError} If name is not a string
     */
    unregister: function (name) {
      // Get the appropriate error class (handle both namespaces for backwards compatibility)
      const ValidationError =
        Prime.Errors && Prime.Errors.ValidationError
          ? Prime.Errors.ValidationError
          : Prime.ValidationError;

      // Validate parameter
      if (!Prime.Utils.isString(name)) {
        throw new ValidationError("Module name must be a string");
      }

      // Check if module exists
      if (Prime[name] === undefined) {
        return false;
      }

      // Unregister the module
      delete Prime[name];
      return true;
    },

    /**
     * Gets a list of all registered module names
     * @returns {Array<string>} Array of module names
     */
    getModules: function () {
      // Get all keys from Prime that are objects (excluding functions and primitives)
      return Object.keys(Prime).filter(
        (key) =>
          Prime.Utils.isObject(Prime[key]) &&
          // Exclude core utilities and internal properties
          !["Utils", "Errors", "EventBus"].includes(key),
      );
    },
  };

  // Attach ModuleLoader to Prime
  Prime.ModuleLoader = ModuleLoader;
})(Prime);

// CommonJS export
if (typeof module !== "undefined" && module.exports) {
  module.exports = Prime;
}
