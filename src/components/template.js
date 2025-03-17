/**
 * PrimeOS JavaScript Library - Component Template
 * Templates for creating reusable components
 * Version 1.0.0
 */

// Import Prime using CommonJS to avoid circular dependency
const Prime = require('../core.js');
// Ensure all modules are loaded in correct order
require('../mathematics.js');
require('../coherence.js');
require('../framework/index.js');
require('./base.js');
require('./factory.js');

(function(Prime) {

  /**
   * Component Template for creating reusable component templates
   */
  class ComponentTemplate {
    /**
     * Create a new component template
     * @param {Object} template - Template configuration
     */
    constructor(template) {
      this.template = Prime.Utils.deepClone(template);
      this.validators = [];

      // Add name validation by default
      this.addValidator(config => {
        if (!config.meta || !config.meta.name) {
          throw new Prime.ValidationError('Component must have a meta.name property');
        }
        return true;
      });
    }

    /**
     * Add a validator function
     * @param {Function} validator - Validator function
     * @returns {ComponentTemplate} This template for chaining
     */
    addValidator(validator) {
      if (!Prime.Utils.isFunction(validator)) {
        throw new Prime.ValidationError('Validator must be a function');
      }

      this.validators.push(validator);
      return this;
    }

    /**
     * Create a component from this template
     * @param {Object} config - Component configuration
     * @returns {Object} New component
     */
    create(config) {
      // Merge template with provided config
      const mergedConfig = this._mergeConfigs(this.template, config);

      // Run all validators
      for (const validator of this.validators) {
        validator(mergedConfig);
      }

      // Create the component
      return Prime.createComponent(mergedConfig);
    }

    /**
     * Create multiple components from this template
     * @param {Array} configs - Array of component configurations
     * @returns {Array} New components
     */
    createBatch(configs) {
      return configs.map(config => this.create(config));
    }

    /**
     * Extend this template with additional properties
     * @param {Object} extension - Template extension
     * @returns {ComponentTemplate} New template
     */
    extend(extension) {
      const extendedTemplate = new ComponentTemplate(this._mergeConfigs(this.template, extension));

      // Copy validators
      for (const validator of this.validators) {
        extendedTemplate.addValidator(validator);
      }

      return extendedTemplate;
    }

    /**
     * Register this template as a component type
     * @param {string} typeName - Type name to register
     * @returns {ComponentTemplate} This template for chaining
     */
    registerType(typeName) {
      if (!Prime.Utils.isString(typeName)) {
        throw new Prime.ValidationError('Type name must be a string');
      }

      // Register with component factory
      Prime.ComponentFactory.register(typeName, config => this.create(config));

      return this;
    }

    /**
     * Helper to deeply merge configurations
     * @private
     * @param {Object} base - Base configuration
     * @param {Object} override - Configuration override
     * @returns {Object} Merged configuration
     */
    _mergeConfigs(base, override) {
      const result = Prime.Utils.deepClone(base);

      // Special handling for different sections
      for (const section of ['meta', 'invariant', 'variant']) {
        if (override[section]) {
          result[section] = result[section] || {};
          result[section] = { ...result[section], ...override[section] };
        }
      }

      // Handle other properties
      for (const key in override) {
        if (!['meta', 'invariant', 'variant'].includes(key)) {
          result[key] = override[key];
        }
      }

      return result;
    }
  }

  // Export ComponentTemplate to Prime
  Prime.ComponentTemplate = ComponentTemplate;

  // Publish component module loaded event
  Prime.EventBus.publish('module:loaded', { name: 'component-template' });

})(Prime);

// CommonJS export (no ES module export to avoid circular dependency)
if (typeof module !== 'undefined' && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== 'undefined') {
  window.Prime = Prime;
}