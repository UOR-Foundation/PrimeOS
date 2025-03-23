/**
 * Base3 - Application Layer
 *
 * This module provides the core functionality for user-space applications,
 * including application lifecycle management, state management, UI components,
 * and interaction handlers.
 */

const Prime = require('../../core');
const { Utils } = Prime;

// Import internal modules
const createApplication = require('./application');
const createComponent = require('./component');
const createFramework = require('./framework');
const connectToBase2 = require('./connect');

/**
 * Initializes the Base3 application layer
 * @param {Object} config - Configuration settings
 * @returns {Object} Base3 API
 */
function initialize(config = {}) {
  return {
    /**
     * Create a new application
     * @param {Object} options - Application options
     * @returns {Object} Application instance
     */
    createApplication: function (options) {
      return createApplication(options);
    },

    /**
     * Create a new component
     * @param {Object} options - Component options
     * @returns {Object} Component instance
     */
    createComponent: function (options) {
      return createComponent(options);
    },

    /**
     * Create framework utilities
     * @param {Object} options - Framework options
     * @returns {Object} Framework utilities
     */
    createFramework: function (options) {
      return createFramework(options);
    },
  };
}

// Export initialization and connection module
module.exports = initialize;
module.exports.connectToBase2 = connectToBase2;
module.exports.createApplication = createApplication;
