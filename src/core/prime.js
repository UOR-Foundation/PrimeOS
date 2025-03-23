/**
 * PrimeOS JavaScript Library - Core Prime Object
 * Foundation for all Prime functionality
 * Version 1.0.0
 */

// Use module pattern for encapsulation
const Prime = (function () {
  /**
   * Library version with semantic validation support
   */
  const VERSION = '1.0.0';

  /**
   * Public API
   */
  return {
    /**
     * Public version identifiers
     */
    VERSION,
    version: VERSION,

    /**
     * Utility container - populated by utils.js
     */
    Utils: {},

    /**
     * Error class container - populated by error.js
     */
    Errors: {},

    /**
     * Event bus container - populated by event-bus.js
     */
    EventBus: null,

    /**
     * Logger container - populated by logger.js
     */
    Logger: null,

    /**
     * Placeholder for other modules to be attached
     */
    Clifford: null,
    Lie: null,
    coherence: null,
    UOR: null,
    Base0: null,
    Base1: null,
    Base2: null,
    Base3: null,
    ComponentRegistry: null,
    ComponentFactory: null,
    ComponentTemplate: null,
    Components: {},
  };
})();

// CommonJS export (no ES module export to avoid circular dependency)
if (typeof module !== 'undefined' && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== 'undefined') {
  window.Prime = Prime;
}
