/**
 * PrimeOS Test Utilities - Environments
 * 
 * Utilities for handling different test environments (Node.js vs Browser).
 * Provides standardized environment detection and configuration.
 */

/**
 * Detect the current JavaScript execution environment
 * 
 * @returns {string} Environment identifier ('node', 'browser', 'worker', etc.)
 */
function detectEnvironment() {
  // Check for Node.js environment
  if (typeof process !== 'undefined' && process.versions && process.versions.node) {
    return 'node';
  }
  
  // Check for browser environment
  if (typeof window !== 'undefined' && typeof document !== 'undefined') {
    return 'browser';
  }
  
  // Check for web worker
  if (typeof self !== 'undefined' && typeof WorkerGlobalScope !== 'undefined' && 
      self instanceof WorkerGlobalScope) {
    return 'worker';
  }
  
  // Check for service worker
  if (typeof self !== 'undefined' && typeof ServiceWorkerGlobalScope !== 'undefined' && 
      self instanceof ServiceWorkerGlobalScope) {
    return 'serviceWorker';
  }
  
  // Unknown environment
  return 'unknown';
}

/**
 * Create an isolated test environment
 * @param {Object} options - Configuration options
 * @returns {Object} Isolated environment object
 */
function createIsolatedTestEnvironment(options = {}) {
  // Implementation depends on the environment
  if (detectEnvironment() === 'node') {
    // For Node.js, we can use vm module to create isolated contexts
    const vm = require('vm');
    const sandbox = { ...options.globals };
    return vm.createContext(sandbox);
  } else if (detectEnvironment() === 'browser') {
    // For browsers, we can use iframes
    const iframe = document.createElement('iframe');
    iframe.style.display = 'none';
    document.body.appendChild(iframe);
    
    // Clean up function
    const cleanup = () => {
      document.body.removeChild(iframe);
    };
    
    // Return environment with cleanup
    return {
      window: iframe.contentWindow,
      document: iframe.contentDocument,
      cleanup
    };
  }
  
  // Fallback for unsupported environments
  return { unsupported: true };
}

/**
 * Create a test environment bridge for cross-environment testing
 * @returns {Object} Environment bridge
 */
function createEnvironmentBridge() {
  // Implementation depends on the environment
  if (detectEnvironment() === 'node') {
    // For Node.js
    return {
      getGlobal: (name) => global[name],
      setGlobal: (name, value) => { global[name] = value; },
      environment: 'node'
    };
  } else if (detectEnvironment() === 'browser') {
    // For browsers
    return {
      getGlobal: (name) => window[name],
      setGlobal: (name, value) => { window[name] = value; },
      environment: 'browser'
    };
  }
  
  // Fallback
  return { environment: detectEnvironment() };
}

/**
 * Setup a clean test state
 * @returns {Function} Function to restore original state
 */
function setupCleanTestState() {
  const env = detectEnvironment();
  let restore;
  
  if (env === 'node') {
    // For Node.js, capture module cache state
    const originalModuleCache = { ...require.cache };
    restore = () => {
      // Restore original module cache
      Object.keys(require.cache).forEach(key => {
        if (!originalModuleCache[key]) {
          delete require.cache[key];
        }
      });
    };
  } else if (env === 'browser') {
    // For browsers, capture global properties
    const originalProps = {};
    const testProps = ['__TEST_GLOBALS', '__TEST_STATE']; // Example test globals to track
    
    testProps.forEach(prop => {
      originalProps[prop] = window[prop];
    });
    
    restore = () => {
      // Restore original properties
      testProps.forEach(prop => {
        if (originalProps[prop] === undefined) {
          delete window[prop];
        } else {
          window[prop] = originalProps[prop];
        }
      });
    };
  } else {
    // Fallback
    restore = () => {};
  }
  
  return restore;
}

// Export the Environments module
const Environments = {
  /**
   * Check if running in Node.js
   * @returns {boolean} True if running in Node.js
   */
  isNode: () => detectEnvironment() === 'node',
  
  /**
   * Check if running in browser
   * @returns {boolean} True if running in browser
   */
  isBrowser: () => detectEnvironment() === 'browser',
  
  /**
   * Check if running in worker
   * @returns {boolean} True if running in worker
   */
  isWorker: () => ['worker', 'serviceWorker'].includes(detectEnvironment()),
  
  /**
   * Configure environment-specific test setup
   * 
   * @param {Object} options - Setup options
   * @param {Function} [options.node] - Node.js setup function
   * @param {Function} [options.browser] - Browser setup function
   * @param {Function} [options.common] - Common setup function
   */
  configure: (options = {}) => {
    const { node, browser, common } = options;
    
    // Run common setup if provided
    if (typeof common === 'function') {
      common();
    }
    
    // Run environment-specific setup
    if (Environments.isNode() && typeof node === 'function') {
      node();
    } else if (Environments.isBrowser() && typeof browser === 'function') {
      browser();
    }
  },
  
  /**
   * Create environment-specific test data
   * 
   * @param {Object} data - Environment-specific data
   * @param {*} data.node - Node.js-specific data
   * @param {*} data.browser - Browser-specific data
   * @param {*} [data.common] - Common data
   * @returns {*} - Data for current environment
   */
  getData: (data) => {
    // Start with common data if provided
    const result = data.common ? { ...data.common } : {};
    
    // Add environment-specific data
    if (Environments.isNode() && data.node) {
      return typeof data.node === 'object' && data.node !== null
        ? { ...result, ...data.node }
        : data.node;
    } else if (Environments.isBrowser() && data.browser) {
      return typeof data.browser === 'object' && data.browser !== null
        ? { ...result, ...data.browser }
        : data.browser;
    }
    
    return result;
  },
  
  /**
   * Get the current environment name
   * 
   * @returns {string} - Environment name
   */
  getEnvironment: () => {
    return detectEnvironment();
  },
  
  /**
   * Create an environment bridge for cross-environment testing
   * 
   * @returns {Object} - Environment bridge
   */
  createBridge: createEnvironmentBridge,
  
  /**
   * Create an isolated test environment
   * 
   * @param {Object} options - Options
   * @returns {Object} - Isolated environment
   */
  createIsolatedEnvironment: createIsolatedTestEnvironment,
  
  /**
   * Setup a clean test state
   * 
   * @returns {Function} - Function to restore original state
   */
  setupCleanState: setupCleanTestState
};

module.exports = Environments;