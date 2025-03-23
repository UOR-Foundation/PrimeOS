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
 * Create a bridge for cross-environment testing
 * 
 * @returns {Object} Environment bridge object with methods for cross-environment communication
 */
function createEnvironmentBridge() {
  const environment = detectEnvironment();
  
  // In a real testing scenario, this would use environment-specific mechanisms
  // to communicate between Node.js and browser environments
  
  // For Node.js environment
  if (environment === 'node') {
    return {
      /**
       * Run test code in the browser environment
       * 
       * @param {string} testName - Name of the test to run
       * @param {Object} testData - Test data to send to browser
       * @returns {Promise<any>} Results from browser environment
       */
      runInOtherEnvironment: async (testName, testData) => {
        // This would launch or communicate with a browser instance
        // For this simulation, we'll return compatible results
        
        // Framework Base0 test
        if (testName === 'frameworkBase0Test') {
          const Base0 = require('../../src/framework/base0');
          const base0 = new Base0();
          return testData.patterns.map(pattern => base0.processData(pattern));
        }
        
        // Framework Base1 test
        if (testName === 'frameworkBase1Test') {
          const Base1 = require('../../src/framework/base1');
          const base1 = new Base1();
          return testData.patterns.map(data => base1.recognizePattern(data));
        }
        
        // Framework Base2 test
        if (testName === 'frameworkBase2Test') {
          const Base2 = require('../../src/framework/base2');
          const base2 = new Base2();
          return base2.integratePatterns(testData.patterns);
        }
        
        // Framework Base3 test
        if (testName === 'frameworkBase3Test') {
          const Base3 = require('../../src/framework/base3');
          const base3 = new Base3();
          return base3.transformResult(testData.input);
        }
        
        // Framework Math test
        if (testName === 'frameworkMathTest') {
          const FrameworkMath = require('../../src/framework/math');
          return FrameworkMath.calculateCoherence(testData.vectors);
        }
        
        // Framework Pattern Recognition test
        if (testName === 'frameworkPatternTest') {
          const FrameworkMath = require('../../src/framework/math');
          return FrameworkMath.recognizePatterns(testData.pattern);
        }
        
        // Framework Pipeline test
        if (testName === 'frameworkPipelineTest') {
          const Base0 = require('../../src/framework/base0');
          const Base1 = require('../../src/framework/base1');
          const Base2 = require('../../src/framework/base2');
          const Base3 = require('../../src/framework/base3');
          
          const base0 = new Base0();
          const base1 = new Base1();
          const base2 = new Base2();
          const base3 = new Base3();
          
          // Process through all layers
          const base0Results = testData.testData.map(data => base0.processData(data));
          const base1Results = base0Results.map(result => base1.recognizePattern(result));
          const base2Result = base2.integratePatterns(base1Results);
          const base3Result = base3.transformResult(base2Result);
          
          return {
            finalCoherence: base3Result.transformationCoherence,
            transformationType: base3Result.transformationType,
            transformed: base3Result.transformed
          };
        }
        
        return null;
      }
    };
  }
  
  // For browser environment
  if (environment === 'browser') {
    return {
      /**
       * Run test code in the Node.js environment
       * 
       * @param {string} testName - Name of the test to run
       * @param {Object} testData - Test data to send to Node.js
       * @returns {Promise<any>} Results from Node.js environment
       */
      runInOtherEnvironment: async (testName, testData) => {
        // This would communicate with a Node.js process
        // For this simulation, we'll create browser-compatible results
        
        // Similar implementations to above but optimized for browser
        // In a real implementation, this would make XHR/fetch requests to a test server
        
        return null; // Placeholder
      }
    };
  }
  
  // Default no-op implementation
  return null;
}

/**
 * Create an isolated test environment
 * 
 * @param {Object} options - Environment configuration options
 * @returns {Object} Isolated environment context
 */
function createIsolatedTestEnvironment(options = {}) {
  const environment = options.environment || detectEnvironment();
  
  // Create a clean context for testing
  const context = {
    environment,
    globals: {},
    modules: {},
    cleanup: []
  };
  
  // Store original global values
  const originalGlobals = saveGlobalState();
  
  // Setup isolation
  if (environment === 'node') {
    // Node.js-specific isolation
    setupNodeIsolation(context);
  } else if (environment === 'browser') {
    // Browser-specific isolation
    setupBrowserIsolation(context);
  }
  
  // Return environment with cleanup function
  return {
    context,
    restore: () => {
      // Run cleanup functions
      context.cleanup.forEach(cleanup => {
        if (typeof cleanup === 'function') {
          cleanup();
        }
      });
      
      // Restore original global state
      restoreGlobalState(originalGlobals);
    }
  };
}

/**
 * Save the current global state
 * 
 * @returns {Object} Snapshot of global state
 */
function saveGlobalState() {
  const globals = {};
  
  // Detect environment
  const environment = detectEnvironment();
  
  if (environment === 'node') {
    // Save Node.js globals
    Object.keys(global).forEach(key => {
      if (typeof global[key] !== 'function' && key !== 'global') {
        try {
          globals[key] = JSON.parse(JSON.stringify(global[key]));
        } catch (e) {
          // Skip non-serializable objects
        }
      }
    });
  } else if (environment === 'browser') {
    // Save browser globals
    Object.keys(window).forEach(key => {
      if (typeof window[key] !== 'function' && !key.startsWith('webkit')) {
        try {
          globals[key] = JSON.parse(JSON.stringify(window[key]));
        } catch (e) {
          // Skip non-serializable objects
        }
      }
    });
  }
  
  return {
    environment,
    globals
  };
}

/**
 * Restore the global state from a snapshot
 * 
 * @param {Object} snapshot - Global state snapshot
 */
function restoreGlobalState(snapshot) {
  // Detect environment
  const environment = detectEnvironment();
  
  if (environment !== snapshot.environment) {
    throw new Error(`Cannot restore state from ${snapshot.environment} in ${environment} environment`);
  }
  
  if (environment === 'node') {
    // Restore Node.js globals
    Object.keys(snapshot.globals).forEach(key => {
      global[key] = snapshot.globals[key];
    });
  } else if (environment === 'browser') {
    // Restore browser globals
    Object.keys(snapshot.globals).forEach(key => {
      if (key !== 'location' && key !== 'history') {
        window[key] = snapshot.globals[key];
      }
    });
  }
}

/**
 * Setup Node.js-specific isolation
 * 
 * @param {Object} context - Environment context
 */
function setupNodeIsolation(context) {
  // Save original require
  const originalRequire = require;
  
  // Create module cache
  const moduleCache = {};
  
  // Mock require
  global.require = function(modulePath) {
    // Check for cached module
    if (moduleCache[modulePath]) {
      return moduleCache[modulePath];
    }
    
    // Call original require
    return originalRequire(modulePath);
  };
  
  // Add cleanup function
  context.cleanup.push(() => {
    global.require = originalRequire;
  });
}

/**
 * Setup browser-specific isolation
 * 
 * @param {Object} context - Environment context
 */
function setupBrowserIsolation(context) {
  // Save original XMLHttpRequest
  const originalXHR = window.XMLHttpRequest;
  
  // Mock XMLHttpRequest
  window.XMLHttpRequest = function() {
    const xhr = new originalXHR();
    
    // Save XHR instance for cleanup
    context.globals.xhrInstances = context.globals.xhrInstances || [];
    context.globals.xhrInstances.push(xhr);
    
    return xhr;
  };
  
  // Add cleanup function
  context.cleanup.push(() => {
    window.XMLHttpRequest = originalXHR;
    
    // Abort any pending requests
    if (context.globals.xhrInstances) {
      context.globals.xhrInstances.forEach(xhr => {
        try {
          xhr.abort();
        } catch (e) {
          // Ignore errors
        }
      });
    }
  });
}

/**
 * Setup a clean test state
 * 
 * @returns {Function} Function to restore original state
 */
function setupCleanTestState() {
  // Create isolated environment
  const isolatedEnv = createIsolatedTestEnvironment();
  
  // Return cleanup function
  return () => isolatedEnv.restore();
}

/**
 * Environment handling utilities for cross-platform testing
 */
const Environments = {
  /**
   * Check if code is running in a browser environment
   * 
   * @returns {boolean} - True if running in browser
   */
  isBrowser: () => {
    return typeof window !== 'undefined' && typeof document !== 'undefined';
  },
  
  /**
   * Check if code is running in a Node.js environment
   * 
   * @returns {boolean} - True if running in Node.js
   */
  isNode: () => {
    return typeof process !== 'undefined' && 
      process.versions && 
      process.versions.node;
  },
  
  /**
   * Check if code is running in a Jest test environment
   * 
   * @returns {boolean} - True if running in Jest
   */
  isJest: () => {
    return typeof jest !== 'undefined';
  },
  
  /**
   * Run tests only in a specific environment
   * 
   * @param {string} env - Target environment ('node', 'browser', or 'any')
   * @param {Function} testFn - Test function to run
   * @returns {Function} - Function that conditionally runs the test
   */
  runIn: (env, testFn) => {
    return (...args) => {
      if (env === 'any') {
        return testFn(...args);
      }
      
      if (env === 'node' && Environments.isNode()) {
        return testFn(...args);
      }
      
      if (env === 'browser' && Environments.isBrowser()) {
        return testFn(...args);
      }
      
      // If environment doesn't match, return a dummy function
      return function() {
        if (typeof it === 'function' && typeof it.skip === 'function') {
          it.skip(`Test skipped - requires ${env} environment`);
        } else {
          console.log(`Test skipped - requires ${env} environment`);
        }
      };
    };
  },
  
  /**
   * Skip tests in specific environments
   * 
   * @param {string} env - Environment to skip ('node', 'browser')
   * @param {Function} testFn - Test function
   * @returns {Function} - Function that conditionally runs the test
   */
  skipIn: (env, testFn) => {
    return (...args) => {
      if (env === 'node' && Environments.isNode()) {
        if (typeof it === 'function' && typeof it.skip === 'function') {
          it.skip(`Test skipped in node environment`);
        } else {
          console.log(`Test skipped in node environment`);
        }
        return;
      }
      
      if (env === 'browser' && Environments.isBrowser()) {
        if (typeof it === 'function' && typeof it.skip === 'function') {
          it.skip(`Test skipped in browser environment`);
        } else {
          console.log(`Test skipped in browser environment`);
        }
        return;
      }
      
      // Run the test if not in the skipped environment
      return testFn(...args);
    };
  },
  
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
  }
};

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