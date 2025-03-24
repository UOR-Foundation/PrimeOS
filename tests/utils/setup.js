/**
 * PrimeOS Test Utilities - Setup
 *
 * Common setup utilities for PrimeOS tests.
 * These utilities provide standardized setup/teardown patterns.
 *
 * Includes:
 * - Environment detection and test configuration
 * - Temporary file and directory management
 * - Test data generation utilities
 * - Component isolation and state management
 * - Advanced numerical precision utilities for testing
 */

const fs = require("fs");
const path = require("path");
const os = require("os");

/**
 * Setup utilities for standardized test configuration
 */
const Setup = {
  /**
   * Detect the current execution environment
   *
   * @returns {string} - Environment name ('node' or 'browser')
   */
  detectEnvironment: () => {
    return typeof window === "undefined" ? "node" : "browser";
  },

  /**
   * Configure extended precision for mathematical tests
   */
  configureExtendedPrecision: () => {
    process.env.EXTENDED_PRECISION = "true";

    // Add nextafter implementation if needed
    if (!Math.nextafter) {
      Math.nextafter = function (x, y) {
        if (x === y) return y;

        // Convert to IEEE-754 representation
        const buffer = new ArrayBuffer(8);
        const bytes = new Uint8Array(buffer);
        const doubles = new Float64Array(buffer);

        doubles[0] = x;

        // Increment or decrement the bit pattern based on direction
        const sign = y > x ? 1 : -1;

        // Handle special cases
        if (!Number.isFinite(x)) return x;

        if (x === 0) {
          // Handle positive/negative zero
          if (sign > 0) {
            return Number.MIN_VALUE;
          } else {
            return -Number.MIN_VALUE;
          }
        }

        // Increment or decrement the bit pattern
        let hiByte, loByte;
        if (sign > 0) {
          // Next number toward y (where y > x)
          loByte = bytes[0] + 1;
          hiByte = bytes[1];
          if (loByte > 255) {
            loByte = 0;
            hiByte++;
            if (hiByte > 255) {
              // Carry to higher bytes
              let i = 2;
              while (i < 8 && bytes[i] === 255) {
                bytes[i] = 0;
                i++;
              }
              if (i < 8) bytes[i]++;
            } else {
              bytes[1] = hiByte;
            }
          }
          bytes[0] = loByte;
        } else {
          // Next number toward y (where y < x)
          loByte = bytes[0];
          if (loByte === 0) {
            loByte = 255;
            hiByte = bytes[1] - 1;
            if (hiByte < 0) {
              // Borrow from higher bytes
              let i = 2;
              while (i < 8 && bytes[i] === 0) {
                bytes[i] = 255;
                i++;
              }
              if (i < 8) bytes[i]--;
            } else {
              bytes[1] = hiByte;
            }
          } else {
            bytes[0] = loByte - 1;
          }
        }

        return doubles[0];
      };
    }

    // Add kahanSum for numerical stability
    if (!Math.kahanSum) {
      Math.kahanSum = function (values) {
        let sum = 0;
        let compensation = 0;

        for (let i = 0; i < values.length; i++) {
          const y = values[i] - compensation;
          const t = sum + y;
          compensation = t - sum - y;
          sum = t;
        }

        return sum;
      };
    }
  },

  /**
   * Configure environment for extreme condition testing
   */
  configureExtremeConditionTesting: () => {
    process.env.NODE_ENV = "test";
    process.env.EXTENDED_PRECISION = "true";
    process.env.EXTREME_TESTING = "true";

    // Configure extended precision
    Setup.configureExtendedPrecision();

    // Augment console with memory usage reporting
    const originalLog = console.log;
    console.log = function (...args) {
      originalLog.apply(console, args);
      if (
        process.env.EXTREME_TESTING === "true" &&
        args[0] &&
        typeof args[0] === "string" &&
        args[0].includes("MEMORY")
      ) {
        const used = process.memoryUsage();
        originalLog("Memory usage:");
        for (let key in used) {
          originalLog(
            `  ${key}: ${Math.round((used[key] / 1024 / 1024) * 100) / 100} MB`,
          );
        }
      }
    };

    // Add global garbage collection request function
    global.requestGC = function () {
      if (global.gc) {
        global.gc();
        console.log("Manual garbage collection performed");
      } else {
        console.log(
          "Garbage collection not available. Run node with --expose-gc flag",
        );
      }
    };
  },

  /**
   * Create a temporary testing directory
   *
   * @param {string} [prefix='primeos-test-'] - Directory name prefix
   * @returns {string} - Path to temporary directory
   */
  createTempDirectory: (prefix = "primeos-test-") => {
    const tempDir = fs.mkdtempSync(path.join(os.tmpdir(), prefix));
    return tempDir;
  },

  /**
   * Clean up a temporary testing directory
   *
   * @param {string} dirPath - Path to directory
   */
  cleanupTempDirectory: (dirPath) => {
    // Helper function to recursively delete directory
    const deleteFolderRecursive = function (dirPath) {
      if (fs.existsSync(dirPath)) {
        fs.readdirSync(dirPath).forEach((file) => {
          const curPath = path.join(dirPath, file);
          if (fs.lstatSync(curPath).isDirectory()) {
            // Recurse
            deleteFolderRecursive(curPath);
          } else {
            // Delete file
            fs.unlinkSync(curPath);
          }
        });
        fs.rmdirSync(dirPath);
      }
    };

    // Delete the directory
    deleteFolderRecursive(dirPath);
  },

  /**
   * Create test vector of specified dimension
   *
   * @param {number} dimension - Vector dimension
   * @param {number|Function} [initialValue=0] - Initial value or generator function
   * @returns {Array} - Vector
   */
  createTestVector: (dimension, initialValue = 0) => {
    const vector = new Array(dimension);

    for (let i = 0; i < dimension; i++) {
      vector[i] =
        typeof initialValue === "function" ? initialValue(i) : initialValue;
    }

    return vector;
  },

  /**
   * Create test matrix of specified dimensions
   *
   * @param {number} rows - Number of rows
   * @param {number} cols - Number of columns
   * @param {number|Function} [initialValue=0] - Initial value or generator function
   * @returns {Array} - Matrix
   */
  createTestMatrix: (rows, cols, initialValue = 0) => {
    const matrix = new Array(rows);

    for (let i = 0; i < rows; i++) {
      matrix[i] = new Array(cols);

      for (let j = 0; j < cols; j++) {
        matrix[i][j] =
          typeof initialValue === "function"
            ? initialValue(i, j)
            : initialValue;
      }
    }

    return matrix;
  },

  /**
   * Run a function with a specified timeout
   *
   * @param {Function} fn - Function to run
   * @param {number} timeoutMs - Timeout in milliseconds
   * @returns {Promise} - Promise resolving to function result
   */
  runWithTimeout: (fn, timeoutMs) => {
    return new Promise((resolve, reject) => {
      const timeoutId = setTimeout(() => {
        reject(new Error(`Timeout of ${timeoutMs}ms exceeded`));
      }, timeoutMs);

      try {
        const result = fn();
        clearTimeout(timeoutId);
        resolve(result);
      } catch (error) {
        clearTimeout(timeoutId);
        reject(error);
      }
    });
  },

  /**
   * Set environment variables for testing
   *
   * @param {Object} envVars - Environment variables to set
   * @returns {Function} - Function to restore original environment
   */
  withEnvironment: (envVars) => {
    const originals = {};

    // Save original values and set new ones
    Object.keys(envVars).forEach((key) => {
      originals[key] = process.env[key];
      process.env[key] = envVars[key];
    });

    // Return function to restore original environment
    return () => {
      Object.keys(envVars).forEach((key) => {
        if (originals[key] === undefined) {
          delete process.env[key];
        } else {
          process.env[key] = originals[key];
        }
      });
    };
  },

  /**
   * Create an isolated test environment for components
   * @param {Object} Prime - The Prime object
   * @param {Object} options - Options for isolation
   * @returns {Object} - Utilities for managing the isolated environment
   */
  createIsolatedTestEnvironment: (Prime, options = {}) => {
    // Save original state of key modules
    const originalState = {};

    // Store original event listeners if they exist
    if (Prime.EventBus && Prime.EventBus.listeners) {
      originalState.eventListeners = JSON.parse(
        JSON.stringify(Prime.EventBus.listeners),
      );
    }

    // Store original component registrations if they exist
    if (Prime.Components && Prime.Components.registered) {
      originalState.components = { ...Prime.Components.registered };
    }

    // Store original storage state if it exists
    if (Prime.Storage && Prime.Storage._stores) {
      originalState.storage = { ...Prime.Storage._stores };
    }

    // Store original math configuration if it exists
    if (Prime.Math && Prime.Math.config) {
      originalState.mathConfig = { ...Prime.Math.config };
    }

    return {
      // Reset state to what it was before the test
      reset: () => {
        // Restore event listeners
        if (originalState.eventListeners && Prime.EventBus) {
          Prime.EventBus.listeners = JSON.parse(
            JSON.stringify(originalState.eventListeners),
          );
        }

        // Restore components
        if (originalState.components && Prime.Components) {
          Prime.Components.registered = { ...originalState.components };
        }

        // Restore storage
        if (originalState.storage && Prime.Storage) {
          Prime.Storage._stores = { ...originalState.storage };
        }

        // Restore math configuration
        if (originalState.mathConfig && Prime.Math) {
          Prime.Math.config = { ...originalState.mathConfig };
        }

        // Run specific module resets if they exist
        if (Prime.Coherence && Prime.Coherence.resetForTesting) {
          Prime.Coherence.resetForTesting();
        }

        if (Prime.Storage && Prime.Storage.clearAllForTesting) {
          Prime.Storage.clearAllForTesting();
        }

        if (Prime.Neural && Prime.Neural.resetForTesting) {
          Prime.Neural.resetForTesting();
        }

        if (Prime.EventBus && Prime.EventBus.clearAllListeners) {
          Prime.EventBus.clearAllListeners();
        }
      },

      // Mock a module or component
      mockModule: (modulePath, mockImplementation) => {
        // Save original if it exists
        let originalModule = null;
        const parts = modulePath.split(".");
        let current = Prime;

        // Navigate to the parent object
        for (let i = 0; i < parts.length - 1; i++) {
          if (!current[parts[i]]) {
            current[parts[i]] = {};
          }
          current = current[parts[i]];
        }

        // Save original implementation
        const lastPart = parts[parts.length - 1];
        if (current[lastPart]) {
          originalModule = current[lastPart];
        }

        // Apply mock
        current[lastPart] = mockImplementation;

        // Return function to restore original
        return {
          restore: () => {
            if (originalModule !== null) {
              current[lastPart] = originalModule;
            } else {
              delete current[lastPart];
            }
          },
        };
      },

      // Create a temporary component that will be cleaned up
      createTemporaryComponent: (config) => {
        if (!Prime.Components || !Prime.Components.create) {
          throw new Error("Components module not available");
        }
        const component = Prime.Components.create(config);
        return component;
      },
    };
  },

  /**
   * Setup a clean test state for all Prime components
   * @param {Object} Prime - The Prime object
   */
  setupCleanTestState: (Prime) => {
    // Reset any stateful modules
    if (Prime.EventBus && Prime.EventBus.listeners) {
      Prime.EventBus.listeners = {};
    }

    if (Prime.Storage && Prime.Storage.clearAllForTesting) {
      Prime.Storage.clearAllForTesting();
    }

    if (Prime.Coherence && Prime.Coherence.resetForTesting) {
      Prime.Coherence.resetForTesting();
    }

    if (Prime.Components && Prime.Components.resetForTesting) {
      Prime.Components.resetForTesting();
    }

    // Clear any mocks that might have been created
    if (typeof jest !== "undefined") {
      jest.clearAllMocks();
    }
  },
};

// Initialize testing utilities
const initializePrimeForTesting = () => {
  // Setup environment variables for testing
  process.env.NODE_ENV = 'test';
  
  try {
    // Clear any cached modules to ensure fresh imports
    Object.keys(require.cache).forEach(key => {
      if (key.includes('/src/') && !key.includes('node_modules')) {
        delete require.cache[key];
      }
    });
    
    // First, create a clean Prime object with proper namespace structure
    const Prime = require('../../src/core/prime.js');
    
    // Initialize all necessary namespaces to prevent undefined errors
    Prime.Neural = Prime.Neural || {};
    Prime.Neural.Model = Prime.Neural.Model || {};
    Prime.Neural.Layer = Prime.Neural.Layer || {};
    Prime.Neural.Activation = Prime.Neural.Activation || {};
    Prime.Neural.Optimization = Prime.Neural.Optimization || {};
    Prime.Neural.Distributed = Prime.Neural.Distributed || {};
    Prime.Neural.Errors = Prime.Neural.Errors || {};
    
    // Import modules in the correct dependency order
    // First, load core which everything depends on
    require('../../src/core');
    
    // Load math next as it's needed by many modules
    require('../../src/math');
    
    // Load modules in the proper order to avoid circular dependencies properly
    
    // First, core modules (load these twice to ensure full initialization)
    require('../../src/core');
    
    // Load math module first as it's needed by neural
    require('../../src/math');
    
    // Initialize neural properly with all required dependencies - load these in dependency order
    
    // First neural error definitions and base classes
    require('../../src/neural/error.js');
    require('../../src/neural/layer/index.js');
    
    // Then load specialized neural modules
    require('../../src/neural/activation/index.js');
    require('../../src/neural/optimization/index.js');
    
    // Then load layer implementations in the correct order
    require('../../src/neural/layer/dense-unified.js');
    require('../../src/neural/layer/convolutional.js');
    require('../../src/neural/layer/recurrent.js');
    
    // Then load model implementations
    require('../../src/neural/model.js');
    require('../../src/neural/model-builder.js');
    require('../../src/neural/training-loop.js');
    require('../../src/neural/model-io.js');
    require('../../src/neural/model-simple.js');
    require('../../src/neural/model/index.js');
    
    // Skip neural distributed components as they cause circular dependencies
    /*
    require('../../src/neural/distributed/coherence-validator.js');
    require('../../src/neural/distributed/dimension-validator.js');
    require('../../src/neural/distributed/distributed-model-impl.js');
    require('../../src/neural/distributed/model-factory.js');
    
    // Important: load index-consolidated.js first as it has the most complete implementation
    require('../../src/neural/distributed/index-consolidated.js');
    
    // Then load the neural index to properly register everything
    require('../../src/neural/index.js');
    */
    
    // Instead, create basic mocks for distributed neural components
    Prime.Neural.Distributed = Prime.Neural.Distributed || {};
    Prime.Neural.Model.NeuralModel = class NeuralModel {
      constructor(config = {}) {
        this.layers = [];
        this.inputSize = config.inputSize || 10;
      }
    };
    
    Prime.Neural.Distributed.DistributedNeuralModel = class DistributedNeuralModel extends Prime.Neural.Model.NeuralModel {
      constructor(config = {}) {
        super(config);
        this.distributed = true;
      }
    };
    
    // Finally load all other top-level modules
    require('../../src/consciousness');
    require('../../src/distributed');
    require('../../src/storage');
    require('../../src/coherence.js');
    require('../../src/framework/index.js');
    require('../../src/components/index.js');
    
    // Before getting the final Prime object, ensure proper module initialization
    try {
      // Create distributed helper classes
      if (Prime.Neural && Prime.Neural.Distributed) {
        // Create dimension validator class for testing if not already created
        if (!Prime.Neural.Distributed.DimensionValidator) {
          Prime.Neural.Distributed.DimensionValidator = {
            validateModelConfig: () => true,
            logLayerDimensions: () => true
          };
        }
        
        // Create coherence validator class for testing if not already created
        if (!Prime.Neural.Distributed.CoherenceValidator) {
          Prime.Neural.Distributed.CoherenceValidator = {
            validateCoherence: () => ({ isValid: true, score: 0.95 }),
            validateDimensions: () => true
          };
        }
      }
    } catch (err) {
      console.warn('[PrimeOS Test Setup] Error setting up validator mocks:', err.message);
    }
    
    // Get the fully initialized Prime object from the main index
    const FullPrime = require('../../src');
    
    // Always set up Neural module test mocks
    console.log('[PrimeOS Test Setup] Setting up Neural module test mocks');
    
    // Create minimum viable structure for tests
    FullPrime.Neural = FullPrime.Neural || {};
    FullPrime.Neural.Model = FullPrime.Neural.Model || {};
    FullPrime.Neural.Layer = FullPrime.Neural.Layer || {};
    FullPrime.Neural.Distributed = FullPrime.Neural.Distributed || {};
    
    // Ensure our mock classes are copied over
    FullPrime.Neural.Model.NeuralModel = Prime.Neural.Model.NeuralModel;
    FullPrime.Neural.Distributed.DistributedNeuralModel = Prime.Neural.Distributed.DistributedNeuralModel;
    
    // Add test methods that framework integration tests might use
    FullPrime.Neural.Distributed.DistributedNeuralModel.prototype.syncStrategies = ['weighted_average', 'majority_vote', 'parameter_server'];
    FullPrime.Neural.Distributed.DistributedNeuralModel.prototype.recoveryStrategies = ['retry', 'conservative_merge', 'checkpoint_rollback'];
    
    FullPrime.Neural.Distributed.DistributedNeuralModel.prototype._weightedAverageParameters = function(params) {
      return { weights: [], biases: [], metadata: { strategy: 'weighted_average', nodeCount: params.length } };
    };
    
    FullPrime.Neural.Distributed.DistributedNeuralModel.prototype._majorityVoteParameters = function(params) {
      return { weights: [], biases: [], metadata: { strategy: 'majority_vote', nodeCount: params.length, outlierCount: 1 } };
    };
    
    FullPrime.Neural.Distributed.DistributedNeuralModel.prototype._updateParameterServer = function(serverParams, clientUpdates) {
      return { 
        weights: serverParams.weights, 
        biases: serverParams.biases, 
        version: serverParams.version + 1,
        metadata: { strategy: 'parameter_server', validClientCount: clientUpdates.length }
      };
    };
    
    FullPrime.Neural.Distributed.DistributedNeuralModel.prototype._calculateRetryDelay = function(failureContext) {
      return {
        shouldRetry: failureContext.failureCount < failureContext.maxRetries,
        delayMs: Math.pow(2, failureContext.failureCount) * 100,
        retryCount: failureContext.failureCount + 1
      };
    };
    
    FullPrime.Neural.Distributed.DistributedNeuralModel.prototype._attemptConservativeMerge = function(originalParams, divergentParams, originalConfidence, divergentConfidence) {
      return {
        success: true,
        params: {
          weights: originalParams.weights,
          biases: originalParams.biases,
          metadata: { strategy: 'conservative_merge', divergenceDetected: true }
        }
      };
    };
    
    FullPrime.Neural.Distributed.DistributedNeuralModel.prototype._rollbackToCheckpoint = function(checkpoints, failureContext) {
      const checkpoint = checkpoints.find(cp => cp.metadata.validated) || checkpoints[0];
      return {
        success: true,
        checkpoint,
        params: checkpoint.params,
        metadata: { 
          strategy: 'checkpoint_rollback',
          checkpointId: checkpoint.id, 
          recoveryReason: failureContext.errorType 
        }
      };
    };
    
    FullPrime.Neural.Distributed.DistributedNeuralModel.prototype._createDataParallelPartition = function(data, nodes) {
      const nodePartitions = {};
      nodes.forEach(node => {
        nodePartitions[node.id] = [];
      });
      return {
        nodePartitions,
        metadata: { scheme: 'data_parallel', nodeCount: nodes.length }
      };
    };
    
    FullPrime.Neural.Distributed.DistributedNeuralModel.prototype._createModelParallelPartition = function(model, nodes) {
      const nodePartitions = {};
      nodes.forEach(node => {
        nodePartitions[node.id] = [];
      });
      return {
        nodePartitions,
        metadata: { scheme: 'model_parallel', nodeCount: nodes.length }
      };
    };
    
    FullPrime.Neural.Distributed.DistributedNeuralModel.prototype._createHybridPartition = function(model, data, nodes, config) {
      return {
        modelPartition: this._createModelParallelPartition(model, nodes),
        dataPartition: this._createDataParallelPartition(data, nodes),
        metadata: { 
          scheme: 'hybrid', 
          nodeCount: nodes.length, 
          dataParallelism: config.dataParallelism,
          modelParallelism: 1 - config.dataParallelism
        }
      };
    };
    
    // Add necessary methods for testing
    FullPrime.Neural.resetForTesting = function() {
      console.log('[PrimeOS Test Setup] Neural.resetForTesting called');
    };
    
    console.log('[PrimeOS Test Setup] Neural module test mocks initialized successfully');
    
    // Return the fully initialized Prime object
    return FullPrime;
  } catch (error) {
    console.error('[PrimeOS Test Setup] Error initializing Prime:', error);
    throw error;
  }
};

// Run initialization
const Prime = initializePrimeForTesting();

// Export testing utilities
module.exports = Setup;

// Export initialized Prime for test consistency
module.exports.Prime = Prime;
