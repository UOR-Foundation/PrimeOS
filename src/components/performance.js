/**
 * PrimeOS JavaScript Library - Component Performance
 * Performance optimization and benchmarking for components
 * Version 1.0.0
 */

// Import Prime using CommonJS to avoid circular dependency
const Prime = require('../core.js');
// Ensure all modules are loaded in correct order
require('../mathematics.js');
require('../coherence.js');
require('../framework/index.js');
require('./base.js');

(function (Prime) {
  /**
   * Performance optimization and benchmarking
   */
  const performance = {
    /**
     * Current configuration
     */
    config: {
      useWebAssembly: false,
      useWorkers: false,
      memoizationLimit: 1000,
      precision: 'double',
      optimizationLevel: 'balanced',
      preferredRenderer: 'auto',
      logPerformance: false,
    },

    /**
     * Cache for performance measurements
     */
    _cache: new Map(),

    /**
     * Performance history
     */
    _history: [],

    /**
     * Configure performance options
     * @param {Object} options - Performance options
     * @returns {Object} Updated configuration
     */
    configure: function (options) {
      if (!options) {
        return this.config;
      }

      this.config = { ...this.config, ...options };

      // Apply configuration changes
      if (options.memoizationLimit !== undefined) {
        this._pruneCache();
      }

      return this.config;
    },

    /**
     * Run a benchmark
     * @param {Function} operation - Operation to benchmark
     * @param {Object} options - Benchmark options
     * @returns {Object} Benchmark results
     */
    benchmark: async function (operation, options = {}) {
      if (!Prime.Utils.isFunction(operation)) {
        throw new Prime.ValidationError('Operation must be a function');
      }

      const iterations = options.iterations || 100;
      const warmup = options.warmup || 10;
      const name = options.name || operation.name || 'anonymous';
      const args = options.args || [];

      // Track all timings
      const timings = [];

      // Run warmup iterations
      for (let i = 0; i < warmup; i++) {
        try {
          await operation(...args);
        } catch (error) {
          Prime.Logger.warn(`Error during warmup iteration ${i}`, {
            error: error.message,
            stack: error.stack,
          });
        }
      }

      // Run benchmark iterations
      for (let i = 0; i < iterations; i++) {
        try {
          const start = performance.now ? performance.now() : Date.now();
          await operation(...args);
          const end = performance.now ? performance.now() : Date.now();

          timings.push(end - start);
        } catch (error) {
          Prime.Logger.warn(`Error during benchmark iteration ${i}`, {
            error: error.message,
            stack: error.stack,
          });

          // Add a high timing value to indicate error
          timings.push(Number.MAX_SAFE_INTEGER);
        }
      }

      // Calculate statistics
      const validTimings = timings.filter((t) => t !== Number.MAX_SAFE_INTEGER);
      const sum = validTimings.reduce((a, b) => a + b, 0);
      const mean = sum / validTimings.length;

      const squaredDifferences = validTimings.map((t) => Math.pow(t - mean, 2));
      const variance =
        squaredDifferences.reduce((a, b) => a + b, 0) / validTimings.length;
      const stdDev = Math.sqrt(variance);

      // Calculate percentiles
      const sortedTimings = [...validTimings].sort((a, b) => a - b);
      const median = this._calculatePercentile(sortedTimings, 50);
      const p95 = this._calculatePercentile(sortedTimings, 95);
      const p99 = this._calculatePercentile(sortedTimings, 99);

      // Create result object
      const result = {
        name,
        iterations: validTimings.length,
        failedIterations: timings.length - validTimings.length,
        mean,
        median,
        stdDev,
        min: Math.min(...validTimings),
        max: Math.max(...validTimings),
        p95,
        p99,
        total: sum,
        // Always include samples array, but limit its size if not explicitly requested
        samples: options.keepTimings ? validTimings : validTimings.slice(0, 10),
        timestamp: Date.now(),
      };

      // Save to history
      this._history.push({
        name,
        mean,
        median,
        stdDev,
        timestamp: Date.now(),
      });

      // Prune history if needed
      if (this._history.length > 1000) {
        this._history = this._history.slice(-1000);
      }

      // Log results if configured
      if (this.config.logPerformance) {
        Prime.Logger.info(`Benchmark results for ${name}`, result);
      }

      return result;
    },

    /**
     * Run comparative benchmark of multiple operations
     * @param {Array} operations - Operations to benchmark
     * @param {Object} options - Benchmark options
     * @returns {Object} Comparison results
     */
    compare: async function (operations, options = {}) {
      if (!Prime.Utils.isArray(operations)) {
        throw new Prime.ValidationError('Operations must be an array');
      }

      // Add names if not provided
      const namedOperations = operations.map((op, index) => {
        if (Prime.Utils.isFunction(op)) {
          return {
            name: op.name || `Operation ${index + 1}`,
            fn: op,
          };
        }
        return op;
      });

      // Run benchmarks for each operation
      const results = [];

      for (const op of namedOperations) {
        const result = await this.benchmark(op.fn, {
          ...options,
          name: op.name,
          args: op.args,
        });

        results.push(result);
      }

      // Calculate relative performance
      const sorted = [...results].sort((a, b) => a.mean - b.mean);
      const fastest = sorted[0];

      // Add relative speed
      const withRelative = results.map((result) => ({
        ...result,
        relative: result.mean / fastest.mean,
      }));

      return {
        results: withRelative,
        fastest: fastest.name,
        slowest: sorted[sorted.length - 1].name,
        timestamp: Date.now(),
      };
    },

    /**
     * Create a function optimized for performance
     * @param {Function} fn - Function to optimize
     * @param {Object} options - Optimization options
     * @returns {Function} Optimized function
     */
    optimize: function (fn, options = {}) {
      if (!Prime.Utils.isFunction(fn)) {
        throw new Prime.ValidationError('Function is required');
      }

      const mergedOptions = {
        memoize: options.memoize !== false,
        memoizeLimit: options.memoizeLimit || this.config.memoizationLimit,
        async:
          options.async !== false && fn.constructor.name === 'AsyncFunction',
        monitor: options.monitor !== false,
        validateInput: options.validateInput,
        validateOutput: options.validateOutput,
      };

      // Start with the original function
      let optimized = fn;

      // Add input validation if provided
      if (mergedOptions.validateInput) {
        const originalFn = optimized;
        optimized = function (...args) {
          if (!mergedOptions.validateInput(...args)) {
            throw new Prime.ValidationError('Input validation failed');
          }
          return originalFn.apply(this, args);
        };
      }

      // Add output validation if provided
      if (mergedOptions.validateOutput) {
        const originalFn = optimized;
        optimized = function (...args) {
          const result = originalFn.apply(this, args);

          if (!mergedOptions.validateOutput(result, ...args)) {
            throw new Prime.ValidationError('Output validation failed');
          }

          return result;
        };
      }

      // Add memoization if requested
      if (mergedOptions.memoize) {
        optimized = Prime.Utils.memoize(optimized, {
          maxSize: mergedOptions.memoizeLimit,
        });
      }

      // Add performance monitoring if requested
      if (mergedOptions.monitor) {
        const name = fn.name || 'anonymous';
        const monitoredFn = optimized;

        if (mergedOptions.async) {
          optimized = async function (...args) {
            const start = performance.now ? performance.now() : Date.now();

            try {
              const result = await monitoredFn.apply(this, args);

              const end = performance.now ? performance.now() : Date.now();
              performance._recordExecution(name, end - start);

              return result;
            } catch (error) {
              const end = performance.now ? performance.now() : Date.now();
              performance._recordExecution(name, end - start, error);

              throw error;
            }
          };
        } else {
          optimized = function (...args) {
            const start = performance.now ? performance.now() : Date.now();

            try {
              const result = monitoredFn.apply(this, args);

              const end = performance.now ? performance.now() : Date.now();
              performance._recordExecution(name, end - start);

              return result;
            } catch (error) {
              const end = performance.now ? performance.now() : Date.now();
              performance._recordExecution(name, end - start, error);

              throw error;
            }
          };
        }
      }

      return optimized;
    },

    /**
     * Create an async function optimized for performance
     * @param {Function} fn - Async function to optimize
     * @param {Object} options - Optimization options
     * @returns {Function} Optimized async function
     */
    optimizeAsync: function (fn, options = {}) {
      if (!Prime.Utils.isFunction(fn)) {
        throw new Prime.ValidationError('Function is required');
      }

      const mergedOptions = {
        ...options,
        async: true,
        memoize: options.memoize !== false,
        cacheTime: options.cacheTime || 5000, // Default cache time: 5 seconds
        validateInput: options.validateInput,
        validateOutput: options.validateOutput,
      };

      // Create cache for async results
      const cache = new Map();
      const cacheTimers = new Map();

      // Core optimized function
      const optimized = async function (...args) {
        // Input validation
        if (
          mergedOptions.validateInput &&
          !mergedOptions.validateInput(...args)
        ) {
          throw new Prime.ValidationError('Input validation failed');
        }

        // Generate cache key
        let cacheKey;
        try {
          cacheKey = JSON.stringify(args);
        } catch (e) {
          // If args can't be stringified, use a timestamp as key
          cacheKey = `non-serializable-${Date.now()}`;
        }

        // Check for cached result
        if (mergedOptions.memoize && cache.has(cacheKey)) {
          return cache.get(cacheKey);
        }

        // Monitor execution time
        const start = performance.now ? performance.now() : Date.now();

        try {
          // Execute the function
          const result = await fn.apply(this, args);

          // Output validation
          if (
            mergedOptions.validateOutput &&
            !mergedOptions.validateOutput(result, ...args)
          ) {
            throw new Prime.ValidationError('Output validation failed');
          }

          // Record execution time
          const end = performance.now ? performance.now() : Date.now();
          performance._recordExecution(
            fn.name || 'anonymous-async',
            end - start,
          );

          // Cache the result if memoization is enabled
          if (mergedOptions.memoize) {
            cache.set(cacheKey, result);

            // Set up cache expiration
            if (cacheTimers.has(cacheKey)) {
              clearTimeout(cacheTimers.get(cacheKey));
            }

            cacheTimers.set(
              cacheKey,
              setTimeout(() => {
                cache.delete(cacheKey);
                cacheTimers.delete(cacheKey);
              }, mergedOptions.cacheTime),
            );
          }

          return result;
        } catch (error) {
          // Record failed execution
          const end = performance.now ? performance.now() : Date.now();
          performance._recordExecution(
            fn.name || 'anonymous-async',
            end - start,
            error,
          );
          throw error;
        }
      };

      // Add methods to control the cache
      optimized.clearCache = function () {
        cache.clear();

        // Clear all timeouts
        for (const timer of cacheTimers.values()) {
          clearTimeout(timer);
        }
        cacheTimers.clear();

        return true;
      };

      optimized.getCacheSize = function () {
        return cache.size;
      };

      optimized.setCacheTime = function (ms) {
        if (typeof ms !== 'number' || ms < 0) {
          throw new Prime.ValidationError(
            'Cache time must be a positive number',
          );
        }
        mergedOptions.cacheTime = ms;
        return true;
      };

      return optimized;
    },

    /**
     * Get performance statistics
     * @param {string} [name] - Function name filter
     * @returns {Object} Performance statistics
     */
    getStatistics: function (name) {
      if (name) {
        // Filter history by name
        const filtered = this._history.filter((entry) => entry.name === name);

        if (filtered.length === 0) {
          return {
            name,
            calls: 0,
            totalTime: 0,
            averageTime: 0,
          };
        }

        // Calculate statistics
        const totalTime = filtered.reduce((sum, entry) => sum + entry.mean, 0);

        return {
          name,
          calls: filtered.length,
          totalTime,
          averageTime: totalTime / filtered.length,
          history: filtered,
        };
      }

      // Group by name
      const stats = {};

      for (const entry of this._history) {
        if (!stats[entry.name]) {
          stats[entry.name] = {
            calls: 0,
            totalTime: 0,
            history: [],
          };
        }

        stats[entry.name].calls++;
        stats[entry.name].totalTime += entry.mean;
        stats[entry.name].history.push(entry);
      }

      // Calculate averages
      for (const name in stats) {
        stats[name].averageTime = stats[name].totalTime / stats[name].calls;
      }

      return stats;
    },

    /**
     * Clear performance history
     * @returns {number} Number of entries cleared
     */
    clearHistory: function () {
      const count = this._history.length;
      this._history = [];
      return count;
    },

    /**
     * Check if WebAssembly is supported
     * @returns {boolean} True if WebAssembly is supported
     */
    isWebAssemblySupported: function () {
      return (
        typeof WebAssembly === 'object' &&
        typeof WebAssembly.compile === 'function'
      );
    },

    /**
     * Check if Web Workers are supported
     * @returns {boolean} True if Web Workers are supported
     */
    isWorkersSupported: function () {
      return typeof Worker === 'function';
    },

    /**
     * Run a function in a Web Worker thread
     * @param {Function} fn - Function to run
     * @param {Array} args - Arguments to pass to the function
     * @returns {Promise} Promise that resolves with the result
     */
    runInWorker: function (fn, args = []) {
      if (!this.isWorkersSupported()) {
        throw new Prime.InvalidOperationError(
          'Web Workers are not supported in this environment',
        );
      }

      if (!Prime.Utils.isFunction(fn)) {
        throw new Prime.ValidationError('Function is required');
      }

      return new Promise((resolve, reject) => {
        // Convert function to string
        const fnString = fn.toString();

        // Create a worker script as a blob
        const workerScript = `
          self.onmessage = function(e) {
            try {
              // Parse the function from the string representation
              const fn = ${fnString};
              const args = e.data;
              
              // Execute the function with the provided arguments
              const result = fn(...args);
              
              // Send the result back to the main thread
              self.postMessage({ status: 'success', result });
            } catch (error) {
              // Send error information back to the main thread
              self.postMessage({ 
                status: 'error', 
                error: {
                  name: error.name,
                  message: error.message,
                  stack: error.stack
                }
              });
            }
          };
        `;

        // Create the worker
        const blob = new Blob([workerScript], {
          type: 'application/javascript',
        });
        const workerUrl = URL.createObjectURL(blob);
        const worker = new Worker(workerUrl);

        // Set up event handlers
        worker.onmessage = function (e) {
          // Clean up
          worker.terminate();
          URL.revokeObjectURL(workerUrl);

          if (e.data.status === 'success') {
            resolve(e.data.result);
          } else {
            const error = new Error(e.data.error.message);
            error.name = e.data.error.name;
            error.stack = e.data.error.stack;
            reject(error);
          }
        };

        worker.onerror = function (error) {
          // Clean up
          worker.terminate();
          URL.revokeObjectURL(workerUrl);

          reject(new Error(`Worker error: ${error.message}`));
        };

        // Start the worker with the provided arguments
        worker.postMessage(args);
      });
    },

    /**
     * Throttle a function to limit execution frequency
     * @param {Function} fn - Function to throttle
     * @param {number} wait - Time in milliseconds to wait between calls
     * @param {Object} options - Throttle options
     * @returns {Function} Throttled function
     */
    throttle: function (fn, wait, options = {}) {
      // Use the core Utils throttle method
      return Prime.Utils.throttle(fn, wait, options);
    },

    /**
     * Debounce a function to delay execution until input stops
     * @param {Function} fn - Function to debounce
     * @param {number} wait - Time in milliseconds to wait after last call
     * @param {Object} options - Debounce options
     * @returns {Function} Debounced function
     */
    debounce: function (fn, wait, options = {}) {
      // Use the core Utils debounce method
      return Prime.Utils.debounce(fn, wait, options);
    },

    /**
     * Prune the memoization cache to maintain limits
     * @private
     */
    _pruneCache: function () {
      // Get the current memoization limit
      const limit = this.config.memoizationLimit;

      // Check all the known memoized functions
      const functions = Object.values(Prime.Utils._memoizedFunctions || {});

      for (const memoizedFn of functions) {
        // Skip if the function doesn't have a cache property
        if (!memoizedFn.cache) {
          continue;
        }

        // Check if the cache is over the limit
        if (memoizedFn.cache.size > limit) {
          // Get the oldest entries
          const entries = Array.from(memoizedFn.cache.entries());

          // Sort entries by timestamp (if available)
          if (entries.length > 0 && entries[0][1] && entries[0][1].timestamp) {
            entries.sort((a, b) => a[1].timestamp - b[1].timestamp);
          }

          // Remove oldest entries to get back under the limit
          const entriesToRemove = entries.slice(0, entries.length - limit);

          for (const [key] of entriesToRemove) {
            memoizedFn.cache.delete(key);
          }

          if (Prime.Logger && Prime.Logger.debug) {
            Prime.Logger.debug(
              `Pruned ${entriesToRemove.length} entries from memoization cache`,
              {
                functionName: memoizedFn.name || 'anonymous',
                beforeSize: entries.length,
                afterSize: memoizedFn.cache.size,
                limit,
              },
            );
          }
        }
      }

      // Check the instance cache as well
      if (this._cache.size > limit) {
        // Get the oldest entries by timestamp
        const entries = Array.from(this._cache.entries()).sort(
          (a, b) => a[1].timestamp - b[1].timestamp,
        );

        // Remove oldest entries to get back under the limit
        const entriesToRemove = entries.slice(0, entries.length - limit);

        for (const [key] of entriesToRemove) {
          this._cache.delete(key);
        }

        if (Prime.Logger && Prime.Logger.debug) {
          Prime.Logger.debug(
            `Pruned ${entriesToRemove.length} entries from performance cache`,
            {
              beforeSize: entries.length,
              afterSize: this._cache.size,
              limit,
            },
          );
        }
      }
    },

    /**
     * Record a function execution
     * @private
     * @param {string} name - Function name
     * @param {number} time - Execution time
     * @param {Error} [error] - Error if execution failed
     */
    _recordExecution: function (name, time, error) {
      const key = `${name}:${Date.now()}`;

      this._cache.set(key, {
        name,
        time,
        error: error ? error.message : undefined,
        timestamp: Date.now(),
      });

      // Prune cache if needed
      if (this._cache.size > this.config.memoizationLimit) {
        // Remove oldest entries
        const entries = Array.from(this._cache.entries());
        const oldest = entries.slice(
          0,
          entries.length - this.config.memoizationLimit,
        );

        for (const [key] of oldest) {
          this._cache.delete(key);
        }
      }
    },

    /**
     * Calculate a percentile from sorted values
     * @private
     * @param {Array} sorted - Sorted array of values
     * @param {number} percentile - Percentile to calculate
     * @returns {number} Percentile value
     */
    _calculatePercentile: function (sorted, percentile) {
      if (sorted.length === 0) return 0;

      const index = Math.ceil((percentile / 100) * sorted.length) - 1;
      return sorted[Math.min(index, sorted.length - 1)];
    },
  };

  // Export performance to Prime
  Prime.performance = performance;

  // Publish component module loaded event
  Prime.EventBus.publish('module:loaded', { name: 'component-performance' });
})(Prime);

// CommonJS export (no ES module export to avoid circular dependency)
if (typeof module !== 'undefined' && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== 'undefined') {
  window.Prime = Prime;
}
