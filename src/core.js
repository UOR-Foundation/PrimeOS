/**
 * PrimeOS JavaScript Library - Core
 * Foundation utilities, error classes, version management, and the central Prime object
 * Version 1.0.0
 */

// Use module pattern for encapsulation
const Prime = (function () {
  /**
   * Library version with semantic validation support
   */
  const VERSION = '1.0.0';

  /**
   * Parses a semantic version string into its components
   * @private
   * @param {string} version - Version string to parse (e.g., "1.2.3-alpha.1+build.456")
   * @returns {Object|null} Parsed version object or null if invalid
   */
  const _parseVersion = (version) => {
    if (typeof version !== 'string') return null;

    // Regular expression for SemVer 2.0.0 (major.minor.patch-prerelease+build)
    const semverRegex =
      /^(0|[1-9]\d*)\.?(0|[1-9]\d*)\.?(0|[1-9]\d*)?(?:-((?:0|[1-9]\d*|\d*[a-zA-Z-][0-9a-zA-Z-]*)(?:\.(?:0|[1-9]\d*|\d*[a-zA-Z-][0-9a-zA-Z-]*))*))?(?:\+([0-9a-zA-Z-]+(?:\.[0-9a-zA-Z-]+)*))?$/;

    const match = version.trim().match(semverRegex);
    if (!match) return null;

    const [, majorStr, minorStr, patchStr, prereleaseStr, buildStr] = match;

    // Convert version parts to numbers, handling undefined
    const major = parseInt(majorStr, 10);
    const minor = minorStr !== undefined ? parseInt(minorStr, 10) : 0;
    const patch = patchStr !== undefined ? parseInt(patchStr, 10) : 0;

    // Parse prerelease identifiers
    const prerelease = prereleaseStr ? prereleaseStr.split('.') : [];

    // Parse build metadata
    const build = buildStr ? buildStr.split('.') : [];

    return {
      major,
      minor,
      patch,
      prerelease,
      build,
      original: version,
    };
  };

  /**
   * Compares two prerelease arrays for precedence
   * @private
   * @param {Array} a - First prerelease array
   * @param {Array} b - Second prerelease array
   * @returns {number} -1 if a < b, 0 if a = b, 1 if a > b
   */
  const _comparePrerelease = (a, b) => {
    const aLength = a.length;
    const bLength = b.length;

    // Empty prerelease has higher precedence
    if (aLength === 0 && bLength > 0) return 1;
    if (bLength === 0 && aLength > 0) return -1;
    if (aLength === 0 && bLength === 0) return 0;

    // Compare each identifier in order
    const minLength = Math.min(aLength, bLength);
    for (let i = 0; i < minLength; i++) {
      const identA = a[i];
      const identB = b[i];

      const isANumber = /^\d+$/.test(identA);
      const isBNumber = /^\d+$/.test(identB);

      // Numeric identifiers have lower precedence than non-numeric
      if (isANumber && !isBNumber) return -1;
      if (!isANumber && isBNumber) return 1;

      // Numeric identifiers are compared numerically
      if (isANumber && isBNumber) {
        const numA = parseInt(identA, 10);
        const numB = parseInt(identB, 10);
        if (numA < numB) return -1;
        if (numA > numB) return 1;
        continue;
      }

      // String identifiers are compared lexically
      if (identA < identB) return -1;
      if (identA > identB) return 1;
    }

    // If we get here, all common identifiers are equal
    // A shorter prerelease has higher precedence
    if (aLength < bLength) return -1;
    if (aLength > bLength) return 1;

    return 0;
  };

  /**
   * Validates if the current version satisfies the minimum version requirement
   * @param {string} minVersion - Minimum version requirement (e.g., "1.2.3")
   * @returns {boolean} True if current version satisfies requirement
   * @throws {Error} If the provided version string is invalid
   */
  const validateVersion = (minVersion) => {
    if (!minVersion) return true;

    // Parse current version
    const current = _parseVersion(VERSION);
    if (!current) {
      throw new Error(`Invalid current version: ${VERSION}`);
    }

    // Parse minimum required version
    const required = _parseVersion(minVersion);
    if (!required) {
      throw new Error(`Invalid minimum version requirement: ${minVersion}`);
    }

    // Compare major.minor.patch
    if (current.major > required.major) return true;
    if (current.major < required.major) return false;

    if (current.minor > required.minor) return true;
    if (current.minor < required.minor) return false;

    if (current.patch > required.patch) return true;
    if (current.patch < required.patch) return false;

    // If major.minor.patch are equal, compare prerelease
    // If current has prerelease but required doesn't, current has lower precedence
    if (current.prerelease.length > 0 && required.prerelease.length === 0) {
      return false;
    }

    // If required has prerelease but current doesn't, current has higher precedence
    if (required.prerelease.length > 0 && current.prerelease.length === 0) {
      return true;
    }

    // If both have prerelease, compare them
    if (current.prerelease.length > 0 && required.prerelease.length > 0) {
      const result = _comparePrerelease(
        current.prerelease,
        required.prerelease,
      );
      return result >= 0; // Current must be >= required
    }

    // If we reach here, versions are exactly equal
    return true;
  };

  /**
   * Enhanced utilities with robust error checking
   */
  const Utils = {
    isObject: function (obj) {
      return obj !== null && typeof obj === 'object' && !Array.isArray(obj);
    },

    isFunction: function (fn) {
      return typeof fn === 'function';
    },

    isArray: function (arr) {
      return Array.isArray(arr);
    },

    isNumber: function (num) {
      return typeof num === 'number' && !isNaN(num) && isFinite(num);
    },

    isString: function (str) {
      return typeof str === 'string';
    },

    isBoolean: function (bool) {
      return typeof bool === 'boolean';
    },

    isUndefined: function (val) {
      return typeof val === 'undefined';
    },

    isNull: function (val) {
      return val === null;
    },

    isNullOrUndefined: function (val) {
      return val === null || typeof val === 'undefined';
    },

    isPrimitive: function (val) {
      const type = typeof val;
      return val === null || (type !== 'object' && type !== 'function');
    },

    /**
     * Deep clone an object with circular reference handling and enhanced special object support
     * @param {*} obj - The object to clone
     * @param {Object} [options] - Clone options
     * @param {boolean} [options.preserveNonEnumerable=false] - Whether to preserve non-enumerable properties
     * @param {Set|Array} [options.ignoreProps] - Properties to ignore during cloning
     * @returns {*} Deeply cloned object
     */
    deepClone: function (obj, options = {}) {
      // Early return for primitives
      if (this.isPrimitive(obj)) return obj;

      const preserveNonEnumerable = options.preserveNonEnumerable || false;
      const ignoreProps =
        options.ignoreProps instanceof Set
          ? options.ignoreProps
          : options.ignoreProps
            ? new Set(options.ignoreProps)
            : new Set();

      // Maintain a cache of cloned objects for circular reference detection
      const cache = new WeakMap();

      const clone = (item) => {
        // Handle null first
        if (item === null) return null;

        // Quick check for primitives
        if (this.isPrimitive(item)) return item;

        // Check cache for circular references
        if (cache.has(item)) {
          return cache.get(item);
        }

        let copy;
        const type = Object.prototype.toString.call(item);

        // Handle various object types
        switch (type) {
          case '[object Array]': {
            copy = [];
            cache.set(item, copy);
            for (let i = 0; i < item.length; i++) {
              copy[i] = clone(item[i]);
            }
            return copy;
          }

          case '[object Date]':
            return new Date(item.getTime());

          case '[object RegExp]':
            return new RegExp(item.source, item.flags);

          case '[object Map]': {
            copy = new Map();
            cache.set(item, copy);
            item.forEach((val, key) => {
              copy.set(clone(key), clone(val));
            });
            return copy;
          }

          case '[object Set]': {
            copy = new Set();
            cache.set(item, copy);
            item.forEach((val) => {
              copy.add(clone(val));
            });
            return copy;
          }

          case '[object ArrayBuffer]':
            return item.slice(0);

          case '[object DataView]': {
            const buffer = clone(item.buffer);
            return new DataView(buffer, item.byteOffset, item.byteLength);
          }

          case '[object Int8Array]':
          case '[object Uint8Array]':
          case '[object Uint8ClampedArray]':
          case '[object Int16Array]':
          case '[object Uint16Array]':
          case '[object Int32Array]':
          case '[object Uint32Array]':
          case '[object Float32Array]':
          case '[object Float64Array]': {
            const TypedArrayConstructor = item.constructor;
            return new TypedArrayConstructor(
              clone(item.buffer),
              item.byteOffset,
              item.length,
            );
          }

          case '[object Blob]':
            try {
              return new Blob([item], { type: item.type });
            } catch (e) {
              return item; // Fallback if Blob not supported
            }

          case '[object Function]':
          case '[object GeneratorFunction]':
          case '[object AsyncFunction]':
          case '[object Promise]':
            return item; // Functions, generators, promises aren't cloned

          case '[object Error]':
          case '[object DOMException]': {
            // Clone error objects preserving message and stack
            const ErrorConstructor = item.constructor;
            const error = new ErrorConstructor(item.message);
            // Copy properties like code, name, etc.
            Object.getOwnPropertyNames(item).forEach((prop) => {
              if (
                prop !== 'stack' &&
                prop !== 'message' &&
                !ignoreProps.has(prop)
              ) {
                try {
                  error[prop] = clone(item[prop]);
                } catch (e) {
                  // Some properties might be read-only
                }
              }
            });
            return error;
          }

          case '[object Object]':
          default: {
            // Get the prototype and create a new instance
            const proto = Object.getPrototypeOf(item);
            copy = Object.create(proto);
            cache.set(item, copy);

            // Get property names, including non-enumerable ones if specified
            const propNames = preserveNonEnumerable
              ? Object.getOwnPropertyNames(item)
              : Object.keys(item);

            propNames.forEach((key) => {
              if (ignoreProps.has(key)) return;

              // Handle all property types including getters/setters
              const descriptor = Object.getOwnPropertyDescriptor(item, key);

              try {
                if (descriptor.get || descriptor.set) {
                  // For accessors, preserve the getter/setter as is
                  Object.defineProperty(copy, key, descriptor);
                } else {
                  // For data properties, clone the value
                  const clonedValue = clone(descriptor.value);
                  const newDescriptor = { ...descriptor, value: clonedValue };
                  Object.defineProperty(copy, key, newDescriptor);
                }
              } catch (e) {
                // Some properties might not be configurable or writable
                // In those cases, try a direct assignment as fallback
                try {
                  copy[key] = clone(item[key]);
                } catch (e2) {
                  // If both approaches fail, skip the property
                }
              }
            });

            return copy;
          }
        }
      };

      try {
        return clone(obj);
      } catch (e) {
        // If cloning fails critically, return a new empty object with same prototype
        console.error('Deep clone failed:', e);

        if (typeof obj === 'object' && obj !== null) {
          return Object.create(Object.getPrototypeOf(obj));
        }
        return {};
      }
    },

    /**
     * Memoize a function with configurable cache size limit
     * @param {Function} fn - The function to memoize
     * @param {Object} options - Memoization options
     * @param {number} [options.maxSize=100] - Maximum cache size
     * @param {Function} [options.keyGenerator] - Custom key generator function
     * @param {Function} [options.isEqual] - Function to determine if cached result should be used
     * @returns {Function} - Memoized function
     */
    memoize: function (fn, options = {}) {
      // Use a proper LRU cache with advanced key handling
      const maxSize = options.maxSize || 100;
      const keyGenerator = options.keyGenerator || this._defaultKeyGenerator;
      const isEqual = options.isEqual || this._defaultIsEqual;

      // LRU tracking
      const keyMap = new Map(); // key -> entry
      let newest = null;
      let oldest = null;

      // Create a doubly-linked list for true LRU tracking
      function Entry(key, value) {
        this.key = key;
        this.value = value;
        this.newer = null; // next newer entry
        this.older = null; // previous older entry
        this.originalArgs = null; // store original args for complex equality checks
      }

      // Move entry to front (most recently used)
      function markEntryAsUsed(entry) {
        if (entry === newest) return; // Already the newest

        // Remove from current position
        if (entry.newer) {
          entry.newer.older = entry.older;
        }
        if (entry.older) {
          entry.older.newer = entry.newer;
        }
        if (entry === oldest) {
          oldest = entry.newer;
        }

        // Add to front
        entry.older = newest;
        entry.newer = null;
        if (newest) {
          newest.newer = entry;
        }
        newest = entry;

        if (!oldest) {
          oldest = entry;
        }
      }

      return function (...args) {
        // Generate cache key
        const key = keyGenerator(args);

        // Special handling for undefined keys
        if (key === undefined) {
          return fn.apply(this, args);
        }

        // Check cache with potential deep equality check
        if (keyMap.has(key)) {
          const entry = keyMap.get(key);

          // For complex objects, verify the args are actually equivalent
          if (isEqual(args, entry.originalArgs)) {
            markEntryAsUsed(entry);
            return entry.value;
          }
        }

        // Call the original function
        const result = fn.apply(this, args);

        // Create new cache entry
        const entry = new Entry(key, result);
        entry.originalArgs = args.slice(0); // Store copy of original args
        keyMap.set(key, entry);

        // Handle LRU eviction
        if (keyMap.size > maxSize && oldest) {
          keyMap.delete(oldest.key);
          oldest = oldest.newer;
          if (oldest) oldest.older = null;
        }

        // Add as newest entry
        if (newest) {
          newest.newer = entry;
          entry.older = newest;
        }
        newest = entry;

        if (!oldest) {
          oldest = entry;
        }

        return result;
      };
    },

    /**
     * Default key generator for memoize
     * @private
     * @param {Array} args - Function arguments
     * @returns {string|undefined} Generated key or undefined if not serializable
     */
    _defaultKeyGenerator: function (args) {
      try {
        // Handle primitive arguments efficiently
        if (args.length === 0) return '_empty_';
        if (args.length === 1) {
          const arg = args[0];
          const type = typeof arg;

          // Fast path for primitives
          if (type === 'string') return 's_' + arg;
          if (type === 'number') {
            if (isNaN(arg)) return 'NaN';
            if (!isFinite(arg)) return arg > 0 ? 'Infinity' : '-Infinity';
            return 'n_' + arg;
          }
          if (type === 'boolean') return arg ? 'true' : 'false';
          if (arg === null) return 'null';
          if (arg === undefined) return 'undefined';
        }

        // For multiple or complex arguments, use JSON serialization
        // with additional safety checks
        const seen = new WeakSet();
        const safeStringify = (obj) => {
          return JSON.stringify(obj, (key, value) => {
            // Handle special values
            if (typeof value === 'function') return '[Function]';
            if (typeof value === 'symbol') return value.toString();

            // Detect circular references
            if (typeof value === 'object' && value !== null) {
              if (seen.has(value)) return '[Circular]';
              seen.add(value);
            }
            return value;
          });
        };

        return safeStringify(args);
      } catch (e) {
        // If serialization fails, return undefined to skip caching
        return undefined;
      }
    },

    /**
     * Default equality checker for memoize
     * @private
     * @param {Array} args1 - First set of arguments
     * @param {Array} args2 - Second set of arguments
     * @returns {boolean} Whether the arguments are considered equal
     */
    _defaultIsEqual: function (args1, args2) {
      if (args1.length !== args2.length) return false;

      for (let i = 0; i < args1.length; i++) {
        const a = args1[i];
        const b = args2[i];

        // Identical references or primitive equality
        if (a === b) continue;

        // Special handling for NaN
        if (
          typeof a === 'number' &&
          typeof b === 'number' &&
          isNaN(a) &&
          isNaN(b)
        )
          continue;

        // Different types, references, or values
        return false;
      }

      return true;
    },

    /**
     * Safely get a deeply nested property with a default value
     */
    get: function (obj, path, defaultValue) {
      if (!obj || !path) return defaultValue;

      const keys = this.isArray(path) ? path : path.split('.');
      let result = obj;

      for (const key of keys) {
        if (result === null || result === undefined) {
          return defaultValue;
        }
        result = result[key];
      }

      return result === undefined ? defaultValue : result;
    },

    /**
     * Safely set a deeply nested property
     */
    set: function (obj, path, value) {
      if (!obj || !path) return obj;

      const keys = this.isArray(path) ? path : path.split('.');
      let current = obj;

      for (let i = 0; i < keys.length - 1; i++) {
        const key = keys[i];
        if (current[key] === undefined) {
          current[key] = {};
        }
        current = current[key];
      }

      current[keys[keys.length - 1]] = value;
      return obj;
    },

    /**
     * Throttle a function to limit execution frequency with high precision timing
     * @param {Function} fn - The function to throttle
     * @param {number} delay - The delay in milliseconds
     * @param {Object} [options] - Throttle options
     * @param {boolean} [options.leading=true] - Whether to execute on the leading edge
     * @param {boolean} [options.trailing=true] - Whether to execute on the trailing edge
     * @param {boolean} [options.highResolution=false] - Whether to use high resolution timing
     * @returns {Function} Throttled function
     */
    throttle: function (fn, delay, options = {}) {
      if (typeof delay !== 'number' || isNaN(delay) || delay < 0) {
        throw new Error('Throttle delay must be a positive number');
      }

      const leading = options.leading !== false;
      const trailing = options.trailing !== false;
      const highResolution = options.highResolution === true;

      let lastCallTime = 0;
      // this variable is used in several places, but appears unused in lint
      /* eslint-disable-next-line no-unused-vars */
      let lastInvokeTime = 0;
      let timerId = null;
      let lastArgs = null;
      let lastThis = null;
      let result;

      // Function to clear the timeout
      const cancelTimer = () => {
        if (timerId !== null) {
          clearTimeout(timerId);
          timerId = null;
        }
      };

      // Function to get current time with high precision if available
      const now = () => {
        if (
          highResolution &&
          typeof performance !== 'undefined' &&
          typeof performance.now === 'function'
        ) {
          return performance.now();
        }
        return Date.now();
      };

      // The main throttled function
      function throttled(...args) {
        const time = now();
        const isInvoking = shouldInvoke(time);

        lastArgs = args;
        lastThis = this;

        if (isInvoking) {
          if (timerId === null && leading) {
            // Invoke immediately on the leading edge
            lastInvokeTime = time;
            result = invokeFunc();
            return result;
          }

          if (trailing) {
            // Schedule a trailing invocation
            return startTimer(time);
          }
        }

        if (timerId === null && trailing) {
          // If no timer is active but we need trailing execution
          return startTimer(time);
        }

        return result;
      }

      // Determine if we should invoke the function now
      function shouldInvoke(time) {
        const timeSinceLastCall = time - lastCallTime;
        // Variable below is not used in this implementation
        // const timeSinceLastInvoke = time - lastInvokeTime;

        // First call, invoke immediately
        if (lastCallTime === 0) return true;

        // Time since last call exceeds delay, invoke
        return timeSinceLastCall >= delay || timeSinceLastCall < 0;
      }

      // Invoke the function with proper this context and args
      function invokeFunc() {
        const args = lastArgs;
        const thisArg = lastThis;

        lastArgs = lastThis = null;
        lastInvokeTime = now();

        result = fn.apply(thisArg, args);
        return result;
      }

      // Start a timer for trailing edge execution
      function startTimer(time) {
        lastCallTime = time;

        timerId = setTimeout(() => {
          const timeNow = now();
          lastCallTime = timeNow;
          invokeFunc();
        }, delay);

        return result;
      }

      // Add a cancel method to the throttled function
      throttled.cancel = cancelTimer;

      return throttled;
    },

    /**
     * Debounce a function to delay execution until input stops
     * @param {Function} fn - The function to debounce
     * @param {number} delay - The delay in milliseconds
     * @param {Object} [options] - Debounce options
     * @param {boolean} [options.leading=false] - Whether to execute on the leading edge
     * @param {boolean} [options.trailing=true] - Whether to execute on the trailing edge
     * @param {boolean} [options.maxWait] - Maximum time to wait before invoking
     * @param {boolean} [options.highResolution=false] - Whether to use high resolution timing
     * @returns {Function} Debounced function
     */
    debounce: function (fn, delay, options = {}) {
      if (typeof delay !== 'number' || isNaN(delay) || delay < 0) {
        throw new Error('Debounce delay must be a positive number');
      }

      const leading = options.leading === true;
      const trailing = options.trailing !== false;
      const maxWait = options.maxWait;
      const highResolution = options.highResolution === true;

      // Validate that maxWait is greater than or equal to delay if specified
      if (
        maxWait !== undefined &&
        (typeof maxWait !== 'number' || maxWait < delay)
      ) {
        throw new Error(
          'maxWait must be a number greater than or equal to delay',
        );
      }

      let timerId = null;
      let lastCallTime = 0;
      let lastInvokeTime = 0;
      let lastArgs = null;
      let lastThis = null;
      let result;

      // Function to clear the timeout
      const cancelTimer = () => {
        if (timerId !== null) {
          clearTimeout(timerId);
          timerId = null;
        }
      };

      // Function to get current time with high precision if available
      const now = () => {
        if (
          highResolution &&
          typeof performance !== 'undefined' &&
          typeof performance.now === 'function'
        ) {
          return performance.now();
        }
        return Date.now();
      };

      // Check if we should invoke the function due to maxWait
      function shouldInvoke(time) {
        const timeSinceLastCall = time - lastCallTime;
        const timeSinceLastInvoke = time - lastInvokeTime;

        // First call, only invoke if leading
        if (lastCallTime === 0) return leading;

        // If we have a maxWait and it's exceeded, we should invoke
        if (maxWait !== undefined && timeSinceLastInvoke >= maxWait) {
          return true;
        }

        // Otherwise, only invoke if we've waited enough time since the last call
        return timeSinceLastCall >= delay;
      }

      // Invoke the function and update invoke time
      function invokeFunc(time) {
        const args = lastArgs;
        const thisArg = lastThis;

        lastArgs = lastThis = null;
        lastInvokeTime = time;

        result = fn.apply(thisArg, args);
        return result;
      }

      // Schedule a trailing invocation
      function startTimer(pendingFn, wait) {
        cancelTimer();

        timerId = setTimeout(pendingFn, wait);
      }

      // Calculate how long to wait for the trailing invocation
      function remainingWait(time) {
        const timeSinceLastCall = time - lastCallTime;
        const timeSinceLastInvoke = time - lastInvokeTime;
        const timeWaiting = delay - timeSinceLastCall;

        // If maxWait is specified, make sure we don't wait longer than necessary
        if (maxWait !== undefined) {
          const maxTimeWaiting = maxWait - timeSinceLastInvoke;
          return Math.min(timeWaiting, maxTimeWaiting);
        }

        return timeWaiting;
      }

      // Function to handle the timeout
      function timerExpired() {
        const time = now();

        if (shouldInvoke(time)) {
          return trailingEdge(time);
        }

        // Restart the timer with the remaining wait time
        startTimer(timerExpired, remainingWait(time));
      }

      // Handle the leading edge invocation
      function leadingEdge(time) {
        lastInvokeTime = time;

        // Schedule a trailing edge invocation if needed
        if (trailing) {
          startTimer(timerExpired, delay);
        }

        return invokeFunc(time);
      }

      // Handle the trailing edge invocation
      function trailingEdge(time) {
        timerId = null;

        // Only invoke if we have lastArgs, which means the function was called
        if (trailing && lastArgs) {
          return invokeFunc(time);
        }

        lastArgs = lastThis = null;
        return result;
      }

      // The main debounced function
      function debounced(...args) {
        const time = now();
        const isInvoking = shouldInvoke(time);

        lastArgs = args;
        lastThis = this;
        lastCallTime = time;

        // If the timer is not running, start it
        if (isInvoking) {
          if (timerId === null) {
            return leadingEdge(time);
          }

          // If maxWait is specified, and we're in the middle of waiting,
          // restart the timer to ensure we don't wait longer than necessary
          if (maxWait !== undefined) {
            startTimer(timerExpired, delay);
            return invokeFunc(time);
          }
        }

        // If no timer is running, start one
        if (timerId === null) {
          startTimer(timerExpired, delay);
        }

        return result;
      }

      // Add cancel and flush methods to the debounced function
      debounced.cancel = function () {
        cancelTimer();
        lastInvokeTime = 0;
        lastCallTime = 0;
        lastArgs = lastThis = null;
      };

      debounced.flush = function () {
        if (timerId !== null) {
          return trailingEdge(now());
        }
        return result;
      };

      debounced.pending = function () {
        return timerId !== null;
      };

      return debounced;
    },

    /**
     * Create a UUID for unique identification
     * Implements RFC4122 v4 UUID with improved randomness
     * @returns {string} A version 4 UUID
     */
    uuid: function () {
      // Use a more robust random number generation
      let getRandomValues;

      if (
        typeof crypto !== 'undefined' &&
        typeof crypto.getRandomValues === 'function'
      ) {
        // Browser environment with crypto support
        getRandomValues = function (arr) {
          return crypto.getRandomValues(arr);
        };
      } else if (typeof require === 'function') {
        try {
          // Node.js environment - try to use crypto module
          const nodeCrypto = require('crypto');
          getRandomValues = function (arr) {
            return nodeCrypto.randomFillSync(arr);
          };
        } catch (e) {
          // Fallback to Math.random with warning
          console.warn(
            'PrimeOS: Cryptographically secure random values unavailable, using Math.random fallback',
          );
          getRandomValues = function (arr) {
            for (let i = 0; i < arr.length; i++) {
              arr[i] = Math.floor(Math.random() * 256);
            }
            return arr;
          };
        }
      } else {
        // Last resort fallback
        getRandomValues = function (arr) {
          for (let i = 0; i < arr.length; i++) {
            arr[i] = Math.floor(Math.random() * 256);
          }
          return arr;
        };
      }

      // Generate 16 random bytes
      const buffer = new Uint8Array(16);
      getRandomValues(buffer);

      // Set version (4) and variant (RFC4122)
      buffer[6] = (buffer[6] & 0x0f) | 0x40; // version 4
      buffer[8] = (buffer[8] & 0x3f) | 0x80; // variant RFC4122

      // Format as UUID string
      let uuid = '';
      for (let i = 0; i < 16; i++) {
        if (i === 4 || i === 6 || i === 8 || i === 10) {
          uuid += '-';
        }
        let hex = buffer[i].toString(16);
        if (hex.length === 1) {
          hex = '0' + hex;
        }
        uuid += hex;
      }

      return uuid;
    },
  };

  /**
   * Comprehensive error hierarchy
   */
  class PrimeError extends Error {
    constructor(message, options = {}) {
      super(message);
      this.name = 'PrimeError';
      this.timestamp = new Date();
      this.code = options.code || 'GENERIC_ERROR';

      // Capture stack trace
      if (Error.captureStackTrace) {
        Error.captureStackTrace(this, this.constructor);
      }

      // Additional context if provided
      if (options.context) {
        this.context = options.context;
      }
    }

    toString() {
      let result = `${this.name}: ${this.message}`;
      if (this.code) {
        result += ` [${this.code}]`;
      }
      if (this.context) {
        result += `\nContext: ${JSON.stringify(this.context)}`;
      }
      return result;
    }
  }

  class CoherenceViolationError extends PrimeError {
    constructor(message, constraint, magnitude, options = {}) {
      super(message, {
        code: options.code || 'COHERENCE_VIOLATION',
        context: { ...options.context, constraint, magnitude },
      });
      this.name = 'CoherenceViolationError';
      this.constraint = constraint;
      this.magnitude = magnitude;
    }
  }

  /**
   * Error thrown when an operation would reduce coherence below acceptable threshold
   * Represents mathematical inconsistency in the system state
   */
  class CoherenceError extends PrimeError {
    constructor(message, options = {}) {
      super(message, {
        code: options.code || 'COHERENCE_ERROR',
        context: options.context,
      });
      this.name = 'CoherenceError';

      // Store coherence metrics if provided
      if (options.context && options.context.currentScore !== undefined) {
        this.currentScore = options.context.currentScore;
      }
      if (options.context && options.context.projectedScore !== undefined) {
        this.projectedScore = options.context.projectedScore;
      }
      if (options.context && options.context.threshold !== undefined) {
        this.threshold = options.context.threshold;
      }
    }
  }

  class MathematicalError extends PrimeError {
    constructor(message, options = {}) {
      super(message, {
        code: options.code || 'MATHEMATICAL_ERROR',
        context: options.context,
      });
      this.name = 'MathematicalError';
    }
  }

  class InvalidOperationError extends PrimeError {
    constructor(message, options = {}) {
      super(message, {
        code: options.code || 'INVALID_OPERATION',
        context: options.context,
      });
      this.name = 'InvalidOperationError';
    }
  }

  class ConfigurationError extends PrimeError {
    constructor(message, options = {}) {
      super(message, {
        code: options.code || 'CONFIGURATION_ERROR',
        context: options.context,
      });
      this.name = 'ConfigurationError';
    }
  }

  class ValidationError extends PrimeError {
    constructor(message, options = {}) {
      super(message, {
        code: options.code || 'VALIDATION_ERROR',
        context: options.context,
      });
      this.name = 'ValidationError';
    }
  }

  /**
   * Global event bus for framework communication
   */
  const EventBus = {
    events: {},

    /**
     * Subscribe to an event with a callback
     * @param {string} event - Event name
     * @param {Function} callback - Callback function
     * @returns {Function} Unsubscribe function
     */
    subscribe: function (event, callback) {
      if (!Utils.isString(event)) {
        throw new ValidationError('Event name must be a string', {
          context: { providedType: typeof event },
        });
      }

      if (!Utils.isFunction(callback)) {
        throw new ValidationError('Callback must be a function', {
          context: { providedType: typeof callback },
        });
      }

      if (!this.events[event]) {
        this.events[event] = [];
      }

      this.events[event].push(callback);

      // Return unsubscribe function
      return () => this.unsubscribe(event, callback);
    },

    /**
     * Publish an event with data
     * @param {string} event - Event name
     * @param {*} data - Event data
     * @param {Object} [options] - Publication options
     * @param {string} [options.errorMode='log'] - Error handling mode: 'log', 'throw', 'silence', or 'callback'
     * @param {Function} [options.errorCallback] - Callback for errors when errorMode is 'callback'
     * @returns {Array} Array of results from successful callbacks, or errors if errorMode is 'throw'
     */
    publish: function (event, data, options = {}) {
      if (!this.events[event]) {
        return [];
      }

      const errorMode = options.errorMode || 'log';
      const errorCallback = options.errorCallback;
      const results = [];
      const errors = [];

      for (const callback of this.events[event]) {
        try {
          // Execute the callback and collect its result
          const result = callback(data);
          results.push(result);
        } catch (error) {
          // Enhanced error handling with multiple strategies
          errors.push({
            error,
            event,
            handler: callback.name || 'anonymous',
            timestamp: new Date(),
          });

          switch (errorMode) {
            case 'throw':
              // Collect all errors and throw at the end
              break;

            case 'callback':
              // Call the provided error callback
              if (typeof errorCallback === 'function') {
                try {
                  errorCallback(error, event, callback);
                } catch (callbackError) {
                  console.error(
                    'Error in event error callback:',
                    callbackError,
                  );
                }
              } else {
                console.error(`Error in event handler for ${event}:`, error);
              }
              break;

            case 'silence':
              // Silently ignore the error
              break;

            case 'log':
            default:
              // Log the error (default behavior)
              console.error(`Error in event handler for ${event}:`, error);
              console.error(`Stack trace: ${error.stack}`);
              break;
          }
        }
      }

      // If in 'throw' mode and we have errors, throw a composite error
      if (errorMode === 'throw' && errors.length > 0) {
        const compositeError = new Error(
          `${errors.length} errors occurred during event handling`,
        );
        compositeError.name = 'EventHandlerError';
        compositeError.errors = errors;
        throw compositeError;
      }

      return results;
    },

    /**
     * Unsubscribe from an event
     * @param {string} event - Event name
     * @param {Function} callback - Callback function
     * @returns {boolean} Success
     */
    unsubscribe: function (event, callback) {
      if (!this.events[event]) {
        return false;
      }

      const index = this.events[event].indexOf(callback);
      if (index !== -1) {
        this.events[event].splice(index, 1);

        // Clean up empty event arrays
        if (this.events[event].length === 0) {
          delete this.events[event];
        }

        return true;
      }

      return false;
    },

    /**
     * Clear all event subscriptions or for a specific event
     * @param {string} [event] - Optional event name
     */
    clear: function (event) {
      if (event) {
        delete this.events[event];
      } else {
        this.events = {};
      }
    },
  };

  /**
   * Module loader with environment detection
   */
  const ModuleLoader = {
    /**
     * Check the current JavaScript environment
     * @returns {string} Environment type: 'browser', 'node', 'worker', or 'unknown'
     */
    detectEnvironment: function () {
      if (typeof window !== 'undefined' && typeof document !== 'undefined') {
        return 'browser';
      }

      if (
        typeof process !== 'undefined' &&
        process.versions &&
        process.versions.node
      ) {
        return 'node';
      }

      if (
        typeof self !== 'undefined' &&
        typeof self.WorkerGlobalScope !== 'undefined' &&
        self instanceof self.WorkerGlobalScope
      ) {
        return 'worker';
      }

      return 'unknown';
    },

    /**
     * Load a module dynamically
     * @param {string} modulePath - Path to module
     * @returns {Promise} Promise that resolves with the loaded module
     */
    load: async function (modulePath) {
      const env = this.detectEnvironment();

      if (env === 'browser' || env === 'worker') {
        try {
          return await import(modulePath);
        } catch (error) {
          throw new InvalidOperationError(
            `Failed to load module: ${modulePath}`,
            {
              context: { error: error.message },
            },
          );
        }
      } else if (env === 'node') {
        try {
          // Use dynamic import for Node.js ESM compatibility
          return await import(modulePath);
        } catch (error) {
          throw new InvalidOperationError(
            `Failed to load module: ${modulePath}`,
            {
              context: { error: error.message },
            },
          );
        }
      } else {
        throw new InvalidOperationError(
          'Module loading not supported in this environment',
        );
      }
    },

    /**
     * Register a module in the Prime namespace
     * @param {string} name - Module name
     * @param {Object} module - Module object
     */
    register: function (name, module) {
      if (!Utils.isString(name)) {
        throw new ValidationError('Module name must be a string');
      }

      if (!Utils.isObject(module)) {
        throw new ValidationError('Module must be an object');
      }

      // Extend Prime with the module
      Prime[name] = module;

      EventBus.publish('module:loaded', { name, module });

      return true;
    },
  };

  /**
   * Testing utilities for the Prime framework
   */
  const Testing = {
    /**
     * Assert that a condition is true
     * @param {boolean} condition - Condition to check
     * @param {string} message - Error message if condition is false
     */
    assert: function (condition, message = 'Assertion failed') {
      if (!condition) {
        throw new ValidationError(message);
      }
    },

    /**
     * Create a mock object for testing
     * @param {Object} template - Template object to mock
     * @returns {Object} Mock object
     */
    createMock: function (template = {}) {
      const mock = {
        calls: {},
        results: {},
        ...Utils.deepClone(template),
      };

      // Track calls to all methods
      Object.keys(mock).forEach((key) => {
        if (
          Utils.isFunction(mock[key]) &&
          key !== 'calls' &&
          key !== 'results'
        ) {
          const originalFn = mock[key];

          mock[key] = function (...args) {
            // Record call
            if (!mock.calls[key]) {
              mock.calls[key] = [];
            }
            mock.calls[key].push(args);

            // Return predefined result if available
            if (mock.results[key]) {
              if (Utils.isFunction(mock.results[key])) {
                return mock.results[key](...args);
              }
              return mock.results[key];
            }

            // Otherwise call original function
            return originalFn.apply(this, args);
          };
        }
      });

      return mock;
    },

    /**
     * Create a spy function that tracks calls
     * @param {Function} [fn] - Original function to spy on
     * @returns {Function} Spy function
     */
    createSpy: function (fn = () => {}) {
      const calls = [];

      const spy = function (...args) {
        calls.push(args);
        return fn.apply(this, args);
      };

      spy.calls = calls;
      spy.getCallCount = () => calls.length;
      spy.reset = () => {
        calls.length = 0;
      };

      return spy;
    },
  };

  /**
   * Internal logger with configurable levels
   */
  const Logger = {
    levels: {
      DEBUG: 0,
      INFO: 1,
      WARN: 2,
      ERROR: 3,
      NONE: 4,
    },

    currentLevel: 1, // Default to INFO

    setLevel: function (level) {
      if (Utils.isString(level)) {
        if (this.levels[level.toUpperCase()] !== undefined) {
          this.currentLevel = this.levels[level.toUpperCase()];
        } else {
          throw new ValidationError(`Invalid log level: ${level}`);
        }
      } else if (Utils.isNumber(level) && level >= 0 && level <= 4) {
        this.currentLevel = level;
      } else {
        throw new ValidationError('Log level must be a valid string or number');
      }
    },

    shouldLog: function (level) {
      return this.levels[level] >= this.currentLevel;
    },

    format: function (level, message, context) {
      let output = `[Prime] [${level}] ${message}`;
      if (context) {
        output += `\nContext: ${JSON.stringify(context)}`;
      }
      return output;
    },

    debug: function (message, context) {
      if (this.shouldLog('DEBUG')) {
        console.debug(this.format('DEBUG', message, context));
      }
    },

    info: function (message, context) {
      if (this.shouldLog('INFO')) {
        console.info(this.format('INFO', message, context));
      }
    },

    warn: function (message, context) {
      if (this.shouldLog('WARN')) {
        console.warn(this.format('WARN', message, context));
      }
    },

    error: function (message, context) {
      if (this.shouldLog('ERROR')) {
        console.error(this.format('ERROR', message, context));
      }
    },
  };

  /**
   * Return core Prime object (to be extended by other modules)
   */
  return {
    // Version information
    version: VERSION,
    validateVersion,

    // Core utilities
    Utils,
    EventBus,
    ModuleLoader,
    Testing,
    Logger,

    // Error classes
    PrimeError,
    CoherenceViolationError,
    CoherenceError,
    MathematicalError,
    InvalidOperationError,
    ConfigurationError,
    ValidationError,

    // Version compatibility system
    isCompatible: function (requirements) {
      // Basic validation
      if (!requirements) {
        return false;
      }
      
      const features = requirements.features || [];
      const minVersion = requirements.minVersion || '0.0.0';

      // Check version compatibility
      if (!validateVersion(minVersion)) {
        return false;
      }

      // Check feature availability
      for (const feature of features) {
        if (feature === 'coherence' && !this.coherence) return false;
        if (feature === 'spectral' && !this.spectral) return false;
        if (feature === 'lie' && !this.Lie) return false;
      }

      return true;
    },

    // Deprecation warning system
    deprecationWarnings: [],

    addDeprecationWarning: function (warning) {
      this.deprecationWarnings.push(warning);
    },

    getDeprecationWarnings: function () {
      return [...this.deprecationWarnings];
    },
  };
})();

// For CommonJS compatibility
if (typeof module !== 'undefined' && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== 'undefined') {
  window.Prime = Prime;
}
