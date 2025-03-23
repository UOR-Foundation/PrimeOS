/**
 * PrimeOS JavaScript Library - Utility Functions
 * General purpose utilities for use throughout the library
 * Version 1.0.0
 */

// Import Prime object from prime.js
const Prime = require('./prime.js');

(function (Prime) {
  // Core utility functions
  const Utils = {
    /**
     * Checks if a value is a function
     * @param {*} value - Value to check
     * @returns {boolean} True if value is a function
     */
    isFunction: (value) => typeof value === 'function',

    /**
     * Checks if a value is an object
     * @param {*} value - Value to check
     * @returns {boolean} True if value is an object
     */
    isObject: (value) =>
      value !== null && typeof value === 'object' && !Array.isArray(value),

    /**
     * Checks if a value is an array
     * @param {*} value - Value to check
     * @returns {boolean} True if value is an array
     */
    isArray: (value) => Array.isArray(value),

    /**
     * Checks if a value is a string
     * @param {*} value - Value to check
     * @returns {boolean} True if value is a string
     */
    isString: (value) => typeof value === 'string',

    /**
     * Checks if a value is a number
     * @param {*} value - Value to check
     * @returns {boolean} True if value is a number
     */
    isNumber: (value) => typeof value === 'number' && !isNaN(value),

    /**
     * Checks if a value is a boolean
     * @param {*} value - Value to check
     * @returns {boolean} True if value is a boolean
     */
    isBoolean: (value) => typeof value === 'boolean',

    /**
     * Checks if a value is undefined
     * @param {*} value - Value to check
     * @returns {boolean} True if value is undefined
     */
    isUndefined: (value) => typeof value === 'undefined',

    /**
     * Checks if a value is null
     * @param {*} value - Value to check
     * @returns {boolean} True if value is null
     */
    isNull: (value) => value === null,

    /**
     * Checks if a value is null or undefined
     * @param {*} value - Value to check
     * @returns {boolean} True if value is null or undefined
     */
    isNullOrUndefined: (value) =>
      value === null || typeof value === 'undefined',

    /**
     * Generates a UUID v4
     * @returns {string} A UUID v4 string
     */
    uuid: () => {
      return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, (c) => {
        const r = (Math.random() * 16) | 0,
          v = c === 'x' ? r : (r & 0x3) | 0x8;
        return v.toString(16);
      });
    },

    /**
     * Creates a deep clone of an object
     * @param {*} obj - Object to clone
     * @returns {*} Cloned object
     */
    deepClone: (obj) => {
      if (obj === null || typeof obj !== 'object') return obj;

      // Handle Date
      if (obj instanceof Date) {
        return new Date(obj.getTime());
      }

      // Handle Array
      if (Array.isArray(obj)) {
        return obj.map((item) => Utils.deepClone(item));
      }

      // Handle Object
      if (obj instanceof Object) {
        const copy = {};
        for (const attr in obj) {
          if (Object.prototype.hasOwnProperty.call(obj, attr)) {
            copy[attr] = Utils.deepClone(obj[attr]);
          }
        }
        return copy;
      }

      throw new Error('Unable to copy object! Its type is not supported.');
    },

    /**
     * Deeply merges two objects
     * @param {Object} target - Target object
     * @param {Object} source - Source object
     * @returns {Object} Merged object
     */
    deepMerge: (target, source) => {
      if (!Utils.isObject(target) || !Utils.isObject(source)) {
        return source;
      }

      for (const key in source) {
        if (Object.prototype.hasOwnProperty.call(source, key)) {
          if (Utils.isObject(source[key])) {
            // Initialize if undefined or not an object
            if (
              typeof target[key] === 'undefined' ||
              !Utils.isObject(target[key])
            ) {
              target[key] = {};
            }
            Utils.deepMerge(target[key], source[key]);
          } else {
            target[key] = source[key];
          }
        }
      }
      return target;
    },

    /**
     * Creates a debounced function
     * @param {Function} func - Function to debounce
     * @param {number} wait - Milliseconds to wait
     * @returns {Function} Debounced function
     */
    debounce: (func, wait) => {
      let timeout;
      return function executedFunction(...args) {
        const later = () => {
          clearTimeout(timeout);
          func(...args);
        };
        clearTimeout(timeout);
        timeout = setTimeout(later, wait);
      };
    },

    /**
     * Creates a throttled function
     * @param {Function} func - Function to throttle
     * @param {number} limit - Milliseconds to throttle
     * @returns {Function} Throttled function
     */
    throttle: (func, limit) => {
      let inThrottle;
      return function executedFunction(...args) {
        if (!inThrottle) {
          func(...args);
          inThrottle = true;
          setTimeout(() => {
            inThrottle = false;
          }, limit);
        }
      };
    },

    /**
     * Formats a string with named placeholders
     * @param {string} str - String with placeholders like {name}
     * @param {Object} params - Values to replace placeholders
     * @returns {string} Formatted string
     */
    formatString: (str, params) => {
      if (!Utils.isString(str)) return '';
      if (!Utils.isObject(params)) return str;

      return str.replace(/{([^{}]*)}/g, (match, key) => {
        const value = params[key];
        return typeof value !== 'undefined' ? String(value) : match;
      });
    },

    /**
     * Gets a value from an object by path
     * @param {Object} obj - Object to get value from
     * @param {string} path - Path to value in dot notation
     * @param {*} [defaultValue] - Default value if path not found
     * @returns {*} Value at path or defaultValue
     */
    getPath: (obj, path, defaultValue) => {
      if (!Utils.isObject(obj) || !Utils.isString(path)) {
        return defaultValue;
      }

      const keys = path.split('.');
      let current = obj;

      for (let i = 0; i < keys.length; i++) {
        if (current === null || typeof current === 'undefined') {
          return defaultValue;
        }
        current = current[keys[i]];
      }

      return typeof current !== 'undefined' ? current : defaultValue;
    },

    /**
     * Sets a value in an object by path
     * @param {Object} obj - Object to set value in
     * @param {string} path - Path in dot notation
     * @param {*} value - Value to set
     * @returns {Object} Updated object
     */
    setPath: (obj, path, value) => {
      if (!Utils.isObject(obj) || !Utils.isString(path)) {
        return obj;
      }

      const keys = path.split('.');
      let current = obj;

      for (let i = 0; i < keys.length - 1; i++) {
        const key = keys[i];
        if (
          typeof current[key] === 'undefined' ||
          !Utils.isObject(current[key])
        ) {
          current[key] = {};
        }
        current = current[key];
      }

      current[keys[keys.length - 1]] = value;
      return obj;
    },
  };

  // Set Utils directly on Prime
  Prime.Utils = Utils;
})(Prime);

// CommonJS export
if (typeof module !== 'undefined' && module.exports) {
  module.exports = Prime;
}
