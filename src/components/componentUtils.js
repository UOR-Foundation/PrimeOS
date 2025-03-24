/**
 * PrimeOS JavaScript Library - Component Utilities
 * Optimized utilities for component operations
 * Version 1.0.0
 */

// Import Prime using CommonJS to avoid circular dependency
const Prime = require("../core.js");

(function (Prime) {
  /**
   * Enhanced component utilities with performance optimizations
   */
  const ComponentUtils = {
    /**
     * Optimized deep cloning specialized for components
     * Uses structured clone API where available and has specialized
     * handling for common component data patterns
     * 
     * @param {*} obj - Object to clone
     * @param {Object} [options] - Cloning options
     * @param {boolean} [options.cacheEnabled=true] - Whether to use object cache
     * @param {boolean} [options.handleCircular=true] - Whether to handle circular references
     * @param {Set} [options._cache] - Internal cache for circular references
     * @returns {*} Cloned object
     */
    fastClone: (obj, options = {}) => {
      // Default options
      const opts = {
        cacheEnabled: options.cacheEnabled !== false,
        handleCircular: options.handleCircular !== false,
        _cache: options._cache || new Map(),
      };

      // Handle primitive values
      if (obj === null || typeof obj !== "object") {
        return obj;
      }
      
      // Try to use native structured clone if available for better performance
      if (typeof structuredClone === 'function') {
        try {
          return structuredClone(obj);
        } catch (e) {
          // Fall back to manual implementation if structured clone fails
          // (e.g., due to DOM nodes, functions, etc.)
        }
      }
      
      // Check cache to handle circular references
      if (opts.handleCircular && opts._cache.has(obj)) {
        return opts._cache.get(obj);
      }
      
      // Handle Date objects
      if (obj instanceof Date) {
        return new Date(obj.getTime());
      }
      
      // Handle Array objects - optimize for common array types
      if (Array.isArray(obj)) {
        // Optimization for arrays of primitives (most common case)
        const isPrimitivesOnly = obj.every(item => 
          item === null || 
          typeof item !== 'object'
        );
        
        if (isPrimitivesOnly) {
          return [...obj]; // Simple spread is much faster for primitives
        }
        
        // For mixed arrays, process each item
        const copy = [];
        
        if (opts.handleCircular) {
          opts._cache.set(obj, copy);
        }
        
        for (let i = 0; i < obj.length; i++) {
          copy[i] = ComponentUtils.fastClone(obj[i], {
            cacheEnabled: opts.cacheEnabled,
            handleCircular: opts.handleCircular,
            _cache: opts._cache
          });
        }
        
        return copy;
      }
      
      // Handle typed arrays efficiently - these are immutable so we can copy the buffer
      if (
        ArrayBuffer.isView(obj) ||
        obj instanceof ArrayBuffer
      ) {
        return obj.slice(0);
      }
      
      // Handle regular Objects
      const copy = {};
      
      if (opts.handleCircular) {
        opts._cache.set(obj, copy);
      }
      
      // Get all own properties including non-enumerable ones if needed
      const keys = Object.keys(obj);
      
      // Fast path for small objects (common in components)
      if (keys.length < 10) {
        for (let i = 0; i < keys.length; i++) {
          const key = keys[i];
          copy[key] = ComponentUtils.fastClone(obj[key], {
            cacheEnabled: opts.cacheEnabled,
            handleCircular: opts.handleCircular,
            _cache: opts._cache
          });
        }
      } else {
        // For larger objects, process in batches for better performance
        for (const key in obj) {
          if (Object.prototype.hasOwnProperty.call(obj, key)) {
            copy[key] = ComponentUtils.fastClone(obj[key], {
              cacheEnabled: opts.cacheEnabled,
              handleCircular: opts.handleCircular,
              _cache: opts._cache
            });
          }
        }
      }
      
      return copy;
    },

    /**
     * Memory-efficient clone optimized for component variant data
     * Only clones modified properties - ideal for state updates
     * 
     * @param {Object} current - Current state object
     * @param {Object} updates - Updated properties
     * @returns {Object} New object with updated properties
     */
    shallowMerge: (current, updates) => {
      if (updates === null || typeof updates !== 'object') {
        return updates;
      }
      
      if (current === null || typeof current !== 'object') {
        return ComponentUtils.fastClone(updates);
      }
      
      // Create a shallow copy of the original
      const result = {...current};
      
      // Apply updates
      for (const key in updates) {
        if (Object.prototype.hasOwnProperty.call(updates, key)) {
          result[key] = updates[key];  
        }
      }
      
      return result;
    },
    
    /**
     * Optimized merge for deep state updates
     * Avoids cloning unchanged branches of the object tree
     * 
     * @param {Object} current - Current state object
     * @param {Object} updates - Deep updates to apply
     * @returns {Object} Efficiently merged result
     */
    efficientMerge: (current, updates) => {
      // Handle simple cases
      if (updates === null || typeof updates !== 'object') {
        return updates;
      }
      
      if (current === null || typeof current !== 'object') {
        return ComponentUtils.fastClone(updates);
      }
      
      // Array handling
      if (Array.isArray(updates)) {
        return ComponentUtils.fastClone(updates);
      }
      
      // Object handling for deep merge
      const result = {...current};
      
      for (const key in updates) {
        if (Object.prototype.hasOwnProperty.call(updates, key)) {
          const currentValue = current[key];
          const updateValue = updates[key];
          
          // Recursive merge for objects
          if (
            updateValue !== null && 
            typeof updateValue === 'object' &&
            currentValue !== null &&
            typeof currentValue === 'object' &&
            !Array.isArray(updateValue)
          ) {
            result[key] = ComponentUtils.efficientMerge(currentValue, updateValue);
          } else {
            // Direct assignment for non-objects or arrays
            result[key] = updateValue;
          }
        }
      }
      
      return result;
    },
    
    /**
     * Check if two objects are deeply equal
     * Used to optimize updates by avoiding unnecessary re-renders
     * 
     * @param {*} obj1 - First object to compare
     * @param {*} obj2 - Second object to compare
     * @returns {boolean} True if objects are deeply equal
     */
    deepEqual: (obj1, obj2) => {
      // Handle simple cases
      if (obj1 === obj2) {
        return true;
      }
      
      // If either is null/undefined but not both
      if (obj1 == null || obj2 == null) {
        return false;
      }
      
      // Get the object types
      const type1 = typeof obj1;
      const type2 = typeof obj2;
      
      // If types differ, objects are not equal
      if (type1 !== type2) {
        return false;
      }
      
      // Handle primitives (already checked === above)
      if (type1 !== 'object') {
        return false;
      }
      
      // Handle dates
      if (obj1 instanceof Date && obj2 instanceof Date) {
        return obj1.getTime() === obj2.getTime();
      }
      
      // Handle arrays
      if (Array.isArray(obj1) && Array.isArray(obj2)) {
        if (obj1.length !== obj2.length) {
          return false;
        }
        
        for (let i = 0; i < obj1.length; i++) {
          if (!ComponentUtils.deepEqual(obj1[i], obj2[i])) {
            return false;
          }
        }
        
        return true;
      }
      
      // Both are objects but not arrays
      if (!Array.isArray(obj1) && !Array.isArray(obj2)) {
        const keys1 = Object.keys(obj1);
        const keys2 = Object.keys(obj2);
        
        if (keys1.length !== keys2.length) {
          return false;
        }
        
        // Check if all keys in obj1 exist in obj2 with same values
        for (const key of keys1) {
          if (!Object.prototype.hasOwnProperty.call(obj2, key)) {
            return false;
          }
          
          if (!ComponentUtils.deepEqual(obj1[key], obj2[key])) {
            return false;
          }
        }
        
        return true;
      }
      
      // One is an array, one is not
      return false;
    }
  };
  
  // Add ComponentUtils to Prime.Components namespace
  Prime.Components = Prime.Components || {};
  Prime.Components.Utils = ComponentUtils;
  
  // Add event publishing wrapped in a try-catch to handle potential initialization issues
  try {
    if (Prime.EventBus && typeof Prime.EventBus.publish === 'function') {
      Prime.EventBus.publish("module:loaded", { name: "component-utils" });
    }
  } catch (err) {
    console.error('Error publishing module:loaded event for component-utils:', err);
  }
})(Prime);

// CommonJS export (no ES module export to avoid circular dependency)
if (typeof module !== "undefined" && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== "undefined") {
  window.Prime = Prime;
}