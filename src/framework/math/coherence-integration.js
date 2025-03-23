/**
 * PrimeOS Framework Math - Coherence Integration Module
 * Provides integration between mathematical coherence modules and the system-wide coherence tracking
 * 
 * This module serves as a bridge between the specialized mathematical coherence implementations
 * and the broader framework coherence system, allowing them to work together smoothly.
 */

// Import Prime core directly to avoid circular dependencies
const Prime = require('../../core/prime.js');

// Import our math modules
const coherence = require('./coherence.js');
const patternRecognition = require('./patternRecognition.js');
const TypeValidation = require('./type-validation.js');

/**
 * CoherenceIntegration provides utilities for connecting mathematical coherence 
 * operations with the broader system coherence tracking
 */
class CoherenceIntegration {
  /**
   * Creates a new CoherenceIntegration instance
   * @param {Object} options Configuration options
   */
  constructor(options = {}) {
    // Validate options if provided
    if (options !== undefined) {
      TypeValidation.assertObject(options, 'options', { 
        operation: 'CoherenceIntegration.constructor' 
      });
    }
    
    this.options = options;
    this.registeredComponents = [];
    this.coherenceMetrics = new Map();
    this.systemCoherenceEnabled = options.enableSystemCoherence !== false;
    
    // Initialize coherence tracking for mathematical modules
    this._initializeCoherenceTracking();
  }
  
  /**
   * Initialize coherence tracking for mathematical modules
   * @private
   */
  _initializeCoherenceTracking() {
    // Check if system coherence tracking is available
    if (this.systemCoherenceEnabled && 
        Prime.coherence && 
        Prime.coherence.systemCoherence && 
        typeof Prime.coherence.systemCoherence.register === 'function') {
      // Register for system-wide coherence tracking
      this.systemCoherenceAvailable = true;
    } else {
      // Fall back to local tracking only
      this.systemCoherenceAvailable = false;
      Prime.Logger.info(
        'System coherence tracking not available. Using local tracking only.',
        { context: { module: 'CoherenceIntegration' } }
      );
    }
  }
  
  /**
   * Register a CliffordAlgebraFiber for coherence tracking
   * 
   * @param {Object} fiber The CliffordAlgebraFiber instance to register
   * @param {Object} options Registration options
   * @param {number} options.weight Weight of this component in coherence calculations (default: 1)
   * @returns {Function} Unregister function
   */
  registerFiber(fiber, options = {}) {
    // Validate fiber is a CliffordAlgebraFiber
    if (!fiber || typeof fiber !== 'object' || fiber.constructor.name !== 'CliffordAlgebraFiber') {
      throw new Prime.ValidationError('Invalid fiber object', {
        operation: 'CoherenceIntegration.registerFiber',
        expectedType: 'CliffordAlgebraFiber',
        actualType: fiber ? fiber.constructor.name : typeof fiber
      });
    }
    
    // Validate options
    if (options !== undefined) {
      TypeValidation.assertObject(options, 'options', { 
        operation: 'CoherenceIntegration.registerFiber' 
      });
      
      if (options.weight !== undefined) {
        TypeValidation.assertPositiveNumber(options.weight, 'options.weight', {
          operation: 'CoherenceIntegration.registerFiber'
        });
      }
    }
    
    const weight = options.weight || 1;
    const unregisterFunctions = [];
    
    // Create a coherence-compatible wrapper for the fiber
    const fiberWrapper = {
      fiber,
      // Provide a norm() method for the coherence system
      norm: () => {
        try {
          return fiber.computeNorm();
        } catch (error) {
          Prime.Logger.warn(
            'Error computing fiber norm for coherence tracking',
            {
              operation: 'CoherenceIntegration.fiberWrapper.norm',
              error: error.message
            }
          );
          return 1; // Fallback to neutral value
        }
      }
    };
    
    // Register with system coherence if available
    if (this.systemCoherenceAvailable) {
      try {
        const unregister = Prime.coherence.systemCoherence.register(fiberWrapper, weight);
        unregisterFunctions.push(unregister);
      } catch (error) {
        Prime.Logger.warn(
          'Error registering fiber with system coherence',
          {
            operation: 'CoherenceIntegration.registerFiber',
            error: error.message
          }
        );
      }
    }
    
    // Add to local tracking
    this.registeredComponents.push({
      component: fiberWrapper,
      weight: weight,
      type: 'fiber'
    });
    
    // Return a function to unregister this component
    return () => {
      // Call all unregister functions
      unregisterFunctions.forEach(fn => {
        try {
          if (typeof fn === 'function') {
            fn();
          }
        } catch (error) {
          Prime.Logger.warn(
            'Error unregistering component',
            {
              operation: 'CoherenceIntegration.unregister',
              error: error.message
            }
          );
        }
      });
      
      // Remove from local tracking
      const index = this.registeredComponents.findIndex(c => c.component === fiberWrapper);
      if (index >= 0) {
        this.registeredComponents.splice(index, 1);
      }
    };
  }
  
  /**
   * Register a CoherenceGradientDescent optimizer for coherence tracking
   * 
   * @param {Object} optimizer The CoherenceGradientDescent instance to register
   * @param {Object} options Registration options
   * @param {number} options.weight Weight of this component in coherence calculations (default: 1)
   * @returns {Function} Unregister function
   */
  registerOptimizer(optimizer, options = {}) {
    // Validate optimizer is a CoherenceGradientDescent
    if (!optimizer || typeof optimizer !== 'object' || optimizer.constructor.name !== 'CoherenceGradientDescent') {
      throw new Prime.ValidationError('Invalid optimizer object', {
        operation: 'CoherenceIntegration.registerOptimizer',
        expectedType: 'CoherenceGradientDescent',
        actualType: optimizer ? optimizer.constructor.name : typeof optimizer
      });
    }
    
    // Validate options
    if (options !== undefined) {
      TypeValidation.assertObject(options, 'options', { 
        operation: 'CoherenceIntegration.registerOptimizer' 
      });
      
      if (options.weight !== undefined) {
        TypeValidation.assertPositiveNumber(options.weight, 'options.weight', {
          operation: 'CoherenceIntegration.registerOptimizer'
        });
      }
    }
    
    const weight = options.weight || 1;
    const unregisterFunctions = [];
    
    // Create a coherence-compatible wrapper for the optimizer
    const optimizerWrapper = {
      optimizer,
      // Provide a norm() method for the coherence system
      norm: () => {
        try {
          // For CoherenceGradientDescent, we can use the best coherence value
          // Lower coherence values are better, so we invert for the norm
          // (which expects higher values to be better)
          if (optimizer.bestCoherence !== undefined && Number.isFinite(optimizer.bestCoherence)) {
            const coherenceValue = optimizer.bestCoherence;
            // If coherence is a measure of violation (lower is better),
            // map to [0,1] range where higher is better
            return Math.max(0, Math.min(1, 1 - coherenceValue / 10));
          }
          return 0.5; // Neutral value if no coherence information is available
        } catch (error) {
          Prime.Logger.warn(
            'Error computing optimizer norm for coherence tracking',
            {
              operation: 'CoherenceIntegration.optimizerWrapper.norm',
              error: error.message
            }
          );
          return 0.5; // Fallback to neutral value
        }
      },
      
      // Provide an optimize() method for the coherence system
      optimize: (options = {}) => {
        try {
          // If no problem is encoded yet, nothing to optimize
          if (!optimizer.encodedProblem) {
            return optimizerWrapper;
          }
          
          // Run one optimization step
          optimizer.solve(optimizer.encodedProblem, { 
            maxIterations: options.maxIterations || 1,
            restartCount: 1
          });
          
          return optimizerWrapper;
        } catch (error) {
          Prime.Logger.warn(
            'Error during optimizer optimization for coherence',
            {
              operation: 'CoherenceIntegration.optimizerWrapper.optimize',
              error: error.message
            }
          );
          return optimizerWrapper;
        }
      }
    };
    
    // Register with system coherence if available
    if (this.systemCoherenceAvailable) {
      try {
        const unregister = Prime.coherence.systemCoherence.register(optimizerWrapper, weight);
        unregisterFunctions.push(unregister);
      } catch (error) {
        Prime.Logger.warn(
          'Error registering optimizer with system coherence',
          {
            operation: 'CoherenceIntegration.registerOptimizer',
            error: error.message
          }
        );
      }
    }
    
    // Add to local tracking
    this.registeredComponents.push({
      component: optimizerWrapper,
      weight: weight,
      type: 'optimizer'
    });
    
    // Return a function to unregister this component
    return () => {
      // Call all unregister functions
      unregisterFunctions.forEach(fn => {
        try {
          if (typeof fn === 'function') {
            fn();
          }
        } catch (error) {
          Prime.Logger.warn(
            'Error unregistering component',
            {
              operation: 'CoherenceIntegration.unregister',
              error: error.message
            }
          );
        }
      });
      
      // Remove from local tracking
      const index = this.registeredComponents.findIndex(c => c.component === optimizerWrapper);
      if (index >= 0) {
        this.registeredComponents.splice(index, 1);
      }
    };
  }
  
  /**
   * Register a pattern recognition system for coherence tracking
   * 
   * @param {Object} patternSystem The pattern recognition system to register
   * @param {Object} options Registration options
   * @param {number} options.weight Weight of this component in coherence calculations (default: 1)
   * @returns {Function} Unregister function
   */
  registerPatternSystem(patternSystem, options = {}) {
    // Validate patternSystem is either FiberAlgebraPatternRecognition or SequencePatternRecognition
    if (!patternSystem || typeof patternSystem !== 'object' || 
        (patternSystem.constructor.name !== 'FiberAlgebraPatternRecognition' && 
         patternSystem.constructor.name !== 'SequencePatternRecognition')) {
      throw new Prime.ValidationError('Invalid pattern recognition system', {
        operation: 'CoherenceIntegration.registerPatternSystem',
        expectedType: 'FiberAlgebraPatternRecognition or SequencePatternRecognition',
        actualType: patternSystem ? patternSystem.constructor.name : typeof patternSystem
      });
    }
    
    // Validate options
    if (options !== undefined) {
      TypeValidation.assertObject(options, 'options', { 
        operation: 'CoherenceIntegration.registerPatternSystem' 
      });
      
      if (options.weight !== undefined) {
        TypeValidation.assertPositiveNumber(options.weight, 'options.weight', {
          operation: 'CoherenceIntegration.registerPatternSystem'
        });
      }
    }
    
    const weight = options.weight || 1;
    const unregisterFunctions = [];
    
    // Create a coherence-compatible wrapper for the pattern system
    const patternWrapper = {
      patternSystem,
      patterns: [],
      coherenceValues: [],
      
      // Provide a norm() method for the coherence system
      norm: () => {
        try {
          // If we have computed coherence values, use their average
          if (patternWrapper.coherenceValues.length > 0) {
            const avg = patternWrapper.coherenceValues.reduce((sum, val) => sum + val, 0) / 
                        patternWrapper.coherenceValues.length;
            return Math.max(0, Math.min(1, avg));
          }
          return 0.5; // Neutral value if no pattern information
        } catch (error) {
          Prime.Logger.warn(
            'Error computing pattern system norm for coherence tracking',
            {
              operation: 'CoherenceIntegration.patternWrapper.norm',
              error: error.message
            }
          );
          return 0.5; // Fallback to neutral value
        }
      }
    };
    
    // Add methods specific to the pattern system type
    if (patternSystem.constructor.name === 'FiberAlgebraPatternRecognition') {
      // Add analyze method to update coherence when patterns are found
      patternWrapper.analyzeData = function(data, nPatterns = 3) {
        try {
          const result = patternSystem.analyzeData(data, nPatterns);
          patternWrapper.patterns = result.patterns || [];
          
          // Update coherence values from pattern coherence scores
          patternWrapper.coherenceValues = patternWrapper.patterns.map(p => p.coherence || 0);
          
          return result;
        } catch (error) {
          Prime.Logger.warn(
            'Error in pattern analysis during coherence tracking',
            {
              operation: 'CoherenceIntegration.patternWrapper.analyzeData',
              error: error.message
            }
          );
          return { patterns: [], features: [], labels: [], nPatternsFound: 0 };
        }
      };
    } else if (patternSystem.constructor.name === 'SequencePatternRecognition') {
      // Add analyze method to update coherence when patterns are found
      patternWrapper.analyzeSequence = function(sequence, options = {}) {
        try {
          const result = patternSystem.analyzeSequence(sequence, options);
          patternWrapper.patterns = result.patterns || [];
          
          // Update coherence values from pattern coherence scores
          patternWrapper.coherenceValues = patternWrapper.patterns.map(p => p.coherence || 0);
          
          return result;
        } catch (error) {
          Prime.Logger.warn(
            'Error in sequence analysis during coherence tracking',
            {
              operation: 'CoherenceIntegration.patternWrapper.analyzeSequence',
              error: error.message
            }
          );
          return { patterns: [], relationships: [], sequenceLength: 0, coverage: 0 };
        }
      };
    }
    
    // Register with system coherence if available
    if (this.systemCoherenceAvailable) {
      try {
        const unregister = Prime.coherence.systemCoherence.register(patternWrapper, weight);
        unregisterFunctions.push(unregister);
      } catch (error) {
        Prime.Logger.warn(
          'Error registering pattern system with system coherence',
          {
            operation: 'CoherenceIntegration.registerPatternSystem',
            error: error.message
          }
        );
      }
    }
    
    // Add to local tracking
    this.registeredComponents.push({
      component: patternWrapper,
      weight: weight,
      type: 'patternSystem'
    });
    
    // Return a function to unregister this component
    return () => {
      // Call all unregister functions
      unregisterFunctions.forEach(fn => {
        try {
          if (typeof fn === 'function') {
            fn();
          }
        } catch (error) {
          Prime.Logger.warn(
            'Error unregistering component',
            {
              operation: 'CoherenceIntegration.unregister',
              error: error.message
            }
          );
        }
      });
      
      // Remove from local tracking
      const index = this.registeredComponents.findIndex(c => c.component === patternWrapper);
      if (index >= 0) {
        this.registeredComponents.splice(index, 1);
      }
    };
  }
  
  /**
   * Calculate the local coherence of registered components
   * This is a fallback when system coherence tracking is not available
   * 
   * @param {Object} options Calculation options
   * @param {string} options.method Calculation method ('weighted_rms' or 'geometric_mean')
   * @returns {number} The calculated coherence value (0-1)
   */
  calculateLocalCoherence(options = {}) {
    // Validate options
    if (options !== undefined) {
      TypeValidation.assertObject(options, 'options', { 
        operation: 'CoherenceIntegration.calculateLocalCoherence' 
      });
      
      if (options.method !== undefined) {
        TypeValidation.assertString(options.method, 'options.method', {
          operation: 'CoherenceIntegration.calculateLocalCoherence'
        });
      }
    }
    
    const method = options.method || 'weighted_rms';
    
    // If no components are registered, return 0
    if (this.registeredComponents.length === 0) {
      return 0;
    }
    
    // Calculate the coherence values for all components
    const componentValues = this.registeredComponents.map(component => {
      try {
        const norm = component.component.norm();
        return {
          value: norm,
          weight: component.weight
        };
      } catch (error) {
        Prime.Logger.warn(
          'Error calculating component norm',
          {
            operation: 'CoherenceIntegration.calculateLocalCoherence',
            componentType: component.type,
            error: error.message
          }
        );
        return {
          value: 0.5, // Neutral value
          weight: component.weight
        };
      }
    });
    
    // Calculate coherence based on the selected method
    if (method === 'geometric_mean') {
      // Geometric mean of weighted values
      let product = 1;
      let totalWeight = 0;
      
      componentValues.forEach(({ value, weight }) => {
        // Ensure value is positive for geometric mean
        const safeValue = Math.max(1e-6, value);
        product *= Math.pow(safeValue, weight);
        totalWeight += weight;
      });
      
      // Compute the weighted geometric mean
      return Math.pow(product, 1 / Math.max(1e-6, totalWeight));
    } else {
      // Default: weighted RMS (root mean square)
      let weightedSum = 0;
      let totalWeight = 0;
      
      componentValues.forEach(({ value, weight }) => {
        weightedSum += weight * value * value;
        totalWeight += weight;
      });
      
      // Compute the weighted RMS
      return Math.sqrt(weightedSum) / Math.max(1e-6, totalWeight);
    }
  }
  
  /**
   * Get the system coherence value if available
   * Falls back to local coherence calculation if system coherence is not available
   * 
   * @param {Object} options Calculation options
   * @returns {number} The calculated coherence value (0-1)
   */
  getSystemCoherence(options = {}) {
    // If system coherence is available, use it
    if (this.systemCoherenceAvailable && 
        Prime.coherence && 
        Prime.coherence.systemCoherence && 
        typeof Prime.coherence.systemCoherence.calculateGlobalCoherence === 'function') {
      try {
        return Prime.coherence.systemCoherence.calculateGlobalCoherence(options);
      } catch (error) {
        Prime.Logger.warn(
          'Error getting system coherence, falling back to local calculation',
          {
            operation: 'CoherenceIntegration.getSystemCoherence',
            error: error.message
          }
        );
      }
    }
    
    // Fall back to local coherence calculation
    return this.calculateLocalCoherence(options);
  }
  
  /**
   * Optimize all registered components for better coherence
   * 
   * @param {Object} options Optimization options
   * @param {number} options.iterations Number of optimization iterations (default: 1)
   * @returns {number} The coherence value after optimization
   */
  optimizeComponents(options = {}) {
    // Validate options
    if (options !== undefined) {
      TypeValidation.assertObject(options, 'options', { 
        operation: 'CoherenceIntegration.optimizeComponents' 
      });
      
      if (options.iterations !== undefined) {
        TypeValidation.assertPositiveInteger(options.iterations, 'options.iterations', {
          operation: 'CoherenceIntegration.optimizeComponents'
        });
      }
    }
    
    const iterations = options.iterations || 1;
    
    // If system coherence is available, use it for global optimization
    if (this.systemCoherenceAvailable && 
        Prime.coherence && 
        Prime.coherence.systemCoherence && 
        typeof Prime.coherence.systemCoherence.optimizeGlobal === 'function') {
      try {
        // Use the system optimization with the specified number of iterations
        Prime.coherence.systemCoherence.optimizeGlobal({
          iterations: iterations
        });
        
        // Return the global coherence after optimization
        return this.getSystemCoherence();
      } catch (error) {
        Prime.Logger.warn(
          'Error using system optimization, falling back to local optimization',
          {
            operation: 'CoherenceIntegration.optimizeComponents',
            error: error.message
          }
        );
      }
    }
    
    // Fall back to local optimization
    // Optimize components that have an optimize method
    for (let i = 0; i < iterations; i++) {
      for (const component of this.registeredComponents) {
        if (component.component.optimize && typeof component.component.optimize === 'function') {
          try {
            component.component.optimize();
          } catch (error) {
            Prime.Logger.warn(
              'Error optimizing component',
              {
                operation: 'CoherenceIntegration.optimizeComponents',
                componentType: component.type,
                error: error.message
              }
            );
          }
        }
      }
    }
    
    // Return the local coherence after optimization
    return this.calculateLocalCoherence();
  }
}

// Create a coherence integration instance
const integrationInstance = new CoherenceIntegration();

// Export factory functions for cleaner API
const CoherenceIntegrationAPI = {
  // Register a CliffordAlgebraFiber for coherence tracking
  registerFiber: (fiber, options) => {
    return integrationInstance.registerFiber(fiber, options);
  },
  
  // Register a CoherenceGradientDescent for coherence tracking
  registerOptimizer: (optimizer, options) => {
    return integrationInstance.registerOptimizer(optimizer, options);
  },
  
  // Register a pattern recognition system for coherence tracking
  registerPatternSystem: (patternSystem, options) => {
    return integrationInstance.registerPatternSystem(patternSystem, options);
  },
  
  // Get the system coherence value
  getSystemCoherence: (options) => {
    return integrationInstance.getSystemCoherence(options);
  },
  
  // Optimize all registered components
  optimizeComponents: (options) => {
    return integrationInstance.optimizeComponents(options);
  },
  
  // The underlying integration instance for advanced use
  instance: integrationInstance
};

// Export the API and classes
module.exports = {
  CoherenceIntegration,
  integration: CoherenceIntegrationAPI
};