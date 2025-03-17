/**
 * PrimeOS JavaScript Library - Coherence
 * Coherence system and Universal Object Reference (UOR) implementation
 * Version 1.0.0
 */

// Import extended Prime
import { Prime } from './mathematics.js';

(function(Prime) {
  'use strict';
  
  /**
   * Enhanced coherence system with proper mathematical foundation
   */
  const Coherence = {
    /**
     * Calculate inner product between two objects
     * @param {*} a - First object
     * @param {*} b - Second object
     * @param {Object} [options={}] - Options for inner product calculation
     * @returns {*} Inner product result
     * @throws {InvalidOperationError} If inner product cannot be computed
     */
    innerProduct: function(a, b, options = {}) {
      // Handle multivectors (Clifford algebra elements)
      if (Prime.Clifford.isMultivector(a) && Prime.Clifford.isMultivector(b)) {
        // Get the appropriate inner product based on the Clifford algebra
        const metric = options.metric || 'euclidean';
        
        // If both are vectors (grade 1), compute dot product directly
        if (a.components[1] && b.components[1]) {
          // Extract vector components
          const aVec = a.toArray();
          const bVec = b.toArray();
          
          // Compute dot product
          let dotProduct = 0;
          for (let i = 0; i < aVec.length && i < bVec.length; i++) {
            dotProduct += aVec[i] * bVec[i];
          }
          
          // Create a scalar multivector with the dot product
          const result = new Prime.Clifford.create({ dimension: aVec.length }).scalar(dotProduct);
          return result;
        }
        
        // For general multivectors, use geometric inner product
        const rev = b.reverse();
        const product = a.multiply(rev);
        
        // Extract scalar part (grade 0)
        return product.grade(0);
      }
      
      // Handle arrays (vectors)
      if (Prime.Utils.isArray(a) && Prime.Utils.isArray(b)) {
        if (a.length !== b.length) {
          throw new Prime.ValidationError('Arrays must have the same length for inner product', {
            context: { aLength: a.length, bLength: b.length }
          });
        }
        
        const metric = options.metric || 'euclidean';
        
        if (metric === 'euclidean') {
          return a.reduce((sum, val, i) => sum + val * b[i], 0);
        } else if (metric === 'weighted') {
          const weights = options.weights || Array(a.length).fill(1);
          return a.reduce((sum, val, i) => sum + val * b[i] * weights[i], 0);
        } else if (metric === 'cosine') {
          const dotProduct = a.reduce((sum, val, i) => sum + val * b[i], 0);
          const normA = Math.sqrt(a.reduce((sum, val) => sum + val * val, 0));
          const normB = Math.sqrt(b.reduce((sum, val) => sum + val * val, 0));
          return dotProduct / (normA * normB);
        }
      }
      
      // Handle custom objects with their own innerProduct method
      if (a && typeof a.innerProduct === 'function') {
        return a.innerProduct(b, options);
      }
      
      // Handle UOR objects
      if (a && a.reference && a.value && b && b.reference && b.value) {
        // Check if references are compatible
        if (a.reference !== b.reference) {
          // Try to project to a common reference
          try {
            const bProjected = b.projectTo(a.reference);
            return this.innerProduct(a.value, bProjected.value, options);
          } catch (error) {
            throw new Prime.InvalidOperationError('Cannot compute inner product for objects with incompatible references', {
              context: { error: error.message }
            });
          }
        }
        
        // If references are compatible, compute inner product of values
        return this.innerProduct(a.value, b.value, options);
      }
      
      throw new Prime.InvalidOperationError('Cannot compute inner product for the given objects', {
        context: { 
          aType: typeof a,
          bType: typeof b,
          aIsArray: Prime.Utils.isArray(a),
          bIsArray: Prime.Utils.isArray(b) 
        }
      });
    },
    
    /**
     * Calculate coherence norm of an object
     * @param {*} obj - Object to calculate norm for
     * @param {Object} [options={}] - Options for norm calculation
     * @returns {number} Coherence norm
     * @throws {InvalidOperationError} If norm cannot be computed
     */
    norm: function(obj, options = {}) {
      // Handle multivectors
      if (Prime.Clifford.isMultivector(obj)) {
        const normType = options.normType || 'coherence';
        
        if (normType === 'coherence') {
          // For coherence norm, we use a specific form that measures
          // the "self-consistency" of the multivector
          if (typeof obj.coherenceNorm === 'function') {
            return obj.coherenceNorm();
          }
          
          // Default to Euclidean norm if coherenceNorm is not available
          return obj.norm();
        } else if (normType === 'euclidean') {
          return obj.norm();
        }
      }
      
      // Handle arrays (vectors)
      if (Prime.Utils.isArray(obj)) {
        const normType = options.normType || 'euclidean';
        
        if (normType === 'euclidean') {
          return Math.sqrt(obj.reduce((sum, val) => sum + val * val, 0));
        } else if (normType === 'manhattan') {
          return obj.reduce((sum, val) => sum + Math.abs(val), 0);
        } else if (normType === 'max') {
          return Math.max(...obj.map(Math.abs));
        } else if (normType === 'weighted') {
          const weights = options.weights || Array(obj.length).fill(1);
          return Math.sqrt(obj.reduce((sum, val, i) => sum + val * val * weights[i], 0));
        }
      }
      
      // Handle objects with their own norm method
      if (obj && typeof obj.norm === 'function') {
        return obj.norm(options);
      }
      
      // Handle objects with their own coherenceNorm method
      if (obj && typeof obj.coherenceNorm === 'function') {
        return obj.coherenceNorm(options);
      }
      
      // Handle UOR objects
      if (obj && obj.reference && obj.value) {
        return this.norm(obj.value, options);
      }
      
      // Handle constraint objects
      if (obj && Prime.Utils.isArray(obj.constraints)) {
        // Calculate norm based on constraint violations
        let sumSquaredViolations = 0;
        
        for (const constraint of obj.constraints) {
          if (!constraint.check(obj.state || obj.value || obj)) {
            const weight = constraint.weight || 1;
            sumSquaredViolations += weight * weight;
          }
        }
        
        return Math.sqrt(sumSquaredViolations);
      }
      
      throw new Prime.InvalidOperationError('Cannot compute coherence norm for the given object', {
        context: { 
          objType: typeof obj,
          isArray: Prime.Utils.isArray(obj)
        }
      });
    },
    
    /**
     * Check if an object is coherent within a tolerance
     * @param {*} obj - Object to check
     * @param {number} [tolerance=1e-6] - Tolerance for coherence check
     * @returns {boolean} True if object is coherent
     */
    isCoherent: function(obj, tolerance = 1e-6) {
      try {
        const norm = this.norm(obj);
        return norm <= tolerance;
      } catch (error) {
        Prime.Logger.warn('Failed to check coherence:', { error: error.message });
        return false;
      }
    },
    
    /**
     * Optimize an object for coherence
     * @param {*} obj - Object to optimize
     * @param {Object} [constraints={}] - Optimization constraints
     * @returns {*} Optimized object
     */
    optimize: function(obj, constraints = {}) {
      // Extract optimization parameters
      const maxIterations = constraints.maxIterations || 100;
      const learningRate = constraints.learningRate || 0.01;
      const tolerance = constraints.tolerance || 1e-6;
      const method = constraints.method || 'gradient';
      
      // Clone the object to avoid modifying the original
      let current = Prime.Utils.deepClone(obj);
      
      // Track optimization progress
      const progress = {
        initialNorm: this.norm(current),
        iterations: 0,
        finalNorm: null,
        converged: false,
        path: []
      };
      
      // Select optimization method
      if (method === 'gradient') {
        // Gradient descent optimization
        for (let i = 0; i < maxIterations; i++) {
          progress.iterations++;
          
          const norm = this.norm(current);
          progress.path.push(norm);
          
          if (norm <= tolerance) {
            progress.converged = true;
            break;
          }
          
          // Compute gradient (direction of steepest increase in norm)
          const gradient = this._computeGradient(current);
          
          // Update current solution by moving against the gradient
          current = this._updateSolution(current, gradient, learningRate);
        }
      } else if (method === 'genetic') {
        // Genetic algorithm optimization
        current = this._geneticOptimization(current, constraints);
      } else if (method === 'annealing') {
        // Simulated annealing optimization
        current = this._simulatedAnnealing(current, constraints);
      }
      
      // Record final norm and return optimized object
      progress.finalNorm = this.norm(current);
      
      // Attach optimization info to the result
      if (Prime.Utils.isObject(current)) {
        current._optimizationInfo = progress;
      }
      
      return current;
    },
    
    /**
     * Create a coherence constraint
     * @param {Function} predicate - Constraint checking function
     * @param {Object} [options={}] - Constraint options
     * @returns {Object} Constraint object
     */
    createConstraint: function(predicate, options = {}) {
      if (!Prime.Utils.isFunction(predicate)) {
        throw new Prime.ValidationError('Constraint predicate must be a function', {
          context: { providedType: typeof predicate }
        });
      }
      
      return {
        check: predicate,
        weight: options.weight || 1,
        name: options.name || predicate.name || 'anonymous constraint',
        description: options.description || '',
        type: options.type || 'hard', // 'hard' or 'soft' constraint
        repair: options.repair || null // Optional function to repair violations
      };
    },
    
    /**
     * Repair a coherence violation
     * @param {Object} error - Coherence violation error
     * @returns {*} Repaired object
     * @throws {InvalidOperationError} If violation cannot be repaired
     */
    repairViolation: function(error) {
      if (!(error instanceof Prime.CoherenceViolationError)) {
        throw new Prime.InvalidOperationError('Can only repair coherence violations', {
          context: { errorType: error.constructor.name }
        });
      }
      
      // Check if the constraint has a repair function
      if (error.constraint && typeof error.constraint.repair === 'function') {
        return error.constraint.repair(error.object);
      }
      
      // Try to apply generic repair strategies
      if (error.object && Prime.Utils.isObject(error.object)) {
        // If the object has a repair method, use it
        if (typeof error.object.repair === 'function') {
          return error.object.repair(error.constraint);
        }
        
        // Apply global optimization
        return this.optimize(error.object, {
          constraints: [error.constraint],
          maxIterations: 50,
          tolerance: 1e-8
        });
      }
      
      throw new Prime.InvalidOperationError('Cannot repair coherence violation', {
        context: { 
          constraint: error.constraint.name,
          magnitude: error.magnitude
        }
      });
    },
    
    /**
     * Create a coherence-constrained state
     * @param {*} initialValue - Initial state value
     * @param {Array} [constraints=[]] - Coherence constraints
     * @returns {Object} Constrained state object
     */
    createState: function(initialValue, constraints = []) {
      // Validate constraints
      if (!Prime.Utils.isArray(constraints)) {
        throw new Prime.ValidationError('Constraints must be an array', {
          context: { providedType: typeof constraints }
        });
      }
      
      // Create a deep clone of the initial value
      const initialClone = Prime.Utils.deepClone(initialValue);
      
      // Check all constraints on the initial value
      for (const constraint of constraints) {
        if (!constraint.check(initialClone)) {
          if (constraint.type === 'hard') {
            throw new Prime.CoherenceViolationError(
              `Initial state violates hard constraint "${constraint.name}"`,
              constraint,
              1.0,
              { object: initialClone }
            );
          }
          
          // For soft constraints, we'll just log a warning
          Prime.Logger.warn(`Initial state violates soft constraint "${constraint.name}"`);
        }
      }
      
      // Create the coherence-constrained state object
      return {
        // Getters and setters for the value
        _value: initialClone,
        get value() { return Prime.Utils.deepClone(this._value); },
        set value(newValue) { 
          // This setter is intentionally empty - use update() to change values
          Prime.Logger.warn('Cannot directly set value. Use update() method instead.');
        },
        
        // Store constraints
        constraints: [...constraints],
        
        /**
         * Update the state value
         * @param {*} newValue - New value or update function
         * @returns {Object} Updated state object
         * @throws {CoherenceViolationError} If update violates constraints
         */
        update: function(newValue) {
          // Allow update to be a function that transforms the current value
          const updateValue = Prime.Utils.isFunction(newValue) 
            ? newValue(this._value)
            : newValue;
          
          // Create the proposed new state
          const proposed = Prime.Utils.isObject(this._value) && Prime.Utils.isObject(updateValue)
            ? { ...this._value, ...updateValue }
            : updateValue;
          
          // Check all constraints
          for (const constraint of this.constraints) {
            if (!constraint.check(proposed)) {
              if (constraint.type === 'hard') {
                throw new Prime.CoherenceViolationError(
                  `Update violates hard constraint "${constraint.name}"`,
                  constraint,
                  1.0,
                  { object: proposed }
                );
              }
              
              // For soft constraints, we'll just log a warning but continue
              Prime.Logger.warn(`Update violates soft constraint "${constraint.name}"`);
            }
          }
          
          // All constraints satisfied or only soft constraints violated, update the value
          this._value = proposed;
          
          // Publish state update event
          Prime.EventBus.publish('state:updated', {
            previous: this._value,
            current: proposed,
            coherenceNorm: this.coherenceNorm()
          });
          
          return this;
        },
        
        /**
         * Calculate coherence norm of the current state
         * @returns {number} Coherence norm
         */
        coherenceNorm: function() {
          // Compute how well the current state satisfies all constraints
          let normSquared = 0;
          
          for (const constraint of this.constraints) {
            const satisfied = constraint.check(this._value);
            if (!satisfied) {
              const weight = constraint.weight || 1;
              normSquared += weight * weight;
            }
          }
          
          return Math.sqrt(normSquared);
        },
        
        /**
         * Add a new constraint to the state
         * @param {Object} constraint - Constraint to add
         * @returns {Object} Updated state object
         */
        addConstraint: function(constraint) {
          this.constraints.push(constraint);
          return this;
        },
        
        /**
         * Remove a constraint from the state
         * @param {Object|string} constraint - Constraint or constraint name to remove
         * @returns {Object} Updated state object
         */
        removeConstraint: function(constraint) {
          const constraintName = typeof constraint === 'string'
            ? constraint
            : constraint.name;
          
          this.constraints = this.constraints.filter(c => c.name !== constraintName);
          return this;
        },
        
        /**
         * Check if the current state is coherent
         * @param {number} [tolerance=1e-6] - Tolerance for coherence check
         * @returns {boolean} True if state is coherent
         */
        isCoherent: function(tolerance = 1e-6) {
          return this.coherenceNorm() <= tolerance;
        },
        
        /**
         * Reset the state to its initial value
         * @returns {Object} Reset state object
         */
        reset: function() {
          this._value = Prime.Utils.deepClone(initialClone);
          return this;
        }
      };
    },
    
    /**
     * Make a function optimize its result for coherence
     * @param {Function} fn - Function to optimize
     * @param {Object} [options={}] - Optimization options
     * @returns {Function} Optimized function
     */
    optimizable: function(fn, options = {}) {
      if (!Prime.Utils.isFunction(fn)) {
        throw new Prime.ValidationError('Expected a function', {
          context: { providedType: typeof fn }
        });
      }
      
      return function(...args) {
        // Execute the original function
        const result = fn.apply(this, args);
        
        // Optimize the result for coherence
        return Coherence.optimize(result, options);
      };
    },
    
    /**
     * Get optimization statistics for a result
     * @param {*} result - Optimization result
     * @returns {Object} Optimization statistics
     */
    getOptimizationStats: function(result) {
      if (result && result._optimizationInfo) {
        return result._optimizationInfo;
      }
      
      return {
        initialNorm: null,
        iterations: 0,
        finalNorm: null,
        converged: false,
        path: []
      };
    },
    
    /**
     * System-wide coherence tracking and optimization
     */
    systemCoherence: {
      // Components registered for system-wide coherence
      components: [],
      
      /**
       * Register a component for system-wide coherence tracking
       * @param {Object} component - Component to register
       * @param {number} [weight=1] - Component weight
       * @returns {Function} Unregister function
       */
      register: function(component, weight = 1) {
        this.components.push({
          component,
          weight,
          timestamp: Date.now()
        });
        
        // Return a function to unregister this component
        return () => this.unregister(component);
      },
      
      /**
       * Unregister a component from system-wide coherence tracking
       * @param {Object} component - Component to unregister
       * @returns {boolean} Success
       */
      unregister: function(component) {
        const initialLength = this.components.length;
        this.components = this.components.filter(item => item.component !== component);
        return this.components.length < initialLength;
      },
      
      /**
       * Calculate global coherence of all registered components
       * @returns {number} Global coherence norm
       */
      calculateGlobalCoherence: function() {
        if (this.components.length === 0) {
          return 0;
        }
        
        let sumSquaredWeightedNorms = 0;
        let sumWeights = 0;
        
        for (const { component, weight } of this.components) {
          try {
            const norm = Coherence.norm(component);
            sumSquaredWeightedNorms += weight * weight * norm * norm;
            sumWeights += weight;
          } catch (error) {
            Prime.Logger.warn(`Failed to calculate norm for component:`, {
              error: error.message,
              component
            });
          }
        }
        
        return sumWeights === 0 ? 0 : Math.sqrt(sumSquaredWeightedNorms) / sumWeights;
      },
      
      /**
       * Optimize global coherence of all registered components
       * @param {Object} [options={}] - Optimization options
       * @returns {number} Optimized global coherence norm
       */
      optimizeGlobal: function(options = {}) {
        const iterations = options.iterations || 10;
        const components = [...this.components];
        
        // Sort components by weight (descending) to prioritize more important ones
        components.sort((a, b) => b.weight - a.weight);
        
        // Iteratively optimize each component
        for (let i = 0; i < iterations; i++) {
          for (const { component } of components) {
            try {
              Coherence.optimize(component, {
                maxIterations: options.componentIterations || 10,
                tolerance: options.tolerance || 1e-6
              });
            } catch (error) {
              Prime.Logger.warn(`Failed to optimize component:`, {
                error: error.message,
                component
              });
            }
          }
        }
        
        return this.calculateGlobalCoherence();
      },
      
      /**
       * Get components above a certain coherence threshold
       * @param {number} [threshold=0.1] - Coherence threshold
       * @returns {Array} Array of incoherent components
       */
      getIncoherentComponents: function(threshold = 0.1) {
        return this.components
          .map(item => ({
            component: item.component,
            weight: item.weight,
            norm: Coherence.norm(item.component)
          }))
          .filter(item => item.norm > threshold)
          .sort((a, b) => b.norm - a.norm); // Sort by descending norm
      }
    },
    
    /**
     * Compute gradient of the coherence norm
     * @private
     * @param {*} obj - Object to compute gradient for
     * @returns {*} Gradient
     */
    _computeGradient: function(obj) {
      // This is a placeholder for a proper gradient computation
      // The actual implementation would depend on the object type
      
      // For arrays, we can estimate the gradient numerically
      if (Prime.Utils.isArray(obj)) {
        const epsilon = 1e-6;
        const baseNorm = this.norm(obj);
        const gradient = [];
        
        for (let i = 0; i < obj.length; i++) {
          // Compute partial derivative by finite difference
          const perturbed = [...obj];
          perturbed[i] += epsilon;
          const perturbedNorm = this.norm(perturbed);
          
          // Estimate gradient component
          gradient[i] = (perturbedNorm - baseNorm) / epsilon;
        }
        
        return gradient;
      }
      
      // For objects with their own gradient method
      if (obj && typeof obj.gradient === 'function') {
        return obj.gradient();
      }
      
      // For multivectors
      if (Prime.Clifford.isMultivector(obj)) {
        // Placeholder for multivector gradient
        return obj.scale(0); // Zero multivector as placeholder
      }
      
      // Default case: return a zero gradient (no change)
      return obj;
    },
    
    /**
     * Update a solution by moving against the gradient
     * @private
     * @param {*} current - Current solution
     * @param {*} gradient - Gradient
     * @param {number} learningRate - Learning rate
     * @returns {*} Updated solution
     */
    _updateSolution: function(current, gradient, learningRate) {
      // For arrays, move against the gradient
      if (Prime.Utils.isArray(current) && Prime.Utils.isArray(gradient)) {
        return current.map((val, i) => val - learningRate * gradient[i]);
      }
      
      // For multivectors
      if (Prime.Clifford.isMultivector(current) && Prime.Clifford.isMultivector(gradient)) {
        return current.subtract(gradient.scale(learningRate));
      }
      
      // For objects with their own update method
      if (current && typeof current.update === 'function') {
        return current.update(gradient, learningRate);
      }
      
      // Default: return unchanged
      return current;
    },
    
    /**
     * Genetic algorithm optimization
     * @private
     * @param {*} initial - Initial solution
     * @param {Object} options - Optimization options
     * @returns {*} Optimized solution
     */
    _geneticOptimization: function(initial, options) {
      // Placeholder for genetic algorithm implementation
      // In a full implementation, this would generate multiple candidate
      // solutions, evaluate their fitness, and evolve through selection,
      // crossover, and mutation
      
      return initial;
    },
    
    /**
     * Simulated annealing optimization
     * @private
     * @param {*} initial - Initial solution
     * @param {Object} options - Optimization options
     * @returns {*} Optimized solution
     */
    _simulatedAnnealing: function(initial, options) {
      // Placeholder for simulated annealing implementation
      // In a full implementation, this would iteratively explore the
      // solution space, accepting worse solutions with decreasing probability
      // to escape local minima
      
      return initial;
    }
  };

  /**
   * Universal Object Reference (UOR) implementation
   */
  
  /**
   * UOR Reference class
   */
  class UORReference {
    /**
     * Construct a new UOR reference
     * @param {*} manifold - Base manifold
     * @param {*} point - Point in the manifold
     * @param {*} fiber - Fiber at the point
     */
    constructor(manifold, point, fiber) {
      this.manifold = manifold;
      this.point = point;
      this.fiber = fiber;
      
      // Validate the fiber if it's a Clifford algebra
      if (fiber && Prime.Clifford.isAlgebra && Prime.Clifford.isAlgebra(fiber)) {
        // Fiber is valid
      } else if (fiber && typeof fiber !== 'object') {
        throw new Prime.ValidationError('Fiber must be a valid algebraic structure', {
          context: { fiberType: typeof fiber }
        });
      }
    }
    
    /**
     * Create an object at this reference
     * @param {*} value - Value in the fiber
     * @returns {UORObject} New UOR object
     */
    createObject(value) {
      return new UORObject(this, value);
    }
    
    /**
     * Create a section of the fiber bundle
     * @param {Function} valueFunction - Function mapping points to fiber values
     * @returns {Object} Section object
     */
    createSection(valueFunction) {
      if (!Prime.Utils.isFunction(valueFunction)) {
        throw new Prime.ValidationError('Value function must be a function', {
          context: { providedType: typeof valueFunction }
        });
      }
      
      return {
        reference: this,
        valueAt: (point) => {
          const value = valueFunction(point);
          return this.createObject(value);
        }
      };
    }
    
    /**
     * Get a related reference at another point
     * @param {*} newPoint - New point in the manifold
     * @returns {UORReference} New reference
     */
    relatedReference(newPoint) {
      return new UORReference(this.manifold, newPoint, this.fiber);
    }
    
    /**
     * Check if this reference is compatible with another
     * @param {UORReference} other - Other reference
     * @returns {boolean} True if references are compatible
     */
    isCompatibleWith(other) {
      if (!(other instanceof UORReference)) {
        return false;
      }
      
      // Check manifold compatibility
      if (this.manifold !== other.manifold) {
        return false;
      }
      
      // Check fiber compatibility
      if (Prime.Clifford.isAlgebra && Prime.Clifford.isAlgebra(this.fiber) && 
          Prime.Clifford.isAlgebra(other.fiber)) {
        // For Clifford algebras, check dimension and signature
        return this.fiber.dimension === other.fiber.dimension &&
               this.fiber.signature.every((v, i) => v === other.fiber.signature[i]);
      }
      
      // Default to reference equality for other fiber types
      return this.fiber === other.fiber;
    }
    
    /**
     * Convert to string
     * @returns {string} String representation
     */
    toString() {
      return `UORReference(${this.manifold}, ${this.point})`;
    }
  }

  /**
   * UOR Object class
   */
  class UORObject {
    /**
     * Construct a new UOR object
     * @param {UORReference} reference - Reference
     * @param {*} value - Value in the fiber
     */
    constructor(reference, value) {
      if (!(reference instanceof UORReference)) {
        throw new Prime.ValidationError('Reference must be a UORReference', {
          context: { providedType: typeof reference }
        });
      }
      
      this.reference = reference;
      this.value = value;
    }
    
    /**
     * Apply a transformation to this object
     * @param {*} transformation - Transformation to apply
     * @returns {UORObject} Transformed object
     * @throws {InvalidOperationError} If transformation cannot be applied
     */
    transform(transformation) {
      // Apply to multivector
      if (Prime.Clifford.isMultivector && Prime.Clifford.isMultivector(this.value)) {
        if (Prime.Lie.isGroupElement && Prime.Lie.isGroupElement(transformation)) {
          // Apply Lie group transformation to multivector
          const transformed = transformation.apply(this.value);
          return new UORObject(this.reference, transformed);
        }
        
        // Check if transformation is a Clifford algebra element
        if (Prime.Clifford.isMultivector(transformation)) {
          // Apply sandwich transformation: T(a) = g a g^(-1)
          const rev = transformation.reverse();
          const transformed = transformation.multiply(this.value).multiply(rev);
          return new UORObject(this.reference, transformed);
        }
      }
      
      // Apply to array
      if (Prime.Utils.isArray(this.value)) {
        if (Prime.Lie.isGroupElement && Prime.Lie.isGroupElement(transformation)) {
          // Apply Lie group transformation to array
          const transformed = transformation.apply(this.value);
          return new UORObject(this.reference, transformed);
        }
        
        // Check if transformation is a function
        if (Prime.Utils.isFunction(transformation)) {
          // Apply function transformation
          const transformed = transformation(this.value);
          return new UORObject(this.reference, transformed);
        }
      }
      
      // Apply custom transformations
      if (this.value && typeof this.value.transform === 'function') {
        // Use object's own transform method
        const transformed = this.value.transform(transformation);
        return new UORObject(this.reference, transformed);
      }
      
      throw new Prime.InvalidOperationError('Cannot apply transformation to this object', {
        context: { 
          valueType: typeof this.value,
          transformationType: typeof transformation
        }
      });
    }
    
    /**
     * Calculate coherence norm of this object
     * @returns {number} Coherence norm
     */
    coherenceNorm() {
      return Coherence.norm(this.value);
    }
    
    /**
     * Project this object to a different reference
     * @param {UORReference} newReference - New reference
     * @returns {UORObject} Projected object
     * @throws {InvalidOperationError} If projection is not possible
     */
    projectTo(newReference) {
      if (!(newReference instanceof UORReference)) {
        throw new Prime.ValidationError('New reference must be a UORReference', {
          context: { providedType: typeof newReference }
        });
      }
      
      // Check if references are compatible
      if (!this.reference.isCompatibleWith(newReference)) {
        throw new Prime.InvalidOperationError('References are not compatible for projection', {
          context: { 
            sourceReference: this.reference.toString(),
            targetReference: newReference.toString()
          }
        });
      }
      
      // If references are already equal, return this object
      if (this.reference === newReference) {
        return this;
      }
      
      // Handle projection between points in the same manifold
      if (this.reference.manifold === newReference.manifold) {
        // For Clifford algebras, we can use parallel transport if available
        if (Prime.Clifford.isMultivector && Prime.Clifford.isMultivector(this.value)) {
          // In a full implementation, this would use a connection on the fiber bundle
          // For now, we'll use a simple identity transport
          return new UORObject(newReference, this.value);
        }
        
        // For arrays, we can use a simple identity transport
        if (Prime.Utils.isArray(this.value)) {
          return new UORObject(newReference, [...this.value]);
        }
      }
      
      // Default case: simple copy to new reference
      return new UORObject(newReference, Prime.Utils.deepClone(this.value));
    }
    
    /**
     * Convert to string
     * @returns {string} String representation
     */
    toString() {
      const valueString = typeof this.value.toString === 'function'
        ? this.value.toString()
        : `[${typeof this.value}]`;
      
      return `UORObject(${this.reference.toString()}, ${valueString})`;
    }
  }

  /**
   * UOR Fiber Bundle class
   */
  class UORFiberBundle {
    /**
     * Construct a new UOR fiber bundle
     * @param {Object} config - Configuration object
     */
    constructor(config) {
      this.baseManifold = config.baseManifold;
      this.fiber = config.fiber;
      this.structure = config.structure || {};
      this.connection = config.connection || null;
      
      // Validate the fiber
      if (this.fiber && Prime.Clifford.isAlgebra && Prime.Clifford.isAlgebra(this.fiber)) {
        // Fiber is a valid Clifford algebra
      } else if (this.fiber && typeof this.fiber !== 'object') {
        throw new Prime.ValidationError('Fiber must be a valid algebraic structure', {
          context: { fiberType: typeof this.fiber }
        });
      }
    }
    
    /**
     * Create a reference at a point
     * @param {*} point - Point in the base manifold
     * @returns {UORReference} Reference at that point
     */
    createReference(point) {
      return new UORReference(this.baseManifold, point, this.fiber);
    }
    
    /**
     * Create a section of this bundle
     * @param {Function} valueFunction - Function mapping points to fiber values
     * @returns {Object} Section object
     */
    createSection(valueFunction) {
      if (!Prime.Utils.isFunction(valueFunction)) {
        throw new Prime.ValidationError('Value function must be a function', {
          context: { providedType: typeof valueFunction }
        });
      }
      
      return {
        bundle: this,
        valueAt: (point) => {
          const reference = this.createReference(point);
          const value = valueFunction(point);
          return reference.createObject(value);
        }
      };
    }
    
    /**
     * Parallel transport a section along a curve
     * @param {Object} section - Section to transport
     * @param {Array} curve - Curve in the base manifold
     * @returns {Object} Transported section
     */
    parallelTransport(section, curve) {
      if (!Prime.Utils.isArray(curve) || curve.length < 2) {
        throw new Prime.ValidationError('Curve must be an array with at least two points', {
          context: { 
            curveType: typeof curve,
            curveLength: curve ? curve.length : null
          }
        });
      }
      
      // Use connection if available
      if (this.connection && typeof this.connection.transport === 'function') {
        return this.connection.transport(section, curve);
      }
      
      // Default implementation: identity transport
      const startPoint = curve[0];
      const endPoint = curve[curve.length - 1];
      const startValue = section.valueAt(startPoint).value;
      
      return {
        bundle: this,
        valueAt: (point) => {
          if (point === endPoint) {
            const reference = this.createReference(point);
            return reference.createObject(Prime.Utils.deepClone(startValue));
          }
          return section.valueAt(point);
        }
      };
    }
    
    /**
     * Calculate the covariant derivative of a section along a vector
     * @param {Object} section - Section
     * @param {Array} vector - Vector in the base manifold
     * @returns {Object} Derivative section
     */
    covariantDerivative(section, vector) {
      // Use connection if available
      if (this.connection && typeof this.connection.derivative === 'function') {
        return this.connection.derivative(section, vector);
      }
      
      // Default implementation: zero derivative (flat connection)
      return {
        bundle: this,
        valueAt: (point) => {
          const reference = this.createReference(point);
          
          // Return zero element in the fiber
          if (Prime.Clifford.isAlgebra && Prime.Clifford.isAlgebra(this.fiber)) {
            return reference.createObject(this.fiber.scalar(0));
          }
          
          if (Prime.Utils.isArray(section.valueAt(point).value)) {
            // Zero array of the same length
            const zeroArray = Array(section.valueAt(point).value.length).fill(0);
            return reference.createObject(zeroArray);
          }
          
          return reference.createObject(0);
        }
      };
    }
    
    /**
     * Check if this bundle has a flat connection
     * @returns {boolean} True if connection is flat
     */
    isFlat() {
      if (!this.connection) {
        // No connection is treated as flat
        return true;
      }
      
      // Use connection's own method if available
      if (typeof this.connection.isFlat === 'function') {
        return this.connection.isFlat();
      }
      
      // Default: assume not flat
      return false;
    }
    
    /**
     * Convert to string
     * @returns {string} String representation
     */
    toString() {
      return `UORFiberBundle(${this.baseManifold}, ${this.fiber})`;
    }
  }

  // Extend Prime with coherence capabilities
  Prime.coherence = Coherence;
  
  // Extend Prime with UOR capabilities
  Prime.UOR = {
    /**
     * Create a UOR reference
     * @param {Object} config - Configuration object
     * @returns {UORReference} New UOR reference
     */
    createReference: function(config) {
      return new UORReference(
        config.manifold,
        config.point,
        config.fiber
      );
    },
    
    /**
     * Create a UOR fiber bundle
     * @param {Object} config - Configuration object
     * @returns {UORFiberBundle} New UOR fiber bundle
     */
    createFiberBundle: function(config) {
      return new UORFiberBundle(config);
    },
    
    /**
     * Check if an object is a UOR reference
     * @param {*} obj - Object to check
     * @returns {boolean} True if obj is a UOR reference
     */
    isReference: function(obj) {
      return obj instanceof UORReference;
    },
    
    /**
     * Check if an object is a UOR object
     * @param {*} obj - Object to check
     * @returns {boolean} True if obj is a UOR object
     */
    isObject: function(obj) {
      return obj instanceof UORObject;
    },
    
    /**
     * Check if an object is a UOR fiber bundle
     * @param {*} obj - Object to check
     * @returns {boolean} True if obj is a UOR fiber bundle
     */
    isFiberBundle: function(obj) {
      return obj instanceof UORFiberBundle;
    }
  };
  
})(Prime);

// Export extended Prime
export { Prime };

// For CommonJS compatibility
if (typeof module !== 'undefined' && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== 'undefined') {
  window.Prime = Prime;
}
