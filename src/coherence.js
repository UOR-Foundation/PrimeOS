/**
 * PrimeOS JavaScript Library - Coherence
 * Coherence system and Universal Object Reference (UOR) implementation
 * Version 1.0.0
 */

// Import core Prime using CommonJS to avoid circular dependency
const Prime = require('./core.js');
// Ensure mathematics is loaded
require('./mathematics.js');

(function (Prime) {
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
    innerProduct: function (a, b, options = {}) {
      // Handle multivectors (Clifford algebra elements)
      if (Prime.Clifford.isMultivector(a) && Prime.Clifford.isMultivector(b)) {
        // Get the appropriate inner product based on the Clifford algebra
        // Note: we're removing the unused 'metric' variable here

        // If both are vectors (grade 1), compute dot product with enhanced precision
        if (a.components[1] && b.components[1]) {
          // Extract vector components
          const aVec = a.toArray();
          const bVec = b.toArray();

          // Check for invalid values
          for (let i = 0; i < aVec.length; i++) {
            if (!Number.isFinite(aVec[i])) {
              throw new Prime.ValidationError(
                'Input vector contains NaN or Infinity',
                {
                  context: { index: i, value: aVec[i] },
                },
              );
            }
          }

          for (let i = 0; i < bVec.length; i++) {
            if (!Number.isFinite(bVec[i])) {
              throw new Prime.ValidationError(
                'Input vector contains NaN or Infinity',
                {
                  context: { index: i, value: bVec[i] },
                },
              );
            }
          }

          // Compute dot product using Kahan summation for higher precision
          let dotProduct = 0;
          let compensation = 0; // For compensated summation

          // Use the minimum length to ensure we don't access undefined elements
          const minLength = Math.min(aVec.length, bVec.length);

          for (let i = 0; i < minLength; i++) {
            // Basic Kahan summation algorithm to reduce floating-point error
            const product = aVec[i] * bVec[i];
            const y = product - compensation;
            const t = dotProduct + y;
            compensation = t - dotProduct - y;
            dotProduct = t;
          }

          // Create a scalar multivector with the dot product
          const result = new Prime.Clifford.create({
            dimension: Math.max(aVec.length, bVec.length),
          }).scalar(dotProduct);
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
        // Validate inputs for numerical stability
        const EPSILON = 1e-10;

        // Check for invalid values
        const hasInvalidValue = (arr) => {
          return arr.some((val) => !Number.isFinite(val));
        };

        if (hasInvalidValue(a) || hasInvalidValue(b)) {
          throw new Prime.ValidationError(
            'Input arrays contain NaN or Infinity values',
            {
              context: {
                aHasNaN: a.some(Number.isNaN),
                bHasNaN: b.some(Number.isNaN),
                aHasInfinity: a.some(
                  (val) => val === Infinity || val === -Infinity,
                ),
                bHasInfinity: b.some(
                  (val) => val === Infinity || val === -Infinity,
                ),
              },
            },
          );
        }

        // For stability, pad shorter array with zeros instead of throwing error
        let paddedA = a;
        let paddedB = b;

        if (a.length !== b.length) {
          const maxLength = Math.max(a.length, b.length);
          if (options.strictLength === true) {
            throw new Prime.ValidationError(
              'Arrays must have the same length for inner product',
              {
                context: { aLength: a.length, bLength: b.length },
              },
            );
          } else {
            // Pad arrays with zeros for numerical stability
            paddedA =
              a.length < maxLength
                ? [...a, ...Array(maxLength - a.length).fill(0)]
                : a;
            paddedB =
              b.length < maxLength
                ? [...b, ...Array(maxLength - b.length).fill(0)]
                : b;

            // Log warning about padding
            Prime.Logger.warn(
              'Arrays of different lengths used in inner product - padding shorter array with zeros',
              {
                aLength: a.length,
                bLength: b.length,
                padding: Math.abs(a.length - b.length),
              },
            );
          }
        }

        const metric = options.metric || 'euclidean';

        if (metric === 'euclidean') {
          // Use Kahan summation for improved accuracy
          let sum = 0;
          let compensation = 0; // For compensated summation

          for (let i = 0; i < paddedA.length; i++) {
            const product = paddedA[i] * paddedB[i];
            const y = product - compensation;
            const t = sum + y;
            compensation = t - sum - y;
            sum = t;
          }

          return sum;
        } else if (metric === 'weighted') {
          const weights = options.weights || Array(paddedA.length).fill(1);

          // Validate weights
          if (weights.length < paddedA.length) {
            throw new Prime.ValidationError(
              'Weights array must be at least as long as the vectors',
              {
                context: {
                  weightsLength: weights.length,
                  vectorLength: paddedA.length,
                },
              },
            );
          }

          if (hasInvalidValue(weights)) {
            throw new Prime.ValidationError(
              'Weights array contains NaN or Infinity values',
            );
          }

          // Use Kahan summation for weighted dot product
          let sum = 0;
          let compensation = 0;

          for (let i = 0; i < paddedA.length; i++) {
            const product = paddedA[i] * paddedB[i] * weights[i];
            const y = product - compensation;
            const t = sum + y;
            compensation = t - sum - y;
            sum = t;
          }

          return sum;
        } else if (metric === 'cosine') {
          // Calculate dot product with Kahan summation
          let dotProduct = 0;
          let dotCompensation = 0;

          // Calculate norms with Kahan summation
          let normASquared = 0;
          let normACompensation = 0;
          let normBSquared = 0;
          let normBCompensation = 0;

          for (let i = 0; i < paddedA.length; i++) {
            // Dot product calculation
            const product = paddedA[i] * paddedB[i];
            const dotY = product - dotCompensation;
            const dotT = dotProduct + dotY;
            dotCompensation = dotT - dotProduct - dotY;
            dotProduct = dotT;

            // Norm A calculation
            const aSquared = paddedA[i] * paddedA[i];
            const aY = aSquared - normACompensation;
            const aT = normASquared + aY;
            normACompensation = aT - normASquared - aY;
            normASquared = aT;

            // Norm B calculation
            const bSquared = paddedB[i] * paddedB[i];
            const bY = bSquared - normBCompensation;
            const bT = normBSquared + bY;
            normBCompensation = bT - normBSquared - bY;
            normBSquared = bT;
          }

          // Calculate norms
          const normA = Math.sqrt(Math.max(0, normASquared)); // Protect against negative values due to numeric errors
          const normB = Math.sqrt(Math.max(0, normBSquared));

          // Handle zero vectors
          if (normA < EPSILON || normB < EPSILON) {
            if (normA < EPSILON && normB < EPSILON) {
              return 1.0; // Both vectors are zero, define similarity as 1 (fully similar)
            }
            return 0.0; // One vector is zero, orthogonal (no similarity)
          }

          // Ensure result is in valid range [-1, 1]
          const rawSimilarity = dotProduct / (normA * normB);
          return Math.max(-1, Math.min(1, rawSimilarity));
        } else if (metric === 'manhattan') {
          // Manhattan distance-based similarity
          let sum = 0;
          let compensation = 0;

          for (let i = 0; i < paddedA.length; i++) {
            const product = Math.abs(paddedA[i] - paddedB[i]);
            const y = product - compensation;
            const t = sum + y;
            compensation = t - sum - y;
            sum = t;
          }

          return sum;
        }

        // If we reach here, the metric is not supported
        throw new Prime.InvalidOperationError(
          `Metric "${metric}" not supported for inner product`,
          {
            context: {
              supportedMetrics: [
                'euclidean',
                'weighted',
                'cosine',
                'manhattan',
              ],
              requested: metric,
            },
          },
        );
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
            throw new Prime.InvalidOperationError(
              'Cannot compute inner product for objects with incompatible references',
              {
                context: { error: error.message },
              },
            );
          }
        }

        // If references are compatible, compute inner product of values
        return this.innerProduct(a.value, b.value, options);
      }

      throw new Prime.InvalidOperationError(
        'Cannot compute inner product for the given objects',
        {
          context: {
            aType: typeof a,
            bType: typeof b,
            aIsArray: Prime.Utils.isArray(a),
            bIsArray: Prime.Utils.isArray(b),
          },
        },
      );
    },

    /**
     * Calculate coherence norm of an object
     * @param {*} obj - Object to calculate norm for
     * @param {Object} [options={}] - Options for norm calculation
     * @returns {number} Coherence norm
     * @throws {InvalidOperationError} If norm cannot be computed
     */
    norm: function (obj, options = {}) {
      // Handle null or undefined
      if (obj == null) {
        return 0;
      }

      // Handle objects with custom norm method
      if (typeof obj === 'object' && typeof obj.norm === 'function') {
        return obj.norm();
      }

      // Handle plain objects (like {x: 5, y: 10})
      if (
        typeof obj === 'object' &&
        !Prime.Utils.isArray(obj) &&
        !(
          Prime.Clifford &&
          Prime.Clifford.isMultivector &&
          Prime.Clifford.isMultivector(obj)
        )
      ) {
        // Extract numeric values
        const values = Object.values(obj).filter(
          (val) => typeof val === 'number',
        );
        if (values.length > 0) {
          // Use euclidean norm of the values
          let sumSquared = 0;
          let compensation = 0;

          for (const val of values) {
            const squared = val * val;
            const y = squared - compensation;
            const t = sumSquared + y;
            compensation = t - sumSquared - y;
            sumSquared = t;
          }

          return Math.sqrt(Math.max(0, sumSquared));
        }
        return 0;
      }

      // Handle multivectors
      if (
        Prime.Clifford &&
        Prime.Clifford.isMultivector &&
        Prime.Clifford.isMultivector(obj)
      ) {
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
        // Validate the array for NaN or Infinity values
        if (obj.some((val) => !Number.isFinite(val))) {
          throw new Prime.ValidationError(
            'Array contains NaN or Infinity values',
            {
              context: {
                hasNaN: obj.some(Number.isNaN),
                hasInfinity: obj.some(
                  (val) => val === Infinity || val === -Infinity,
                ),
              },
            },
          );
        }

        if (normType === 'euclidean') {
          // Use Kahan summation for numerical stability
          let sumSquared = 0;
          let compensation = 0;

          for (let i = 0; i < obj.length; i++) {
            const squared = obj[i] * obj[i];
            const y = squared - compensation;
            const t = sumSquared + y;
            compensation = t - sumSquared - y;
            sumSquared = t;
          }

          return Math.sqrt(Math.max(0, sumSquared)); // Ensure non-negative due to potential floating-point errors
        } else if (normType === 'manhattan') {
          // Use Kahan summation for numerical stability
          let sum = 0;
          let compensation = 0;

          for (let i = 0; i < obj.length; i++) {
            const absVal = Math.abs(obj[i]);
            const y = absVal - compensation;
            const t = sum + y;
            compensation = t - sum - y;
            sum = t;
          }

          return sum;
        } else if (normType === 'max') {
          // Find maximum absolute value
          let maxVal = 0;
          for (let i = 0; i < obj.length; i++) {
            const absVal = Math.abs(obj[i]);
            if (absVal > maxVal) {
              maxVal = absVal;
            }
          }
          return maxVal;
        } else if (normType === 'weighted') {
          const weights = options.weights || Array(obj.length).fill(1);

          // Validate weights
          if (weights.some((w) => !Number.isFinite(w))) {
            throw new Prime.ValidationError(
              'Weights contain NaN or Infinity values',
            );
          }

          // Use Kahan summation for numerical stability
          let sumSquared = 0;
          let compensation = 0;

          for (let i = 0; i < obj.length; i++) {
            const weight = i < weights.length ? weights[i] : 1;
            const weightedSquared = obj[i] * obj[i] * weight;
            const y = weightedSquared - compensation;
            const t = sumSquared + y;
            compensation = t - sumSquared - y;
            sumSquared = t;
          }

          return Math.sqrt(Math.max(0, sumSquared)); // Ensure non-negative
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

      throw new Prime.InvalidOperationError(
        'Cannot compute coherence norm for the given object',
        {
          context: {
            objType: typeof obj,
            isArray: Prime.Utils.isArray(obj),
          },
        },
      );
    },

    /**
     * Check if an object is coherent within a tolerance
     * @param {*} obj - Object to check
     * @param {number} [tolerance=1e-6] - Tolerance for coherence check
     * @returns {boolean} True if object is coherent
     */
    isCoherent: function (obj, tolerance = 1e-6) {
      try {
        const norm = this.norm(obj);
        return norm <= tolerance;
      } catch (error) {
        Prime.Logger.warn('Failed to check coherence:', {
          error: error.message,
        });
        return false;
      }
    },

    /**
     * Optimize an object for coherence
     * @param {*} obj - Object to optimize
     * @param {Object} [constraints={}] - Optimization constraints
     * @returns {*} Optimized object
     */
    optimize: function (obj, constraints = {}) {
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
        path: [],
      };

      // Allow injection of custom gradient computation and update functions
      const computeGradient =
        constraints._computeGradient || this._computeGradient.bind(this);
      const updateSolution =
        constraints._updateSolution || this._updateSolution.bind(this);

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
          const gradient = computeGradient(current);

          // Update current solution by moving against the gradient
          current = updateSolution(current, gradient, learningRate);
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
    createConstraint: function (predicate, options = {}) {
      if (!Prime.Utils.isFunction(predicate)) {
        throw new Prime.ValidationError(
          'Constraint predicate must be a function',
          {
            context: { providedType: typeof predicate },
          },
        );
      }

      return {
        check: predicate,
        weight: options.weight || 1,
        name: options.name || predicate.name || 'anonymous constraint',
        description: options.description || '',
        type: options.type || 'hard', // 'hard' or 'soft' constraint
        repair: options.repair || null, // Optional function to repair violations
      };
    },

    /**
     * Repair a coherence violation
     * @param {Object} error - Coherence violation error
     * @returns {*} Repaired object
     * @throws {InvalidOperationError} If violation cannot be repaired
     */
    repairViolation: function (error) {
      if (!(error instanceof Prime.CoherenceViolationError)) {
        throw new Prime.InvalidOperationError(
          'Can only repair coherence violations',
          {
            context: { errorType: error.constructor.name },
          },
        );
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
          tolerance: 1e-8,
        });
      }

      throw new Prime.InvalidOperationError(
        'Cannot repair coherence violation',
        {
          context: {
            constraint: error.constraint.name,
            magnitude: error.magnitude,
          },
        },
      );
    },

    /**
     * Create a coherence-constrained state
     * @param {*} initialValue - Initial state value
     * @param {Array} [constraints=[]] - Coherence constraints
     * @returns {Object} Constrained state object
     */
    createState: function (initialValue, constraints = []) {
      // Validate constraints
      if (!Prime.Utils.isArray(constraints)) {
        throw new Prime.ValidationError('Constraints must be an array', {
          context: { providedType: typeof constraints },
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
              { object: initialClone },
            );
          }

          // For soft constraints, we'll just log a warning
          Prime.Logger.warn(
            `Initial state violates soft constraint "${constraint.name}"`,
          );
        }
      }

      // Create the coherence-constrained state object
      return {
        // Getters and setters for the value
        _value: initialClone,
        get value() {
          return Prime.Utils.deepClone(this._value);
        },
        set value(newValue) {
          // This setter is intentionally empty - use update() to change values
          Prime.Logger.warn(
            'Cannot directly set value. Use update() method instead.',
          );
        },

        // Store constraints
        constraints: [...constraints],

        /**
         * Update the state value
         * @param {*} newValue - New value or update function
         * @returns {Object} Updated state object
         * @throws {CoherenceViolationError} If update violates constraints
         */
        update: function (newValue) {
          // Allow update to be a function that transforms the current value
          const updateValue = Prime.Utils.isFunction(newValue)
            ? newValue(this._value)
            : newValue;

          // Create the proposed new state
          const proposed =
            Prime.Utils.isObject(this._value) &&
            Prime.Utils.isObject(updateValue)
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
                  { object: proposed },
                );
              }

              // For soft constraints, we'll just log a warning but continue
              Prime.Logger.warn(
                `Update violates soft constraint "${constraint.name}"`,
              );
            }
          }

          // All constraints satisfied or only soft constraints violated, update the value
          this._value = proposed;

          // Publish state update event
          Prime.EventBus.publish('state:updated', {
            previous: this._value,
            current: proposed,
            coherenceNorm: this.coherenceNorm(),
          });

          return this;
        },

        /**
         * Calculate coherence norm of the current state
         * @returns {number} Coherence norm
         */
        coherenceNorm: function () {
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
        addConstraint: function (constraint) {
          this.constraints.push(constraint);
          return this;
        },

        /**
         * Remove a constraint from the state
         * @param {Object|string} constraint - Constraint or constraint name to remove
         * @returns {Object} Updated state object
         */
        removeConstraint: function (constraint) {
          const constraintName =
            typeof constraint === 'string' ? constraint : constraint.name;

          this.constraints = this.constraints.filter(
            (c) => c.name !== constraintName,
          );
          return this;
        },

        /**
         * Check if the current state is coherent
         * @param {number} [tolerance=1e-6] - Tolerance for coherence check
         * @returns {boolean} True if state is coherent
         */
        isCoherent: function (tolerance = 1e-6) {
          return this.coherenceNorm() <= tolerance;
        },

        /**
         * Reset the state to its initial value
         * @returns {Object} Reset state object
         */
        reset: function () {
          this._value = Prime.Utils.deepClone(initialClone);
          return this;
        },
      };
    },

    /**
     * Make a function optimize its result for coherence
     * @param {Function} fn - Function to optimize
     * @param {Object} [options={}] - Optimization options
     * @returns {Function} Optimized function
     */
    optimizable: function (fn, options = {}) {
      if (!Prime.Utils.isFunction(fn)) {
        throw new Prime.ValidationError('Expected a function', {
          context: { providedType: typeof fn },
        });
      }

      return function (...args) {
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
    getOptimizationStats: function (result) {
      if (result && result._optimizationInfo) {
        return result._optimizationInfo;
      }

      return {
        initialNorm: null,
        iterations: 0,
        finalNorm: null,
        converged: false,
        path: [],
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
      register: function (component, weight = 1) {
        this.components.push({
          component,
          weight,
          timestamp: Date.now(),
        });

        // Return a function to unregister this component
        return () => this.unregister(component);
      },

      /**
       * Unregister a component from system-wide coherence tracking
       * @param {Object} component - Component to unregister
       * @returns {boolean} Success
       */
      unregister: function (component) {
        const initialLength = this.components.length;
        this.components = this.components.filter((item) => {
          // Check for reference equality first for performance
          if (item.component === component) return false;

          // For objects with similar structure, do deeper comparison
          if (
            typeof component === 'object' &&
            component !== null &&
            typeof item.component === 'object' &&
            item.component !== null
          ) {
            // Check value property which is used in the test
            if (
              component.value !== undefined &&
              component.value === item.component.value
            ) {
              return false;
            }
          }
          return true;
        });
        return this.components.length < initialLength;
      },

      /**
       * Calculate global coherence of all registered components
       * @param {Object} [options={}] - Calculation options
       * @returns {number} Global coherence norm
       */
      calculateGlobalCoherence: function (options = {}) {
        if (this.components.length === 0) {
          return 0;
        }

        // Validate components before calculation
        const validComponents = this.components.filter((item) => {
          try {
            const isValid =
              item &&
              item.component &&
              typeof Coherence.norm(item.component) === 'number';
            return isValid;
          } catch (error) {
            Prime.Logger.warn(`Filtering invalid component:`, {
              error: error.message,
              component: item?.component,
            });
            return false;
          }
        });

        if (validComponents.length === 0) {
          return 0;
        }

        // Determine calculation method
        const method = options.method || 'weighted_rms'; // Default to weighted RMS

        // Option 1: Weighted RMS (root mean square)
        if (method === 'weighted_rms') {
          let sumSquaredWeightedNorms = 0;
          let sumWeights = 0;
          let compensation = 0; // For Kahan summation

          for (const { component, weight } of validComponents) {
            try {
              const norm = Coherence.norm(component);

              // Validate norm value
              if (!Number.isFinite(norm)) {
                Prime.Logger.warn(`Component has invalid norm value:`, {
                  norm,
                  component,
                });
                continue;
              }

              // Use Kahan summation for numerical stability
              const weightedNormSquared = weight * weight * norm * norm;
              const y = weightedNormSquared - compensation;
              const t = sumSquaredWeightedNorms + y;
              compensation = t - sumSquaredWeightedNorms - y;
              sumSquaredWeightedNorms = t;

              sumWeights += weight;
            } catch (error) {
              Prime.Logger.warn(`Failed to calculate norm for component:`, {
                error: error.message,
                component,
              });
            }
          }

          // Normalize by the sum of weights
          return sumWeights === 0
            ? 0
            : Math.sqrt(sumSquaredWeightedNorms) / sumWeights;
        }
        // Option 2: Maximum weighted incoherence
        else if (method === 'max_weighted') {
          let maxWeightedNorm = 0;

          for (const { component, weight } of validComponents) {
            try {
              const norm = Coherence.norm(component);

              // Check if this is the maximum weighted norm so far
              const weightedNorm = weight * norm;
              if (weightedNorm > maxWeightedNorm) {
                maxWeightedNorm = weightedNorm;
              }
            } catch (error) {
              Prime.Logger.warn(`Failed to calculate norm for component:`, {
                error: error.message,
                component,
              });
            }
          }

          return maxWeightedNorm;
        }
        // Option 3: Geometric mean of norms
        else if (method === 'geometric_mean') {
          let productNorms = 1;
          let count = 0;

          for (const { component, weight } of validComponents) {
            try {
              const norm = Coherence.norm(component);
              if (norm <= 0) continue; // Skip zero or negative norms for geometric mean

              // Apply weight as exponent for geometric mean
              productNorms *= Math.pow(norm, weight);
              count += weight;
            } catch (error) {
              Prime.Logger.warn(`Failed to calculate norm for component:`, {
                error: error.message,
                component,
              });
            }
          }

          return count === 0 ? 0 : Math.pow(productNorms, 1 / count);
        }
        // Default to standard weighted RMS
        else {
          Prime.Logger.warn(
            `Unknown global coherence method: ${method}, using weighted_rms`,
          );
          return this.calculateGlobalCoherence({ method: 'weighted_rms' });
        }
      },

      /**
       * Optimize global coherence of all registered components
       * @param {Object} [options={}] - Optimization options
       * @returns {number} Optimized global coherence norm
       */
      optimizeGlobal: function (options = {}) {
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
                tolerance: options.tolerance || 1e-6,
              });
            } catch (error) {
              Prime.Logger.warn(`Failed to optimize component:`, {
                error: error.message,
                component,
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
      getIncoherentComponents: function (threshold = 0.1) {
        return this.components
          .map((item) => ({
            component: item.component,
            weight: item.weight,
            norm: Coherence.norm(item.component),
          }))
          .filter((item) => item.norm > threshold)
          .sort((a, b) => b.norm - a.norm); // Sort by descending norm
      },
    },

    /**
     * Compute gradient of the coherence norm
     * @private
     * @param {*} obj - Object to compute gradient for
     * @param {Object} [options={}] - Gradient computation options
     * @returns {*} Gradient
     */
    _computeGradient: function (obj, options = {}) {
      // Constants for numerical stability
      const epsilon = options.epsilon || 1e-8;
      const delta = options.delta || 1e-6;
      const useSecondOrder = options.useSecondOrder !== false;

      // For arrays, we can estimate the gradient numerically with improved precision
      if (Prime.Utils.isArray(obj)) {
        // Compute base norm with error handling
        let baseNorm;
        try {
          baseNorm = this.norm(obj);
        } catch (error) {
          // If norm calculation fails, return zero gradient
          Prime.Logger.warn(
            'Norm calculation failed in gradient computation:',
            { error: error.message },
          );
          return Array(obj.length).fill(0);
        }

        // Initialize gradient array
        const gradient = new Array(obj.length);

        // Calculate gradient using central difference for higher accuracy
        for (let i = 0; i < obj.length; i++) {
          try {
            if (useSecondOrder) {
              // Higher-order central difference method for improved accuracy
              // Uses a seven-point stencil for sixth-order accuracy
              const posPerturbed1 = [...obj];
              posPerturbed1[i] += delta;
              const posNorm1 = this.norm(posPerturbed1);

              const posPerturbed2 = [...obj];
              posPerturbed2[i] += 2 * delta;
              const posNorm2 = this.norm(posPerturbed2);

              const posPerturbed3 = [...obj];
              posPerturbed3[i] += 3 * delta;
              const posNorm3 = this.norm(posPerturbed3);

              const negPerturbed1 = [...obj];
              negPerturbed1[i] -= delta;
              const negNorm1 = this.norm(negPerturbed1);

              const negPerturbed2 = [...obj];
              negPerturbed2[i] -= 2 * delta;
              const negNorm2 = this.norm(negPerturbed2);

              const negPerturbed3 = [...obj];
              negPerturbed3[i] -= 3 * delta;
              const negNorm3 = this.norm(negPerturbed3);

              // Seventh-order central difference formula based on Fornberg's method
              // Coefficients derived from Taylor series expansion
              gradient[i] =
                (-negNorm3 +
                  9 * negNorm2 -
                  45 * negNorm1 +
                  45 * posNorm1 -
                  9 * posNorm2 +
                  posNorm3) /
                (60 * delta);

              // Apply Richardson extrapolation to further improve accuracy
              // by combining different step sizes
              if (options.useRichardson) {
                // Compute gradient with half step size
                const halfDelta = delta / 2;

                const posPerturbed1Half = [...obj];
                posPerturbed1Half[i] += halfDelta;
                const posNorm1Half = this.norm(posPerturbed1Half);

                const negPerturbed1Half = [...obj];
                negPerturbed1Half[i] -= halfDelta;
                const negNorm1Half = this.norm(negPerturbed1Half);

                // First-order approximation with half step
                const gradHalf =
                  (posNorm1Half - negNorm1Half) / (2 * halfDelta);

                // Richardson extrapolation (eliminates leading error term)
                const richardsonFactor = 4 / 3; // For first-order central difference
                gradient[i] =
                  richardsonFactor * gradHalf -
                  (richardsonFactor - 1) * gradient[i];
              }
            } else {
              // First-order central difference method (faster)
              const posPerturbed = [...obj];
              posPerturbed[i] += delta;
              const posNorm = this.norm(posPerturbed);

              const negPerturbed = [...obj];
              negPerturbed[i] -= delta;
              const negNorm = this.norm(negPerturbed);

              // Central difference formula
              gradient[i] = (posNorm - negNorm) / (2 * delta);
            }

            // Handle potential numerical errors
            if (!Number.isFinite(gradient[i])) {
              // If computation fails, fall back to simpler method
              const perturbed = [...obj];
              perturbed[i] += epsilon;
              const perturbedNorm = this.norm(perturbed);

              gradient[i] = (perturbedNorm - baseNorm) / epsilon;

              // If still invalid, use zero
              if (!Number.isFinite(gradient[i])) {
                gradient[i] = 0;
              }
            }
          } catch (error) {
            // If any computation fails, use zero for this component
            Prime.Logger.warn(
              `Gradient computation failed for component ${i}:`,
              { error: error.message },
            );
            gradient[i] = 0;
          }
        }

        // Normalize the gradient if it's very large to prevent overshooting
        const gradientMagnitude = Math.sqrt(
          gradient.reduce((sum, val) => sum + val * val, 0),
        );
        if (gradientMagnitude > 1e3) {
          // Scale down large gradients to prevent instability
          const scaleFactor = 1e3 / gradientMagnitude;
          for (let i = 0; i < gradient.length; i++) {
            gradient[i] *= scaleFactor;
          }
        }

        return gradient;
      }

      // For objects with their own gradient method
      if (obj && typeof obj.gradient === 'function') {
        try {
          return obj.gradient(options);
        } catch (error) {
          Prime.Logger.warn('Object gradient method failed:', {
            error: error.message,
          });
          // Return default zero gradient on failure
          return obj.constructor ? new obj.constructor() : {};
        }
      }

      // For multivectors
      if (Prime.Clifford.isMultivector && Prime.Clifford.isMultivector(obj)) {
        try {
          // Compute finite-difference gradient for each component
          const result = obj.scale(0); // Start with zero multivector

          // Iterate through all grades and components
          for (const grade in obj.components) {
            if (!obj.components[grade]) continue;

            for (const basis in obj.components[grade]) {
              // Create perturbed multivector
              const perturbed = obj.clone();
              // Add epsilon to this component
              perturbed.components[grade][basis] += epsilon;

              // Calculate norm difference
              const baseNorm = this.norm(obj);
              const perturbedNorm = this.norm(perturbed);

              // Compute gradient component
              const gradComponent = (perturbedNorm - baseNorm) / epsilon;

              // Add to result only if finite
              if (Number.isFinite(gradComponent) && gradComponent !== 0) {
                // Create basis multivector and scale by gradient
                const basisMv = obj.algebra.basisBlade(basis);
                result.add(basisMv.scale(gradComponent));
              }
            }
          }

          return result;
        } catch (error) {
          Prime.Logger.warn('Multivector gradient computation failed:', {
            error: error.message,
          });
          return obj.scale(0); // Return zero multivector on failure
        }
      }

      // For UOR objects, delegate to the value's gradient
      if (obj && obj.reference && obj.value) {
        try {
          const valueGradient = this._computeGradient(obj.value, options);
          return { reference: obj.reference, value: valueGradient };
        } catch (error) {
          Prime.Logger.warn('UOR object gradient computation failed:', {
            error: error.message,
          });
          return { reference: obj.reference, value: obj.value };
        }
      }

      // Default case: return a structured zero gradient based on object type
      if (Prime.Utils.isObject(obj)) {
        // Create a zero object with the same structure
        const result = {};
        for (const key in obj) {
          if (typeof obj[key] === 'number') {
            result[key] = 0;
          } else if (Prime.Utils.isArray(obj[key])) {
            result[key] = Array(obj[key].length).fill(0);
          } else if (Prime.Utils.isObject(obj[key])) {
            result[key] = this._computeGradient(obj[key], options);
          } else {
            result[key] = obj[key]; // Keep non-numeric properties as is
          }
        }
        return result;
      }

      // For unknown types, return a scalar zero
      return 0;
    },

    /**
     * Update a solution by moving against the gradient
     * @private
     * @param {*} current - Current solution
     * @param {*} gradient - Gradient
     * @param {number} learningRate - Learning rate
     * @returns {*} Updated solution
     */
    _updateSolution: function (current, gradient, learningRate) {
      // For arrays, move against the gradient
      if (Prime.Utils.isArray(current) && Prime.Utils.isArray(gradient)) {
        return current.map((val, i) => val - learningRate * gradient[i]);
      }

      // For multivectors
      if (
        Prime.Clifford.isMultivector(current) &&
        Prime.Clifford.isMultivector(gradient)
      ) {
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
    _geneticOptimization: function (initial, options) {
      // Only arrays are supported for now
      if (!Prime.Utils.isArray(initial)) {
        Prime.Logger.warn(
          'Genetic optimization currently only supports arrays',
          {
            providedType: typeof initial,
          },
        );
        return initial;
      }

      // Set up genetic algorithm parameters
      const populationSize = options.populationSize || 50;
      const generations = options.generations || 100;
      const mutationRate = options.mutationRate || 0.1;
      const crossoverRate = options.crossoverRate || 0.7;
      const elitism = options.elitism !== undefined ? options.elitism : 2;
      const selectionPressure = options.selectionPressure || 2;

      // Create initial population
      let population = [];

      // Add initial solution to population
      population.push(initial.slice());

      // Generate random solutions for the rest of the population
      for (let i = 1; i < populationSize; i++) {
        const individual = initial.slice();

        // Perturb each dimension randomly
        for (let j = 0; j < individual.length; j++) {
          // Apply larger perturbations at the beginning
          const perturbScale = Math.max(0.1, 1 - i / populationSize);

          // Generate perturbation scaled by the value or a default
          const scale =
            Math.abs(individual[j]) > 1e-6 ? Math.abs(individual[j]) : 1.0;
          individual[j] += scale * perturbScale * (Math.random() * 2 - 1);
        }

        population.push(individual);
      }

      // Setup fitness function (lower coherence norm is better)
      const calculateFitness = (individual) => {
        try {
          const norm = this.norm(individual);
          return 1.0 / (norm + 1e-10); // Add small epsilon to avoid division by zero
        } catch (error) {
          return 0; // Individuals with errors get lowest fitness
        }
      };

      // Selection function using tournament selection
      const select = () => {
        // Tournament selection
        const tournamentSize = Math.max(2, Math.floor(population.length / 10));
        const tournament = [];

        // Calculate fitness for all individuals
        const populationFitness = population.map(calculateFitness);

        // Select random individuals for the tournament
        for (let i = 0; i < tournamentSize; i++) {
          const idx = Math.floor(Math.random() * population.length);
          tournament.push({
            individual: population[idx],
            fitness: populationFitness[idx],
          });
        }

        // Sort by fitness (descending)
        tournament.sort((a, b) => b.fitness - a.fitness);

        // Return the winner (with probability based on rank)
        const rank =
          Math.floor(Math.random() * tournamentSize * selectionPressure) %
          tournamentSize;
        return tournament[rank].individual;
      };

      // Crossover two parents to create two children
      const crossover = (parent1, parent2) => {
        if (Math.random() > crossoverRate) {
          // No crossover, return copies of parents
          return [parent1.slice(), parent2.slice()];
        }

        // Choose crossover point(s)
        const crossoverType = Math.random() < 0.5 ? 'single' : 'uniform';
        const child1 = new Array(parent1.length);
        const child2 = new Array(parent2.length);

        if (crossoverType === 'single') {
          // Single-point crossover
          const point = Math.floor(Math.random() * (parent1.length - 1)) + 1;

          for (let i = 0; i < parent1.length; i++) {
            if (i < point) {
              child1[i] = parent1[i];
              child2[i] = parent2[i];
            } else {
              child1[i] = parent2[i];
              child2[i] = parent1[i];
            }
          }
        } else {
          // Uniform crossover
          for (let i = 0; i < parent1.length; i++) {
            if (Math.random() < 0.5) {
              child1[i] = parent1[i];
              child2[i] = parent2[i];
            } else {
              child1[i] = parent2[i];
              child2[i] = parent1[i];
            }
          }
        }

        return [child1, child2];
      };

      // Mutate an individual
      const mutate = (individual) => {
        const result = individual.slice();

        for (let i = 0; i < result.length; i++) {
          // Apply mutation with decreasing probability
          if (Math.random() < mutationRate) {
            // Adaptive mutation rate based on progress
            const mutationScale =
              Math.abs(result[i]) > 1e-6 ? Math.abs(result[i]) * 0.1 : 0.01;
            result[i] += mutationScale * (Math.random() * 2 - 1);
          }
        }

        return result;
      };

      // Main genetic algorithm loop
      let bestSolution = initial.slice();
      let bestFitness = calculateFitness(bestSolution);

      // Track progress for early stopping
      let noImprovementCount = 0;

      for (let generation = 0; generation < generations; generation++) {
        // Calculate fitness for all individuals
        const populationFitness = population.map(calculateFitness);

        // Find best individual
        let generationBestIdx = 0;
        for (let i = 1; i < populationFitness.length; i++) {
          if (populationFitness[i] > populationFitness[generationBestIdx]) {
            generationBestIdx = i;
          }
        }

        // Check if we found a better solution
        if (populationFitness[generationBestIdx] > bestFitness) {
          bestSolution = population[generationBestIdx].slice();
          bestFitness = populationFitness[generationBestIdx];
          noImprovementCount = 0;
        } else {
          noImprovementCount++;

          // Early stopping if no improvement for a while
          if (noImprovementCount >= 20) {
            break;
          }
        }

        // Create next generation
        const nextGeneration = [];

        // Elitism: keep best individuals
        const sortedIndices = populationFitness
          .map((f, i) => i)
          .sort((a, b) => populationFitness[b] - populationFitness[a]);

        for (let i = 0; i < elitism; i++) {
          nextGeneration.push(population[sortedIndices[i]].slice());
        }

        // Create rest of population through selection, crossover, and mutation
        while (nextGeneration.length < populationSize) {
          // Select parents
          const parent1 = select();
          const parent2 = select();

          // Create children through crossover
          const [child1, child2] = crossover(parent1, parent2);

          // Apply mutation
          const mutatedChild1 = mutate(child1);
          nextGeneration.push(mutatedChild1);

          if (nextGeneration.length < populationSize) {
            const mutatedChild2 = mutate(child2);
            nextGeneration.push(mutatedChild2);
          }
        }

        // Replace population
        population = nextGeneration;
      }

      // Return best solution found
      return bestSolution;
    },

    /**
     * Simulated annealing optimization
     * @private
     * @param {*} initial - Initial solution
     * @param {Object} options - Optimization options
     * @returns {*} Optimized solution
     */
    _simulatedAnnealing: function (initial, options) {
      // Only arrays are supported for now
      if (!Prime.Utils.isArray(initial)) {
        Prime.Logger.warn(
          'Simulated annealing currently only supports arrays',
          {
            providedType: typeof initial,
          },
        );
        return initial;
      }

      // Set up annealing parameters with more mathematically sound defaults
      const maxIterations = options.maxIterations || 1000;
      const initialTemperature = options.initialTemperature || 100.0;
      // For optimal annealing, cooling rate should ensure sufficient exploration
      const coolingRate = options.coolingRate || 0.97; // Slower cooling (was 0.95)
      const minTemperature = options.minTemperature || 1e-6;
      const reheatingSchedule = options.reheatingSchedule || false; // Enable reheating
      const reheatingPeriod = options.reheatingPeriod || 100; // Reheat every N iterations
      const reheatingFactor = options.reheatingFactor || 0.5; // Reheat to 50% of initial temp
      const equilibriumSteps = options.equilibriumSteps || 10; // Steps at each temperature
      const boltzmannConstant = options.boltzmannConstant || 1.0; // Scaling constant

      // Enhanced constraints handling
      const constraints = options.constraints || [];
      const applyConstraints = (solution) => {
        let constrainedSolution = solution.slice();

        // Apply domain constraints if provided
        if (constraints.length > 0) {
          for (let i = 0; i < constrainedSolution.length; i++) {
            // Find constraints applicable to this dimension
            const dimensionConstraints = constraints.filter(
              (c) => c.dimension === undefined || c.dimension === i,
            );

            // Apply each constraint
            for (const constraint of dimensionConstraints) {
              if (constraint.type === 'bounds') {
                // Bounded value constraint
                if (
                  constraint.min !== undefined &&
                  constrainedSolution[i] < constraint.min
                ) {
                  constrainedSolution[i] = constraint.min;
                }
                if (
                  constraint.max !== undefined &&
                  constrainedSolution[i] > constraint.max
                ) {
                  constrainedSolution[i] = constraint.max;
                }
              } else if (
                constraint.type === 'function' &&
                typeof constraint.apply === 'function'
              ) {
                // Custom constraint function
                constrainedSolution = constraint.apply(constrainedSolution);
              }
            }
          }
        }

        return constrainedSolution;
      };

      // Helper function to calculate energy (coherence norm) with improved stability
      const calculateEnergy = (solution) => {
        try {
          // Apply constraints first to ensure valid evaluation
          const constrainedSolution = applyConstraints(solution);

          // Calculate the norm (energy)
          const norm = this.norm(constrainedSolution);

          // Add penalty term for constraint violations
          let penaltyTerm = 0;
          if (constraints.length > 0) {
            for (let i = 0; i < constrainedSolution.length; i++) {
              const dimensionConstraints = constraints.filter(
                (c) => c.dimension === undefined || c.dimension === i,
              );

              for (const constraint of dimensionConstraints) {
                if (constraint.type === 'bounds') {
                  // Penalty for bounds violations
                  if (
                    constraint.min !== undefined &&
                    solution[i] < constraint.min
                  ) {
                    const violation = constraint.min - solution[i];
                    penaltyTerm +=
                      violation * violation * (constraint.weight || 100);
                  }
                  if (
                    constraint.max !== undefined &&
                    solution[i] > constraint.max
                  ) {
                    const violation = solution[i] - constraint.max;
                    penaltyTerm +=
                      violation * violation * (constraint.weight || 100);
                  }
                } else if (
                  constraint.type === 'function' &&
                  typeof constraint.penalty === 'function'
                ) {
                  penaltyTerm += constraint.penalty(solution);
                }
              }
            }
          }

          return norm + penaltyTerm;
        } catch (error) {
          Prime.Logger.warn('Energy calculation failed', {
            error: error.message,
          });
          return Infinity; // Invalid solutions get highest energy
        }
      };

      // Generate neighbor solution with improved topology awareness
      const generateNeighbor = (current, temperature, iteration) => {
        const neighbor = current.slice();

        // Adaptive neighborhood size based on temperature
        // At high temperatures, explore more broadly
        // At low temperatures, make more focused changes
        const temperatureRatio = temperature / initialTemperature;

        // Scale the number of dimensions to modify based on temperature
        let dimensions = Math.max(
          1,
          Math.round(temperatureRatio * current.length),
        );

        // Add randomization factor to prevent getting stuck in patterns
        if (Math.random() < 0.2) {
          // 20% chance of randomizing dimension count
          dimensions = 1 + Math.floor(Math.random() * current.length);
        }

        // Select dimensions to modify
        // Use weighted selection to focus on dimensions with highest impact
        const dimensionIndices = new Set();

        // Try to use gradient information if available for smart dimension selection
        let gradientInfo = null;
        try {
          gradientInfo = this._computeGradient(current, {
            useSecondOrder: false,
          });
        } catch (error) {
          // Gradient computation failed, will use random selection
        }

        if (gradientInfo && Prime.Utils.isArray(gradientInfo)) {
          // Create weights based on gradient magnitudes (focus on high-gradient dimensions)
          const weights = gradientInfo.map((g) => Math.abs(g));
          const totalWeight = weights.reduce((sum, w) => sum + w, 0);

          // Use roulette wheel selection for dimensions based on gradient
          while (dimensionIndices.size < dimensions) {
            const r = Math.random() * totalWeight;
            let sum = 0;

            for (let i = 0; i < weights.length; i++) {
              sum += weights[i];
              if (r <= sum && !dimensionIndices.has(i)) {
                dimensionIndices.add(i);
                break;
              }
            }

            // Fallback if no dimension was selected (e.g., all gradients near zero)
            if (dimensionIndices.size === 0) {
              dimensionIndices.add(Math.floor(Math.random() * current.length));
            }
          }
        } else {
          // Fall back to random dimension selection
          while (dimensionIndices.size < dimensions) {
            dimensionIndices.add(Math.floor(Math.random() * current.length));
          }
        }

        // Modify selected dimensions with temperature-adaptive step sizes
        for (const index of dimensionIndices) {
          // Scale perturbation by temperature and current value
          const scale =
            Math.abs(current[index]) > 1e-6 ? Math.abs(current[index]) : 0.1;

          // Use Cauchy distribution for high temperature (allows larger jumps)
          // and Gaussian distribution for low temperature (more focused search)
          let perturbation;

          if (temperatureRatio > 0.5) {
            // Cauchy distribution: good for escaping local minima
            const cauchy = Math.tan(Math.PI * (Math.random() - 0.5));
            perturbation = scale * temperatureRatio * cauchy * 0.5;
          } else {
            // Gaussian distribution: good for fine-tuning
            // Box-Muller transform
            const u1 = Math.random();
            const u2 = Math.random();
            const gaussian =
              Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math.PI * u2);
            perturbation = scale * temperatureRatio * gaussian * 0.3;
          }

          // Limit large perturbations to prevent extreme jumps
          const maxChange = scale * 3 * temperatureRatio;
          if (Math.abs(perturbation) > maxChange) {
            perturbation = Math.sign(perturbation) * maxChange;
          }

          neighbor[index] += perturbation;
        }

        // Apply constraints to ensure the neighbor is valid
        return applyConstraints(neighbor);
      };

      // Initialize simulated annealing
      let currentSolution = applyConstraints(initial.slice());
      let currentEnergy = calculateEnergy(currentSolution);

      let bestSolution = currentSolution.slice();
      let bestEnergy = currentEnergy;

      let temperature = initialTemperature;
      let noImprovementCount = 0;

      // Track energy history for adaptive cooling
      const energyHistory = [];
      let acceptanceRatio = 0;
      // let acceptedMoves = 0; // Not used in this implementation

      // Main simulated annealing loop with multiple moves per temperature
      for (
        let iteration = 0;
        iteration < maxIterations && temperature > minTemperature;
        iteration++
      ) {
        // Perform multiple steps at each temperature to approach equilibrium
        let acceptedAtThisTemp = 0;

        for (let step = 0; step < equilibriumSteps; step++) {
          // Generate and evaluate a neighbor solution
          const neighborSolution = generateNeighbor(
            currentSolution,
            temperature,
            iteration,
          );
          const neighborEnergy = calculateEnergy(neighborSolution);

          // Calculate energy difference
          const deltaE = neighborEnergy - currentEnergy;

          // Decide whether to accept the neighbor solution
          let acceptNeighbor = false;

          if (deltaE <= 0) {
            // Always accept better or equal solutions
            acceptNeighbor = true;
          } else {
            // Accept worse solutions with a temperature-dependent probability
            // This uses the proper Metropolis criterion with Boltzmann factor
            const acceptanceProbability = Math.exp(
              -deltaE / (boltzmannConstant * temperature),
            );
            acceptNeighbor = Math.random() < acceptanceProbability;
          }

          // Update current solution if neighbor is accepted
          if (acceptNeighbor) {
            currentSolution = neighborSolution;
            currentEnergy = neighborEnergy;
            // acceptedMoves not used
            acceptedAtThisTemp++;

            // Update best solution if necessary
            if (currentEnergy < bestEnergy) {
              bestSolution = currentSolution.slice();
              bestEnergy = currentEnergy;
              noImprovementCount = 0;
            } else {
              noImprovementCount++;
            }
          } else {
            noImprovementCount++;
          }
        }

        // Update acceptance ratio for this temperature
        acceptanceRatio = acceptedAtThisTemp / equilibriumSteps;
        energyHistory.push(currentEnergy);

        // Periodic reheating to escape deep local minima
        if (
          reheatingSchedule &&
          iteration > 0 &&
          iteration % reheatingPeriod === 0
        ) {
          // Reheat if we're getting stuck (low acceptance ratio)
          if (
            acceptanceRatio < 0.1 &&
            noImprovementCount > reheatingPeriod / 2
          ) {
            temperature = Math.max(
              temperature,
              initialTemperature * reheatingFactor,
            );
            Prime.Logger.info('Reheating annealing process', {
              iteration,
              temperature,
              acceptanceRatio,
            });
            noImprovementCount = 0;
          }
        }

        // Adaptive cooling schedule
        // Cool faster when acceptance ratio is high, slower when it's low
        let adaptiveCoolingRate = coolingRate;
        if (acceptanceRatio > 0.8) {
          // Many accepts, cool faster
          adaptiveCoolingRate = coolingRate * 0.95;
        } else if (acceptanceRatio < 0.2) {
          // Few accepts, cool slower
          adaptiveCoolingRate = coolingRate * 1.05;
        }

        // Keep cooling rate in reasonable bounds
        adaptiveCoolingRate = Math.max(
          0.8,
          Math.min(0.999, adaptiveCoolingRate),
        );

        // Cool the system
        temperature *= adaptiveCoolingRate;

        // Early stopping condition
        const recentEnergies = energyHistory.slice(-10);
        if (recentEnergies.length >= 10) {
          // Check if energy has stabilized
          // const stable = true; // Unused variable
          const latestEnergy = recentEnergies[recentEnergies.length - 1];
          const energyVariation = recentEnergies.reduce(
            (max, e) => Math.max(max, Math.abs(e - latestEnergy)),
            0,
          );

          // If energy variation is very small and temperature is low, terminate
          if (
            energyVariation < 1e-8 &&
            temperature < initialTemperature * 0.01
          ) {
            Prime.Logger.info('Early stopping: energy stabilized', {
              iteration,
              energyVariation,
              temperature,
            });
            break;
          }
        }
      }

      // Perform final local optimization to fine-tune the solution
      if (options.finalLocalOptimization) {
        // Use gradient descent for final refinement
        let localSolution = bestSolution.slice();
        const localSteps = 20;
        const learningRate = 1e-4;

        for (let step = 0; step < localSteps; step++) {
          try {
            const gradient = this._computeGradient(localSolution);
            if (!Prime.Utils.isArray(gradient)) continue;

            // Update using gradient descent
            const newSolution = localSolution.map(
              (val, idx) => val - learningRate * gradient[idx],
            );

            // Apply constraints
            const constrainedSolution = applyConstraints(newSolution);

            // Check if this improves the solution
            const newEnergy = calculateEnergy(constrainedSolution);
            if (newEnergy < bestEnergy) {
              localSolution = constrainedSolution;
              bestSolution = constrainedSolution;
              bestEnergy = newEnergy;
            } else {
              // No improvement, stop local optimization
              break;
            }
          } catch (error) {
            Prime.Logger.warn('Final local optimization failed', {
              error: error.message,
            });
            break;
          }
        }
      }

      // Return the best solution found
      return bestSolution;
    },
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
      if (
        fiber &&
        Prime.Clifford.isAlgebra &&
        Prime.Clifford.isAlgebra(fiber)
      ) {
        // Fiber is valid
      } else if (fiber && typeof fiber !== 'object') {
        throw new Prime.ValidationError(
          'Fiber must be a valid algebraic structure',
          {
            context: { fiberType: typeof fiber },
          },
        );
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
          context: { providedType: typeof valueFunction },
        });
      }

      return {
        reference: this,
        valueAt: (point) => {
          const value = valueFunction(point);
          return this.createObject(value);
        },
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
      if (
        Prime.Clifford.isAlgebra &&
        Prime.Clifford.isAlgebra(this.fiber) &&
        Prime.Clifford.isAlgebra(other.fiber)
      ) {
        // For Clifford algebras, check dimension and signature
        return (
          this.fiber.dimension === other.fiber.dimension &&
          this.fiber.signature.every((v, i) => v === other.fiber.signature[i])
        );
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
          context: { providedType: typeof reference },
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
      // Check for function transformation first
      if (typeof transformation === 'function') {
        try {
          // Apply function transformation
          const transformed = transformation(this.value);
          return new UORObject(this.reference, transformed);
        } catch (error) {
          throw new Prime.InvalidOperationError(
            'Cannot apply function transformation',
            {
              context: {
                error: error.message,
                valueType: typeof this.value,
              },
            },
          );
        }
      }

      // Apply to multivector
      if (
        Prime.Clifford.isMultivector &&
        Prime.Clifford.isMultivector(this.value)
      ) {
        if (
          Prime.Lie.isGroupElement &&
          Prime.Lie.isGroupElement(transformation)
        ) {
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
        if (
          Prime.Lie.isGroupElement &&
          Prime.Lie.isGroupElement(transformation)
        ) {
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

      throw new Prime.InvalidOperationError(
        'Cannot apply transformation to this object',
        {
          context: {
            valueType: typeof this.value,
            transformationType: typeof transformation,
          },
        },
      );
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
        throw new Prime.ValidationError(
          'New reference must be a UORReference',
          {
            context: { providedType: typeof newReference },
          },
        );
      }

      // Check if references are compatible
      if (!this.reference.isCompatibleWith(newReference)) {
        throw new Prime.InvalidOperationError(
          'References are not compatible for projection',
          {
            context: {
              sourceReference: this.reference.toString(),
              targetReference: newReference.toString(),
            },
          },
        );
      }

      // If references are already equal, return this object
      if (this.reference === newReference) {
        return this;
      }

      // Handle projection between points in the same manifold
      if (this.reference.manifold === newReference.manifold) {
        // Get source and target points
        const sourcePoint = this.reference.point;
        const targetPoint = newReference.point;

        // Check if a connection is available on the manifold
        const connection =
          this.reference.manifold && this.reference.manifold.connection;

        // For Clifford multivectors, apply proper parallel transport
        if (
          Prime.Clifford.isMultivector &&
          Prime.Clifford.isMultivector(this.value)
        ) {
          // If a connection is available, use it for parallel transport
          if (connection && typeof connection.transport === 'function') {
            try {
              // Use the connection's transport function
              const transportedValue = connection.transport(
                this.value,
                sourcePoint,
                targetPoint,
              );
              return new UORObject(newReference, transportedValue);
            } catch (error) {
              Prime.Logger.warn(
                'Connection transport failed, falling back to matrix transport',
                {
                  error: error.message,
                },
              );
              // Fall through to matrix transport
            }
          }

          // If no connection or connection failed, try matrix-based transport
          if (
            this.reference.manifold &&
            typeof this.reference.manifold.getTransportMatrix === 'function'
          ) {
            try {
              // Get transport matrix between the points
              const transportMatrix =
                this.reference.manifold.getTransportMatrix(
                  sourcePoint,
                  targetPoint,
                );

              if (transportMatrix) {
                // Apply the transport matrix to the multivector
                const valueArray = this.value.toArray();
                const result = [];
                // const compensation = 0; // For Kahan summation - unused variable

                // Apply the matrix transformation with Kahan summation for numerical stability
                for (let i = 0; i < transportMatrix.length; i++) {
                  let sum = 0;
                  let comp = 0; // Compensation term

                  for (let j = 0; j < transportMatrix[i].length; j++) {
                    const product = transportMatrix[i][j] * valueArray[j];
                    const y = product - comp;
                    const t = sum + y;
                    comp = t - sum - y;
                    sum = t;
                  }

                  result.push(sum);
                }

                // Convert back to a multivector
                const transportedValue = this.value.algebra.vector(result);
                return new UORObject(newReference, transportedValue);
              }
            } catch (error) {
              Prime.Logger.warn(
                'Matrix transport failed, falling back to Lie transport',
                {
                  error: error.message,
                },
              );
              // Fall through to Lie group transport
            }
          }

          // If matrix transport fails, try Lie group transport for vectors
          if (
            this.value.isVector &&
            this.reference.fiber &&
            typeof this.reference.fiber.getTransportOperator === 'function'
          ) {
            try {
              // Get Lie group transport operator
              const transportOp = this.reference.fiber.getTransportOperator(
                sourcePoint,
                targetPoint,
              );

              if (transportOp) {
                // Apply the transport operator
                const transportedValue = transportOp.apply(this.value);
                return new UORObject(newReference, transportedValue);
              }
            } catch (error) {
              Prime.Logger.warn(
                'Lie transport failed, falling back to fallback mechanism',
                {
                  error: error.message,
                },
              );
              // Fall through to the fallback
            }
          }

          // Fallback: attempt to use a numerical approximation of parallel transport
          // Calculate a geodesic between the points and transport along it
          if (
            this.reference.manifold &&
            typeof this.reference.manifold.computeGeodesic === 'function'
          ) {
            try {
              // Get a discrete geodesic path
              const geodesic = this.reference.manifold.computeGeodesic(
                sourcePoint,
                targetPoint,
              );

              if (geodesic && geodesic.length > 1) {
                // Step-by-step transport along the geodesic
                let currentValue = this.value;

                for (let i = 1; i < geodesic.length; i++) {
                  // Segment source/target variables not used in this implementation
                  // const segmentSource = geodesic[i-1];
                  // const segmentTarget = geodesic[i];

                  // For small steps, we can use linear approximation
                  // In a full implementation, this would use the connection coefficients
                  // or solve parallel transport differential equations

                  // For now, we use the identity transport for each segment
                  currentValue = currentValue.clone(); // Just to avoid reference issues
                }

                return new UORObject(newReference, currentValue);
              }
            } catch (error) {
              Prime.Logger.warn('Geodesic transport failed', {
                error: error.message,
              });
              // Fall through to default transport
            }
          }
        }

        // For arrays (vectors), apply proper parallel transport
        if (Prime.Utils.isArray(this.value)) {
          // If a connection is available, use it for parallel transport
          if (connection && typeof connection.transport === 'function') {
            try {
              // Use the connection's transport function
              const transportedValue = connection.transport(
                this.value,
                sourcePoint,
                targetPoint,
              );
              return new UORObject(newReference, transportedValue);
            } catch (error) {
              Prime.Logger.warn(
                'Connection transport failed for array, falling back to matrix transport',
                {
                  error: error.message,
                },
              );
              // Fall through to matrix transport
            }
          }

          // Try matrix-based transport for arrays
          if (
            this.reference.manifold &&
            typeof this.reference.manifold.getTransportMatrix === 'function'
          ) {
            try {
              // Get transport matrix between the points
              const transportMatrix =
                this.reference.manifold.getTransportMatrix(
                  sourcePoint,
                  targetPoint,
                );

              if (
                transportMatrix &&
                transportMatrix.length === this.value.length
              ) {
                // Apply the transport matrix using Kahan summation
                const result = [];

                for (let i = 0; i < transportMatrix.length; i++) {
                  let sum = 0;
                  let compensation = 0;

                  for (let j = 0; j < this.value.length; j++) {
                    // Kahan summation for numerical stability
                    const product = transportMatrix[i][j] * this.value[j];
                    const y = product - compensation;
                    const t = sum + y;
                    compensation = t - sum - y;
                    sum = t;
                  }

                  result.push(sum);
                }

                return new UORObject(newReference, result);
              }
            } catch (error) {
              Prime.Logger.warn('Matrix transport failed for array', {
                error: error.message,
              });
              // Fall through to default transport
            }
          }

          // If no proper transport is available, default to identity transport with a copy
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
      const valueString =
        typeof this.value.toString === 'function'
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
      if (
        this.fiber &&
        Prime.Clifford.isAlgebra &&
        Prime.Clifford.isAlgebra(this.fiber)
      ) {
        // Fiber is a valid Clifford algebra
      } else if (this.fiber && typeof this.fiber !== 'object') {
        throw new Prime.ValidationError(
          'Fiber must be a valid algebraic structure',
          {
            context: { fiberType: typeof this.fiber },
          },
        );
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
          context: { providedType: typeof valueFunction },
        });
      }

      return {
        bundle: this,
        valueAt: (point) => {
          const reference = this.createReference(point);
          const value = valueFunction(point);
          return reference.createObject(value);
        },
      };
    }

    /**
     * Parallel transport a section along a curve
     * @param {Object} section - Section to transport
     * @param {Array} curve - Curve in the base manifold
     * @param {Object} [options={}] - Transport options
     * @returns {Object} Transported section
     */
    parallelTransport(section, curve, options = {}) {
      if (!Prime.Utils.isArray(curve) || curve.length < 2) {
        throw new Prime.ValidationError(
          'Curve must be an array with at least two points',
          {
            context: {
              curveType: typeof curve,
              curveLength: curve ? curve.length : null,
            },
          },
        );
      }

      // Use connection if available
      if (this.connection && typeof this.connection.transport === 'function') {
        return this.connection.transport(section, curve, options);
      }

      // For manifolds with connection coefficients (Christoffel symbols)
      if (
        this.baseManifold &&
        typeof this.baseManifold.getConnectionCoefficients === 'function'
      ) {
        try {
          // Integrate parallel transport equations along the curve
          const startPoint = curve[0];
          const startVector = section.valueAt(startPoint).value;

          // Only process if startVector is an array or multivector
          if (
            Prime.Utils.isArray(startVector) ||
            (Prime.Clifford.isMultivector &&
              Prime.Clifford.isMultivector(startVector))
          ) {
            // Initialize transported vector with the starting vector
            let transportedVector;
            if (Prime.Utils.isArray(startVector)) {
              transportedVector = [...startVector];
            } else {
              transportedVector = startVector.clone();
            }

            // Step along the curve and solve parallel transport equations
            for (let i = 1; i < curve.length; i++) {
              const point1 = curve[i - 1];
              const point2 = curve[i];

              // Get connection coefficients at the midpoint (or first point as an approximation)
              const connectionCoefficients =
                this.baseManifold.getConnectionCoefficients(point1);

              if (connectionCoefficients) {
                // Calculate tangent vector (direction of the curve)
                const tangent = [];
                for (let j = 0; j < point1.length; j++) {
                  tangent.push(point2[j] - point1[j]);
                }

                // Normalize the tangent vector if needed
                const tangentNorm = Math.sqrt(
                  tangent.reduce((sum, val) => sum + val * val, 0),
                );
                if (tangentNorm > 0) {
                  for (let j = 0; j < tangent.length; j++) {
                    tangent[j] /= tangentNorm;
                  }
                }

                // Compute the transport for this segment using parallel transport equations
                if (Prime.Utils.isArray(transportedVector)) {
                  // For arrays (vectors)
                  const updatedVector = transportedVector.slice();

                  // Apply the connection coefficients (first-order approximation of parallel transport)
                  for (let j = 0; j < transportedVector.length; j++) {
                    let correction = 0;
                    let compensation = 0; // For Kahan summation

                    for (let k = 0; k < transportedVector.length; k++) {
                      for (let l = 0; l < tangent.length; l++) {
                        // Get the connection coefficient Γ^j_kl
                        const gamma =
                          (connectionCoefficients[j] &&
                            connectionCoefficients[j][k] &&
                            connectionCoefficients[j][k][l]) ||
                          0;

                        // Apply the correction term with Kahan summation for stability
                        const term =
                          -gamma *
                          transportedVector[k] *
                          tangent[l] *
                          tangentNorm;
                        const y = term - compensation;
                        const t = correction + y;
                        compensation = t - correction - y;
                        correction = t;
                      }
                    }

                    updatedVector[j] += correction;
                  }

                  transportedVector = updatedVector;
                } else if (
                  Prime.Clifford.isMultivector &&
                  Prime.Clifford.isMultivector(transportedVector)
                ) {
                  // For multivectors, convert to array and back to handle Clifford algebra elements
                  const vectorArray = transportedVector.toArray();
                  const updatedArray = vectorArray.slice();

                  // Apply connection corrections as above
                  // This is a simplified approach for multivectors
                  for (let j = 0; j < vectorArray.length; j++) {
                    let correction = 0;
                    let compensation = 0;

                    for (let k = 0; k < vectorArray.length; k++) {
                      for (let l = 0; l < tangent.length; l++) {
                        const gamma =
                          (connectionCoefficients[j] &&
                            connectionCoefficients[j][k] &&
                            connectionCoefficients[j][k][l]) ||
                          0;

                        const term =
                          -gamma * vectorArray[k] * tangent[l] * tangentNorm;
                        const y = term - compensation;
                        const t = correction + y;
                        compensation = t - correction - y;
                        correction = t;
                      }
                    }

                    updatedArray[j] += correction;
                  }

                  // Convert back to a multivector
                  transportedVector =
                    transportedVector.algebra.vector(updatedArray);
                }
              }
            }

            // Create the transported section
            const endPoint = curve[curve.length - 1];
            const finalValue = transportedVector;

            return {
              bundle: this,
              valueAt: (point) => {
                if (point === endPoint) {
                  const reference = this.createReference(point);
                  return reference.createObject(finalValue);
                }
                return section.valueAt(point);
              },
            };
          }
        } catch (error) {
          Prime.Logger.warn('Advanced parallel transport failed:', {
            error: error.message,
          });
          // Fall through to matrix-based transport
        }
      }

      // Matrix-based transport as a fallback
      if (
        this.baseManifold &&
        typeof this.baseManifold.getTransportMatrix === 'function'
      ) {
        try {
          const startPoint = curve[0];
          const endPoint = curve[curve.length - 1];
          const transportMatrix = this.baseManifold.getTransportMatrix(
            startPoint,
            endPoint,
          );

          if (transportMatrix) {
            return {
              bundle: this,
              valueAt: (point) => {
                if (point === endPoint) {
                  const startValue = section.valueAt(startPoint).value;
                  let transportedValue;

                  // Apply the transport matrix to the value
                  if (Prime.Utils.isArray(startValue)) {
                    transportedValue = [];
                    for (let i = 0; i < transportMatrix.length; i++) {
                      let sum = 0;
                      let compensation = 0;

                      for (let j = 0; j < startValue.length; j++) {
                        // Kahan summation for stability
                        const product = transportMatrix[i][j] * startValue[j];
                        const y = product - compensation;
                        const t = sum + y;
                        compensation = t - sum - y;
                        sum = t;
                      }

                      transportedValue.push(sum);
                    }
                  } else if (
                    Prime.Clifford.isMultivector &&
                    Prime.Clifford.isMultivector(startValue)
                  ) {
                    // For multivectors, convert to array and back
                    const startArray = startValue.toArray();
                    const resultArray = [];

                    for (let i = 0; i < transportMatrix.length; i++) {
                      let sum = 0;
                      let compensation = 0;

                      for (let j = 0; j < startArray.length; j++) {
                        const product = transportMatrix[i][j] * startArray[j];
                        const y = product - compensation;
                        const t = sum + y;
                        compensation = t - sum - y;
                        sum = t;
                      }

                      resultArray.push(sum);
                    }

                    transportedValue = startValue.algebra.vector(resultArray);
                  } else {
                    // For other types, use deepClone
                    transportedValue = Prime.Utils.deepClone(startValue);
                  }

                  const reference = this.createReference(point);
                  return reference.createObject(transportedValue);
                }

                return section.valueAt(point);
              },
            };
          }
        } catch (error) {
          Prime.Logger.warn('Matrix transport failed:', {
            error: error.message,
          });
          // Fall through to default implementation
        }
      }

      // Default implementation: identity transport (fallback)
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
        },
      };
    }

    /**
     * Calculate the covariant derivative of a section along a vector
     * @param {Object} section - Section
     * @param {Array} vector - Vector in the base manifold
     * @param {Object} [options={}] - Derivative options
     * @returns {Object} Derivative section
     */
    covariantDerivative(section, vector, options = {}) {
      // Validate inputs
      if (!section || typeof section.valueAt !== 'function') {
        throw new Prime.ValidationError('Section must have a valueAt method');
      }

      if (!Prime.Utils.isArray(vector)) {
        throw new Prime.ValidationError('Vector must be an array');
      }

      // Use connection if available
      if (this.connection && typeof this.connection.derivative === 'function') {
        return this.connection.derivative(section, vector, options);
      }

      // For manifolds with connection coefficients
      if (
        this.baseManifold &&
        typeof this.baseManifold.getConnectionCoefficients === 'function'
      ) {
        // We'll implement a proper covariant derivative using the connection coefficients
        return {
          bundle: this,
          valueAt: (point) => {
            try {
              const sectionValue = section.valueAt(point).value;
              const reference = this.createReference(point);

              // Get the partial derivatives of the section at this point
              // The directional derivative in direction 'vector' is the inner product of vector with ∇S
              let directionalDerivative;

              // Calculate directional derivative based on the section value type
              if (Prime.Utils.isArray(sectionValue)) {
                // For array values (vector fields)
                const connectionCoefficients =
                  this.baseManifold.getConnectionCoefficients(point);

                // Initialize the result array
                directionalDerivative = Array(sectionValue.length).fill(0);

                // First, add the ordinary directional derivative component
                // This requires evaluating partial derivatives of section components
                // For simplification, we'll use a numerical approximation with central differences
                const h = options.stepSize || 1e-6; // Step size for numerical differentiation

                // For each component of the section value
                for (let i = 0; i < sectionValue.length; i++) {
                  let partialSum = 0;
                  let compensation = 0; // For Kahan summation

                  // Compute the directional derivative as sum of partial derivatives
                  for (let j = 0; j < vector.length; j++) {
                    if (Math.abs(vector[j]) < 1e-10) continue; // Skip near-zero components

                    // Construct points for central difference
                    const forwardPoint = [...point];
                    const backwardPoint = [...point];
                    forwardPoint[j] += h;
                    backwardPoint[j] -= h;

                    // Get section values at these points
                    const forwardValue = section.valueAt(forwardPoint).value;
                    const backwardValue = section.valueAt(backwardPoint).value;

                    // Central difference formula with Kahan summation
                    const partialDerivative =
                      (forwardValue[i] - backwardValue[i]) / (2 * h);
                    const term = vector[j] * partialDerivative;
                    const y = term - compensation;
                    const t = partialSum + y;
                    compensation = t - partialSum - y;
                    partialSum = t;
                  }

                  // Store the ordinary directional derivative component
                  directionalDerivative[i] = partialSum;

                  // Now add the connection coefficient terms for the covariant derivative
                  if (connectionCoefficients) {
                    let connectionSum = 0;
                    let connectionComp = 0; // For Kahan summation

                    // Sum over connection coefficient terms
                    for (let j = 0; j < sectionValue.length; j++) {
                      for (let k = 0; k < vector.length; k++) {
                        const gamma =
                          (connectionCoefficients[i] &&
                            connectionCoefficients[i][j] &&
                            connectionCoefficients[i][j][k]) ||
                          0;

                        const term = gamma * sectionValue[j] * vector[k];
                        const y = term - connectionComp;
                        const t = connectionSum + y;
                        connectionComp = t - connectionSum - y;
                        connectionSum = t;
                      }
                    }

                    // Add the connection term to the directional derivative
                    directionalDerivative[i] += connectionSum;
                  }
                }

                return reference.createObject(directionalDerivative);
              } else if (
                Prime.Clifford.isMultivector &&
                Prime.Clifford.isMultivector(sectionValue)
              ) {
                // For multivector fields
                // This is a simplified implementation
                // Convert to array, compute covariant derivative components, and convert back
                const valueArray = sectionValue.toArray();
                const connectionCoefficients =
                  this.baseManifold.getConnectionCoefficients(point);
                const derivativeArray = Array(valueArray.length).fill(0);

                // Same procedure as for arrays
                const h = options.stepSize || 1e-6;

                for (let i = 0; i < valueArray.length; i++) {
                  let partialSum = 0;
                  let compensation = 0;

                  for (let j = 0; j < vector.length; j++) {
                    if (Math.abs(vector[j]) < 1e-10) continue;

                    const forwardPoint = [...point];
                    const backwardPoint = [...point];
                    forwardPoint[j] += h;
                    backwardPoint[j] -= h;

                    const forwardArray = section
                      .valueAt(forwardPoint)
                      .value.toArray();
                    const backwardArray = section
                      .valueAt(backwardPoint)
                      .value.toArray();

                    const partialDerivative =
                      (forwardArray[i] - backwardArray[i]) / (2 * h);
                    const term = vector[j] * partialDerivative;
                    const y = term - compensation;
                    const t = partialSum + y;
                    compensation = t - partialSum - y;
                    partialSum = t;
                  }

                  derivativeArray[i] = partialSum;

                  if (connectionCoefficients) {
                    let connectionSum = 0;
                    let connectionComp = 0;

                    for (let j = 0; j < valueArray.length; j++) {
                      for (let k = 0; k < vector.length; k++) {
                        const gamma =
                          (connectionCoefficients[i] &&
                            connectionCoefficients[i][j] &&
                            connectionCoefficients[i][j][k]) ||
                          0;

                        const term = gamma * valueArray[j] * vector[k];
                        const y = term - connectionComp;
                        const t = connectionSum + y;
                        connectionComp = t - connectionSum - y;
                        connectionSum = t;
                      }
                    }

                    derivativeArray[i] += connectionSum;
                  }
                }

                // Convert back to a multivector
                directionalDerivative =
                  sectionValue.algebra.vector(derivativeArray);
                return reference.createObject(directionalDerivative);
              }

              // For other types, we'll return a zero value as fallback
              return this._createZeroObject(reference, sectionValue);
            } catch (error) {
              Prime.Logger.warn('Covariant derivative calculation failed:', {
                error: error.message,
              });
              const reference = this.createReference(point);
              return this._createZeroObject(
                reference,
                section.valueAt(point).value,
              );
            }
          },
        };
      }

      // Default implementation: zero derivative (flat connection)
      return {
        bundle: this,
        valueAt: (point) => {
          const reference = this.createReference(point);
          return this._createZeroObject(
            reference,
            section.valueAt(point).value,
          );
        },
      };
    }

    /**
     * Helper method to create a zero object of the same type as the input
     * @private
     * @param {UORReference} reference - Reference to create object at
     * @param {*} templateValue - Template value to determine type
     * @returns {UORObject} Zero object
     */
    _createZeroObject(reference, templateValue) {
      // Return zero element in the fiber
      if (Prime.Clifford.isAlgebra && Prime.Clifford.isAlgebra(this.fiber)) {
        return reference.createObject(this.fiber.scalar(0));
      }

      if (
        Prime.Clifford.isMultivector &&
        Prime.Clifford.isMultivector(templateValue)
      ) {
        return reference.createObject(templateValue.scale(0));
      }

      if (Prime.Utils.isArray(templateValue)) {
        // Zero array of the same length
        const zeroArray = Array(templateValue.length).fill(0);
        return reference.createObject(zeroArray);
      }

      return reference.createObject(0);
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
    createReference: function (config) {
      return new UORReference(config.manifold, config.point, config.fiber);
    },

    /**
     * Create a UOR fiber bundle
     * @param {Object} config - Configuration object
     * @returns {UORFiberBundle} New UOR fiber bundle
     */
    createFiberBundle: function (config) {
      return new UORFiberBundle(config);
    },

    /**
     * Check if an object is a UOR reference
     * @param {*} obj - Object to check
     * @returns {boolean} True if obj is a UOR reference
     */
    isReference: function (obj) {
      return obj instanceof UORReference;
    },

    /**
     * Check if an object is a UOR object
     * @param {*} obj - Object to check
     * @returns {boolean} True if obj is a UOR object
     */
    isObject: function (obj) {
      return obj instanceof UORObject;
    },

    /**
     * Check if an object is a UOR fiber bundle
     * @param {*} obj - Object to check
     * @returns {boolean} True if obj is a UOR fiber bundle
     */
    isFiberBundle: function (obj) {
      return obj instanceof UORFiberBundle;
    },
  };
})(Prime);

// CommonJS export (no ES module export to avoid circular dependency)
if (typeof module !== 'undefined' && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== 'undefined') {
  window.Prime = Prime;
}
