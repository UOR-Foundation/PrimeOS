/**
 * PrimeOS JavaScript Library - Clifford Algebra
 * Implementation of Clifford algebra for geometric computing
 */

// Import the Prime object
const Prime = require("../core");

// Create the Clifford module using IIFE
(function () {
  /**
   * Represents a multivector in Clifford algebra
   */
  class Multivector {
    /**
     * Create a new multivector
     * @param {Object} components - Object mapping basis blade indices to coefficients
     * @param {number} dimensions - Number of dimensions for the algebra
     */
    constructor(components = {}, dimensions = 3) {
      if (!Prime.Utils.isObject(components)) {
        throw new Prime.ValidationError(
          "Components must be an object mapping indices to coefficients",
        );
      }

      if (
        !Prime.Utils.isNumber(dimensions) ||
        dimensions <= 0 ||
        !Number.isInteger(dimensions)
      ) {
        throw new Prime.ValidationError(
          "Dimensions must be a positive integer",
        );
      }

      this.components = { ...components };
      this.dimensions = dimensions;
    }

    /**
     * Get a specific component of the multivector
     * @param {number|string} index - Basis blade index or name
     * @returns {number} - Component value, 0 if not present
     */
    getComponent(index) {
      if (this.components[index] !== undefined) {
        return this.components[index];
      }
      return 0;
    }

    /**
     * Set a specific component of the multivector
     * @param {number|string} index - Basis blade index or name
     * @param {number} value - Component value
     * @returns {Multivector} - This multivector for chaining
     */
    setComponent(index, value) {
      if (!Prime.Utils.isNumber(value)) {
        throw new Prime.ValidationError("Component value must be a number");
      }

      // If value is effectively zero, remove the component to keep storage minimal
      if (Math.abs(value) < 1e-10) {
        delete this.components[index];
      } else {
        this.components[index] = value;
      }

      return this;
    }

    /**
     * Create a copy of this multivector
     * @returns {Multivector} - A new multivector with the same components
     */
    clone() {
      return new Multivector({ ...this.components }, this.dimensions);
    }

    /**
     * Add another multivector to this one
     * @param {Multivector} mv - Multivector to add
     * @returns {Multivector} - New multivector representing the sum
     */
    add(mv) {
      if (!(mv instanceof Multivector)) {
        throw new Prime.ValidationError("Argument must be a Multivector");
      }

      const result = this.clone();

      // Add components from the other multivector
      Object.entries(mv.components).forEach(([index, value]) => {
        const currentValue = result.getComponent(index);
        result.setComponent(index, currentValue + value);
      });

      return result;
    }

    /**
     * Subtract another multivector from this one
     * @param {Multivector} mv - Multivector to subtract
     * @returns {Multivector} - New multivector representing the difference
     */
    subtract(mv) {
      if (!(mv instanceof Multivector)) {
        throw new Prime.ValidationError("Argument must be a Multivector");
      }

      const result = this.clone();

      // Subtract components from the other multivector
      Object.entries(mv.components).forEach(([index, value]) => {
        const currentValue = result.getComponent(index);
        result.setComponent(index, currentValue - value);
      });

      return result;
    }

    /**
     * Scale this multivector by a scalar
     * @param {number} scalar - Scaling factor
     * @returns {Multivector} - New scaled multivector
     */
    scale(scalar) {
      if (!Prime.Utils.isNumber(scalar)) {
        throw new Prime.ValidationError("Scalar must be a number");
      }

      const result = new Multivector({}, this.dimensions);

      // Scale each component
      Object.entries(this.components).forEach(([index, value]) => {
        result.setComponent(index, value * scalar);
      });

      return result;
    }

    /**
     * Calculate the magnitude squared of this multivector
     * @returns {number} - Squared magnitude
     */
    magnitudeSquared() {
      let sum = 0;

      // Sum squares of all components
      Object.values(this.components).forEach((value) => {
        sum += value * value;
      });

      return sum;
    }

    /**
     * Calculate the magnitude of this multivector
     * @returns {number} - Magnitude
     */
    magnitude() {
      return Math.sqrt(this.magnitudeSquared());
    }

    /**
     * Normalize this multivector to unit magnitude
     * @returns {Multivector} - New normalized multivector
     */
    normalize() {
      const mag = this.magnitude();

      if (mag === 0) {
        throw new Prime.MathematicalError(
          "Cannot normalize a zero multivector",
        );
      }

      return this.scale(1 / mag);
    }

    /**
     * Convert this multivector to a string representation
     * @returns {string} - String representation
     */
    toString() {
      if (Object.keys(this.components).length === 0) {
        return "0";
      }

      const terms = [];

      Object.entries(this.components).forEach(([index, value]) => {
        if (Math.abs(value) < 1e-10) return; // Skip near-zero terms

        const basisName = index === "0" ? "" : `e${index}`;
        const sign =
          terms.length > 0
            ? value >= 0
              ? " + "
              : " - "
            : value >= 0
              ? ""
              : "-";
        const absValue = Math.abs(value);
        const valueStr =
          Math.abs(Math.abs(value) - 1) < 1e-10 ? "" : absValue.toString();

        terms.push(`${sign}${valueStr}${basisName}`);
      });

      return terms.join("");
    }
  }

  /**
   * Clifford algebra operations and utilities
   */
  const Clifford = {
    /**
     * Create a new scalar multivector
     * @param {number} value - Scalar value
     * @param {number} dimensions - Number of dimensions
     * @returns {Multivector} - New scalar multivector
     */
    scalar: function (value, dimensions = 3) {
      return new Multivector({ 0: value }, dimensions);
    },

    /**
     * Create a new vector multivector
     * @param {Array} vector - Vector components
     * @returns {Multivector} - New vector multivector
     */
    vector: function (vector) {
      if (!Array.isArray(vector)) {
        throw new Prime.ValidationError("Vector must be an array");
      }

      const dimensions = vector.length;
      const components = {};

      // Set components for each basis vector
      for (let i = 0; i < dimensions; i++) {
        if (vector[i] !== 0) {
          components[`${i + 1}`] = vector[i];
        }
      }

      return new Multivector(components, dimensions);
    },

    /**
     * Create a new bivector multivector
     * @param {Array} matrix - Antisymmetric matrix representing the bivector
     * @returns {Multivector} - New bivector multivector
     */
    bivector: function (matrix) {
      if (
        !Array.isArray(matrix) ||
        !matrix.every((row) => Array.isArray(row))
      ) {
        throw new Prime.ValidationError("Matrix must be a 2D array");
      }

      const dimensions = matrix.length;

      // Verify the matrix is square
      if (!matrix.every((row) => row.length === dimensions)) {
        throw new Prime.ValidationError("Matrix must be square");
      }

      const components = {};

      // Extract bivector components from the antisymmetric matrix
      for (let i = 0; i < dimensions; i++) {
        for (let j = i + 1; j < dimensions; j++) {
          // Use only the upper triangular part (antisymmetric)
          const value = matrix[i][j];
          if (value !== 0) {
            components[`${i + 1}${j + 1}`] = value;
          }
        }
      }

      return new Multivector(components, dimensions);
    },

    /**
     * Compute the geometric product of two multivectors
     * @param {Multivector} a - First multivector
     * @param {Multivector} b - Second multivector
     * @returns {Multivector} - Geometric product result
     */
    geometricProduct: function (a, b) {
      if (!(a instanceof Multivector) || !(b instanceof Multivector)) {
        throw new Prime.ValidationError("Arguments must be Multivectors");
      }

      if (a.dimensions !== b.dimensions) {
        throw new Prime.ValidationError(
          "Multivectors must have the same dimensions",
        );
      }

      const dimensions = a.dimensions;
      const result = new Multivector({}, dimensions);

      // Compute the geometric product (simplified version)
      // In a full implementation, this would handle all blade products correctly
      Object.entries(a.components).forEach(([indexA, valueA]) => {
        Object.entries(b.components).forEach(([indexB, valueB]) => {
          const product = valueA * valueB;

          // For scalar-scalar product
          if (indexA === "0" && indexB === "0") {
            result.setComponent("0", (result.getComponent("0") || 0) + product);
            return;
          }

          // For scalar-blade product
          if (indexA === "0") {
            result.setComponent(
              indexB,
              (result.getComponent(indexB) || 0) + product,
            );
            return;
          }

          // For blade-scalar product
          if (indexB === "0") {
            result.setComponent(
              indexA,
              (result.getComponent(indexA) || 0) + product,
            );
            return;
          }

          // TODO: Implement full geometric product rules
          // This is a simplified placeholder that would need to be expanded
          // with proper blade multiplication rules based on Clifford algebra
        });
      });

      return result;
    },

    /**
     * Compute the outer product of two multivectors
     * @param {Multivector} a - First multivector
     * @param {Multivector} b - Second multivector
     * @returns {Multivector} - Outer product result
     */
    outerProduct: function (a, b) {
      // Simplified implementation - would need complete implementation in production
      // The outer product extracts the antisymmetric part of the geometric product
      return this.geometricProduct(a, b); // Placeholder
    },

    /**
     * Compute the inner product of two multivectors
     * @param {Multivector} a - First multivector
     * @param {Multivector} b - Second multivector
     * @returns {Multivector} - Inner product result
     */
    innerProduct: function (a, b) {
      // Simplified implementation - would need complete implementation in production
      // The inner product extracts the symmetric part of the geometric product
      return this.geometricProduct(a, b); // Placeholder
    },

    /**
     * Multivector class for direct instantiation
     */
    Multivector,
  };

  // Add Clifford to the Prime.Math namespace
  Prime.Math = Prime.Math || {};
  
  // Check if Clifford already has a getter defined, if so, use it
  if (Object.getOwnPropertyDescriptor(Prime.Math, 'Clifford') && 
      Object.getOwnPropertyDescriptor(Prime.Math, 'Clifford').get) {
    // Use a more careful approach to update the property
    const descriptor = Object.getOwnPropertyDescriptor(Prime.Math, 'Clifford');
    const originalGetter = descriptor.get;
    
    Object.defineProperty(Prime.Math, 'Clifford', {
      get: function() {
        const result = originalGetter.call(this);
        // If result is an empty object (placeholder), return our implementation
        if (Object.keys(result).length === 0) {
          return Clifford;
        }
        // Otherwise, preserve what's already there
        return result;
      },
      configurable: true
    });
  } else {
    // Direct assignment if no getter exists
    Prime.Math.Clifford = Clifford;
  }
})();

// Export the enhanced Prime object
module.exports = Prime;
