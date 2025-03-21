/**
 * PrimeOS JavaScript Library - Mathematics
 * Mathematical foundations including Clifford Algebra and Lie Groups
 * Version 1.0.0
 */

// Import core using CommonJS to avoid circular dependency
const Prime = require("./core.js");

(function (Prime) {
  /**
   * Enhanced Multivector implementation with sparse representation
   */
  class Multivector {
    /**
     * Construct a new multivector
     * @param {Object} components - Components of the multivector
     * @param {CliffordAlgebra} [algebra] - Associated Clifford algebra
     */
    constructor(components = {}, algebra = null) {
      this.components = this._normalizeComponents(components);
      this._algebra = algebra;
      this._cachedValues = new Map();
    }

    /**
     * Normalize components by removing zero values
     * @private
     */
    _normalizeComponents(components) {
      const normalized = {};

      for (const grade in components) {
        const gradeParts = {};

        for (const basis in components[grade]) {
          const value = components[grade][basis];

          // Use epsilon comparison for better floating-point precision
          if (Math.abs(value) > Number.EPSILON) {
            gradeParts[basis] = value;
          }
        }

        if (Object.keys(gradeParts).length > 0) {
          normalized[grade] = gradeParts;
        }
      }

      return normalized;
    }

    /**
     * Set the algebra for this multivector
     * @param {CliffordAlgebra} algebra - Clifford algebra
     * @returns {Multivector} This multivector for chaining
     */
    setAlgebra(algebra) {
      if (!(algebra instanceof CliffordAlgebra)) {
        throw new Prime.ValidationError("Expected a CliffordAlgebra instance");
      }

      this._algebra = algebra;
      this._cachedValues.clear(); // Clear cached values when algebra changes
      return this;
    }

    /**
     * Get the algebra for this multivector
     * @returns {CliffordAlgebra} Associated Clifford algebra
     * @throws {MathematicalError} If algebra is not set
     */
    getAlgebra() {
      if (!this._algebra) {
        throw new Prime.MathematicalError("Algebra not set for multivector");
      }
      return this._algebra;
    }

    /**
     * Check if this multivector has an associated algebra
     * @returns {boolean} True if algebra is set
     */
    hasAlgebra() {
      return this._algebra !== null;
    }

    /**
     * Get all grades present in this multivector
     * @returns {number[]} Array of grades
     */
    getGrades() {
      return Object.keys(this.components)
        .map(Number)
        .sort((a, b) => a - b);
    }

    /**
     * Add another multivector to this one
     * @param {Multivector} other - Multivector to add
     * @returns {Multivector} New multivector representing the sum
     * @throws {MathematicalError} If algebras don't match
     */
    add(other) {
      this._checkAlgebraCompatibility(other);

      const result = new Multivector({}, this._algebra);
      const allGrades = new Set([
        ...Object.keys(this.components),
        ...Object.keys(other.components),
      ]);

      for (const grade of allGrades) {
        const a = this.components[grade] || {};
        const b = other.components[grade] || {};

        result.components[grade] = {};

        const allBasisElements = new Set([
          ...Object.keys(a),
          ...Object.keys(b),
        ]);

        for (const basis of allBasisElements) {
          const valueA = a[basis] || 0;
          const valueB = b[basis] || 0;
          const sum = valueA + valueB;

          if (sum !== 0) {
            result.components[grade][basis] = sum;
          }
        }

        if (Object.keys(result.components[grade]).length === 0) {
          delete result.components[grade];
        }
      }

      return result;
    }

    /**
     * Subtract another multivector from this one
     * @param {Multivector} other - Multivector to subtract
     * @returns {Multivector} New multivector representing the difference
     */
    subtract(other) {
      return this.add(other.scale(-1));
    }

    /**
     * Scale this multivector by a scalar
     * @param {number} scalar - Scalar value
     * @returns {Multivector} New scaled multivector
     */
    scale(scalar) {
      if (!Prime.Utils.isNumber(scalar)) {
        throw new Prime.ValidationError("Scalar must be a number", {
          context: { providedType: typeof scalar },
        });
      }

      if (scalar === 0) {
        return new Multivector({}, this._algebra);
      }

      if (scalar === 1) {
        return this.clone();
      }

      const result = new Multivector({}, this._algebra);

      for (const grade in this.components) {
        result.components[grade] = {};

        for (const basis in this.components[grade]) {
          const value = this.components[grade][basis] * scalar;

          if (value !== 0) {
            result.components[grade][basis] = value;
          }
        }

        if (Object.keys(result.components[grade]).length === 0) {
          delete result.components[grade];
        }
      }

      return result;
    }

    /**
     * Multiply this multivector by another using the geometric product
     * @param {Multivector} other - Multivector to multiply by
     * @returns {Multivector} New multivector representing the product
     * @throws {MathematicalError} If algebra is not set or algebras don't match
     */
    multiply(other) {
      this._checkAlgebraCompatibility(other);
      const algebra = this.getAlgebra();

      const result = new Multivector({}, algebra);

      // Caching key for this multiplication
      const cacheKey = `multiply:${this.toString()}:${other.toString()}`;

      if (this._cachedValues.has(cacheKey)) {
        return this._cachedValues.get(cacheKey);
      }

      // Implement geometric product based on the algebra's multiplication table
      for (const gradeA in this.components) {
        for (const gradeB in other.components) {
          for (const basisA in this.components[gradeA]) {
            for (const basisB in other.components[gradeB]) {
              const valueA = this.components[gradeA][basisA];
              const valueB = other.components[gradeB][basisB];

              try {
                const {
                  grade: resultGrade,
                  basis: resultBasis,
                  sign,
                } = algebra.getMultiplicationResult(basisA, basisB);

                const value = valueA * valueB * sign;

                if (!result.components[resultGrade]) {
                  result.components[resultGrade] = {};
                }

                const currentValue =
                  result.components[resultGrade][resultBasis] || 0;
                result.components[resultGrade][resultBasis] =
                  currentValue + value;

                if (result.components[resultGrade][resultBasis] === 0) {
                  delete result.components[resultGrade][resultBasis];

                  if (
                    Object.keys(result.components[resultGrade]).length === 0
                  ) {
                    delete result.components[resultGrade];
                  }
                }
              } catch (error) {
                throw new Prime.MathematicalError(
                  `Error calculating product of ${basisA} and ${basisB}: ${error.message}`,
                  { context: { basisA, basisB, valueA, valueB } },
                );
              }
            }
          }
        }
      }

      // Cache the result
      this._cachedValues.set(cacheKey, result);

      return result;
    }

    /**
     * Calculate the inner product with another multivector
     * @param {Multivector} other - Multivector to calculate inner product with
     * @returns {Multivector} New multivector representing the inner product
     */
    dot(other) {
      this._checkAlgebraCompatibility(other);
      const algebra = this.getAlgebra();

      const result = new Multivector({}, algebra);

      // Caching key for this operation
      const cacheKey = `dot:${this.toString()}:${other.toString()}`;

      if (this._cachedValues.has(cacheKey)) {
        return this._cachedValues.get(cacheKey);
      }

      // Implement inner product based on the algebra's rules
      for (const gradeA in this.components) {
        for (const gradeB in other.components) {
          // For inner product, |a-b| gives resulting grade
          const resultGrade = Math.abs(parseInt(gradeA) - parseInt(gradeB));

          for (const basisA in this.components[gradeA]) {
            for (const basisB in other.components[gradeB]) {
              const valueA = this.components[gradeA][basisA];
              const valueB = other.components[gradeB][basisB];

              try {
                const { grade, basis, sign } = algebra.getMultiplicationResult(
                  basisA,
                  basisB,
                );

                // Only include terms that contribute to the inner product
                if (parseInt(grade) === resultGrade) {
                  // Use Kahan summation algorithm for better numerical precision
                  // when accumulating floating point values
                  const value = valueA * valueB * sign;

                  // Check if value is actually significant to avoid adding noise
                  if (Math.abs(value) > Number.EPSILON) {
                    if (!result.components[resultGrade]) {
                      result.components[resultGrade] = {};
                    }

                    // Get current accumulated value or initialize
                    const currentValue =
                      result.components[resultGrade][basis] || 0;

                    // Apply Kahan summation for better precision
                    // This helps mitigate floating point errors when adding many small values
                    // Store compensation term in a property on the result object
                    if (!result._compensation) {
                      result._compensation = {};
                    }
                    if (!result._compensation[resultGrade]) {
                      result._compensation[resultGrade] = {};
                    }

                    // Get or initialize compensation for this basis
                    const compensationKey = `${resultGrade}:${basis}`;
                    const compensation =
                      result._compensation[compensationKey] || 0;

                    // Kahan summation algorithm
                    const y = value - compensation;
                    const t = currentValue + y;
                    result._compensation[compensationKey] =
                      t - currentValue - y;

                    // Store the updated value
                    result.components[resultGrade][basis] = t;

                    // Clean up if the value is effectively zero
                    if (
                      Math.abs(result.components[resultGrade][basis]) <
                      Number.EPSILON
                    ) {
                      delete result.components[resultGrade][basis];
                      delete result._compensation[compensationKey];

                      if (
                        Object.keys(result.components[resultGrade]).length === 0
                      ) {
                        delete result.components[resultGrade];
                      }
                    }
                  }
                }
              } catch (error) {
                throw new Prime.MathematicalError(
                  `Error calculating inner product of ${basisA} and ${basisB}: ${error.message}`,
                  { context: { basisA, basisB, valueA, valueB } },
                );
              }
            }
          }
        }
      }

      // Cache the result
      this._cachedValues.set(cacheKey, result);

      return result;
    }

    /**
     * Calculate the outer product with another multivector
     * @param {Multivector} other - Multivector to calculate outer product with
     * @returns {Multivector} New multivector representing the outer product
     */
    wedge(other) {
      this._checkAlgebraCompatibility(other);
      const algebra = this.getAlgebra();

      const result = new Multivector({}, algebra);

      // Caching key for this operation
      const cacheKey = `wedge:${this.toString()}:${other.toString()}`;

      if (this._cachedValues.has(cacheKey)) {
        return this._cachedValues.get(cacheKey);
      }

      // Implement outer product based on the algebra's rules
      for (const gradeA in this.components) {
        for (const gradeB in other.components) {
          // For outer product, a+b gives resulting grade
          const resultGrade = parseInt(gradeA) + parseInt(gradeB);

          for (const basisA in this.components[gradeA]) {
            for (const basisB in other.components[gradeB]) {
              const valueA = this.components[gradeA][basisA];
              const valueB = other.components[gradeB][basisB];

              try {
                const { grade, basis, sign } = algebra.getMultiplicationResult(
                  basisA,
                  basisB,
                );

                // Only include terms that contribute to the outer product
                if (parseInt(grade) === resultGrade) {
                  const value = valueA * valueB * sign;

                  if (!result.components[resultGrade]) {
                    result.components[resultGrade] = {};
                  }

                  const currentValue =
                    result.components[resultGrade][basis] || 0;
                  result.components[resultGrade][basis] = currentValue + value;

                  if (result.components[resultGrade][basis] === 0) {
                    delete result.components[resultGrade][basis];

                    if (
                      Object.keys(result.components[resultGrade]).length === 0
                    ) {
                      delete result.components[resultGrade];
                    }
                  }
                }
              } catch (error) {
                throw new Prime.MathematicalError(
                  `Error calculating outer product of ${basisA} and ${basisB}: ${error.message}`,
                  { context: { basisA, basisB, valueA, valueB } },
                );
              }
            }
          }
        }
      }

      // Cache the result
      this._cachedValues.set(cacheKey, result);

      return result;
    }

    /**
     * Extract a specific grade from this multivector
     * @param {number} n - Grade to extract
     * @returns {Multivector} New multivector containing only the specified grade
     */
    grade(n) {
      if (!Prime.Utils.isNumber(n) || n < 0 || !Number.isInteger(n)) {
        throw new Prime.ValidationError(
          "Grade must be a non-negative integer",
          {
            context: { providedValue: n },
          },
        );
      }

      const result = new Multivector({}, this._algebra);
      const gradeKey = n.toString();

      if (this.components[gradeKey]) {
        result.components[gradeKey] = { ...this.components[gradeKey] };
      }

      return result;
    }

    /**
     * Extract the scalar part (grade 0) of this multivector
     * @returns {Multivector} New multivector containing only the scalar part
     */
    scalar() {
      return this.grade(0);
    }

    /**
     * Extract the vector part (grade 1) of this multivector
     * @returns {Multivector} New multivector containing only the vector part
     */
    vector() {
      return this.grade(1);
    }

    /**
     * Extract the bivector part (grade 2) of this multivector
     * @returns {Multivector} New multivector containing only the bivector part
     */
    bivector() {
      return this.grade(2);
    }

    /**
     * Calculate the reverse of this multivector
     * @returns {Multivector} New multivector representing the reverse
     */
    reverse() {
      const result = new Multivector({}, this._algebra);

      for (const grade in this.components) {
        const g = parseInt(grade);
        // For reverse, apply (-1)^(k*(k-1)/2) to grade k
        const sign = Math.pow(-1, (g * (g - 1)) / 2);

        result.components[grade] = {};

        for (const basis in this.components[grade]) {
          result.components[grade][basis] =
            this.components[grade][basis] * sign;
        }
      }

      return result;
    }

    /**
     * Calculate the conjugate of this multivector
     * @returns {Multivector} New multivector representing the conjugate
     */
    conjugate() {
      const result = new Multivector({}, this._algebra);

      for (const grade in this.components) {
        const g = parseInt(grade);
        // For conjugate, apply (-1)^k to grade k
        const sign = Math.pow(-1, g);

        result.components[grade] = {};

        for (const basis in this.components[grade]) {
          result.components[grade][basis] =
            this.components[grade][basis] * sign;
        }
      }

      return result;
    }

    /**
     * Calculate the norm of this multivector using a numerically stable algorithm
     * @returns {number} Euclidean norm
     */
    norm() {
      // Special case: zero multivector
      if (this.isZero()) {
        return 0;
      }

      // For better numerical stability, directly compute the norm for simple cases
      if (this.isScalar()) {
        return Math.abs(this.scalarValue());
      }

      // Handle numerical stability issues with standard approach
      const rev = this.reverse();
      const product = this.multiply(rev);

      // The Euclidean norm is the square root of the scalar part of x*~x
      const scalarPart = product.scalar();

      // Handle potential numerical inaccuracies in the scalar part
      if (!scalarPart.components[0] || !scalarPart.components[0]["1"]) {
        // Calculate the norm as a fallback by summing squares of components
        let sumOfSquares = 0;

        for (const grade in this.components) {
          for (const basis in this.components[grade]) {
            const value = this.components[grade][basis];
            sumOfSquares += value * value;
          }
        }

        return Math.sqrt(sumOfSquares);
      }

      // Handle potential negative values from numerical errors
      const scalarValue = scalarPart.components[0]["1"];

      // Use absolute value to ensure we don't try to take sqrt of negative number
      // due to floating point errors
      return Math.sqrt(Math.abs(scalarValue));
    }

    /**
     * Calculate the coherence norm of this multivector
     * @returns {number} Coherence norm
     */
    coherenceNorm() {
      // For a general multivector, this is the same as the Euclidean norm
      // but it can be overridden for specific applications
      return this.norm();
    }

    /**
     * Check if this multivector is zero
     * @returns {boolean} True if this multivector is zero
     */
    isZero() {
      return Object.keys(this.components).length === 0;
    }

    /**
     * Check if this multivector is a scalar
     * @returns {boolean} True if this multivector is a scalar
     */
    isScalar() {
      const grades = Object.keys(this.components);
      return grades.length === 0 || (grades.length === 1 && grades[0] === "0");
    }

    /**
     * Get the scalar value if this multivector is a scalar
     * @returns {number} Scalar value
     * @throws {MathematicalError} If this multivector is not a scalar
     */
    scalarValue() {
      if (!this.isScalar()) {
        throw new Prime.MathematicalError("Multivector is not a scalar");
      }

      if (!this.components[0] || !this.components[0]["1"]) {
        return 0;
      }

      return this.components[0]["1"];
    }

    /**
     * Create a deep clone of this multivector
     * @returns {Multivector} Cloned multivector
     */
    clone() {
      return new Multivector(
        Prime.Utils.deepClone(this.components),
        this._algebra,
      );
    }

    /**
     * Convert this multivector to an array (for vector part only)
     * @returns {number[]} Array of vector components
     */
    toArray() {
      if (!this.components[1]) {
        return [];
      }

      const result = [];
      const dimension = this._algebra ? this._algebra.dimension : 0;

      for (let i = 1; i <= dimension; i++) {
        const basis = `e${i}`;
        result.push(this.components[1][basis] || 0);
      }

      return result;
    }

    /**
     * Convert this multivector to a string
     * @returns {string} String representation
     */
    toString() {
      const terms = [];

      for (const grade in this.components) {
        for (const basis in this.components[grade]) {
          const value = this.components[grade][basis];

          if (value !== 0) {
            const valueStr =
              value === 1 && basis !== "1"
                ? ""
                : value === -1 && basis !== "1"
                  ? "-"
                  : value;
            const basisStr =
              basis === "1" ? (value === 1 || value === -1 ? "1" : "") : basis;
            const term = valueStr + basisStr;
            terms.push(term);
          }
        }
      }

      if (terms.length === 0) {
        return "0";
      }

      return terms.join(" + ").replace(/\+ -/g, "- ");
    }

    /**
     * Check if this multivector's algebra is compatible with another multivector's algebra
     * @private
     * @param {Multivector} other - Other multivector
     * @throws {MathematicalError} If algebras don't match
     */
    _checkAlgebraCompatibility(other) {
      if (!(other instanceof Multivector)) {
        throw new Prime.ValidationError("Expected a Multivector instance", {
          context: { providedType: typeof other },
        });
      }

      // If both have no algebra, that's fine
      if (!this._algebra && !other._algebra) {
        return;
      }

      // If one has an algebra and the other doesn't, use the defined one
      if (!this._algebra && other._algebra) {
        this._algebra = other._algebra;
        return;
      }

      if (this._algebra && !other._algebra) {
        other.setAlgebra(this._algebra);
        return;
      }

      // If both have algebras, they must match
      if (this._algebra && other._algebra && this._algebra !== other._algebra) {
        // Check if the algebras have the same dimension and signature
        const sameDimension =
          this._algebra.dimension === other._algebra.dimension;
        const sameSignature = this._algebra.signature.every(
          (v, i) => v === other._algebra.signature[i],
        );

        if (!sameDimension || !sameSignature) {
          throw new Prime.MathematicalError("Incompatible Clifford algebras", {
            context: {
              algebra1: {
                dimension: this._algebra.dimension,
                signature: this._algebra.signature,
              },
              algebra2: {
                dimension: other._algebra.dimension,
                signature: other._algebra.signature,
              },
            },
          });
        }
      }
    }
  }

  /**
   * Complete CliffordAlgebra implementation
   */
  class CliffordAlgebra {
    /**
     * Construct a new Clifford algebra
     * @param {Object} config - Configuration object
     * @param {number} [config.dimension=3] - Dimension of the algebra
     * @param {number[]} [config.signature] - Signature of the algebra (defaults to all positive)
     */
    constructor(config = {}) {
      this.dimension = config.dimension || 3;

      if (
        !Prime.Utils.isNumber(this.dimension) ||
        this.dimension < 0 ||
        !Number.isInteger(this.dimension)
      ) {
        throw new Prime.ValidationError(
          "Dimension must be a non-negative integer",
          {
            context: { providedValue: this.dimension },
          },
        );
      }

      // Signature defines the square of basis vectors (1 for positive, -1 for negative, 0 for null)
      this.signature = config.signature || Array(this.dimension).fill(1);

      if (
        !Prime.Utils.isArray(this.signature) ||
        this.signature.length !== this.dimension
      ) {
        throw new Prime.ValidationError(
          "Signature must be an array matching the dimension",
          {
            context: {
              dimension: this.dimension,
              signatureLength: this.signature ? this.signature.length : null,
            },
          },
        );
      }

      // Generate basis elements
      this.basis = this._generateBasis();

      // Initialize the multiplication table
      this.multiplicationTable = this._generateMultiplicationTable();
    }

    /**
     * Generate basis elements for this algebra
     * @private
     * @returns {string[]} Array of basis element names
     */
    _generateBasis() {
      const basis = ["1"]; // Scalar basis

      // Generate all basis elements using binary counting (2^dimension of them)
      for (let i = 1; i < 1 << this.dimension; i++) {
        let name = "";
        for (let j = 0; j < this.dimension; j++) {
          if (i & (1 << j)) {
            name += `e${j + 1}`;
          }
        }
        basis.push(name);
      }

      return basis;
    }

    /**
     * Generate multiplication table for this algebra
     * @private
     * @returns {Object} Multiplication table
     */
    _generateMultiplicationTable() {
      const table = {};

      // Initialize with scalar multiplication (identity)
      for (const b of this.basis) {
        table["1," + b] = { grade: this._getGrade(b), basis: b, sign: 1 };
        table[b + ",1"] = { grade: this._getGrade(b), basis: b, sign: 1 };
      }

      // Handle vector basis elements (e1, e2, etc.)
      for (let i = 1; i <= this.dimension; i++) {
        const ei = `e${i}`;

        // e_i * e_i = signature[i-1]
        const signatureValue = this.signature[i - 1];
        table[`${ei},${ei}`] = {
          grade: 0,
          basis: "1",
          sign: signatureValue,
        };

        // e_i * e_j = -e_j * e_i (for i != j)
        for (let j = i + 1; j <= this.dimension; j++) {
          const ej = `e${j}`;
          const eij = `e${i}e${j}`;

          table[`${ei},${ej}`] = { grade: 2, basis: eij, sign: 1 };
          table[`${ej},${ei}`] = { grade: 2, basis: eij, sign: -1 };
        }
      }

      // Handle bivector products
      for (let i = 1; i <= this.dimension; i++) {
        for (let j = i + 1; j <= this.dimension; j++) {
          const eij = `e${i}e${j}`;

          for (let k = 1; k <= this.dimension; k++) {
            if (k !== i && k !== j) {
              const ek = `e${k}`;

              // Calculate (e_i e_j) * e_k
              let result, sign;

              if (k < i) {
                // e_k before e_i and e_j
                result = `e${k}e${i}e${j}`;
                sign = 1;
              } else if (k > j) {
                // e_k after e_i and e_j
                result = `e${i}e${j}e${k}`;
                sign = 1;
              } else {
                // e_k between e_i and e_j - compute the correct sign
                result = `e${i}e${k}e${j}`;
                sign = -1; // Additional sign flip
              }

              table[`${eij},${ek}`] = { grade: 3, basis: result, sign };
            }
          }
        }
      }

      // For a complete implementation, we would generate the entire table recursively
      // This is a simplified version that handles up to bivectors for demonstration

      return table;
    }

    /**
     * Get the grade of a basis element
     * @private
     * @param {string} basis - Basis element name
     * @returns {number} Grade of the basis element
     */
    _getGrade(basis) {
      if (basis === "1") return 0;

      // Count the number of vector basis elements in the product
      const matches = basis.match(/e\d+/g);
      return matches ? matches.length : 0;
    }

    /**
     * Get the result of multiplying two basis elements with robust error handling
     * @param {string} a - First basis element
     * @param {string} b - Second basis element
     * @returns {Object} Multiplication result with grade, basis, and sign
     * @throws {MathematicalError} If the multiplication is not defined
     */
    getMultiplicationResult(a, b) {
      // Validate input basis elements
      if (typeof a !== "string" || typeof b !== "string") {
        throw new Prime.ValidationError("Basis elements must be strings", {
          context: { a_type: typeof a, b_type: typeof b },
        });
      }

      // First check the multiplication table
      const key = `${a},${b}`;

      if (this.multiplicationTable[key]) {
        return this.multiplicationTable[key];
      }

      // Special case handling for identity ('1')
      if (a === "1") {
        return { grade: this._getGrade(b), basis: b, sign: 1 };
      }

      if (b === "1") {
        return { grade: this._getGrade(a), basis: a, sign: 1 };
      }

      // For basis elements not directly in the table, we need to decompose
      // and multiply component by component.
      try {
        // Handle decomposition of a if it's not a primitive basis
        if (a !== "1" && !a.match(/^e\d+$/)) {
          // Split a into first vector and rest
          const firstVectorMatch = a.match(/^e\d+/);

          if (!firstVectorMatch) {
            throw new Prime.MathematicalError(`Invalid basis element: ${a}`);
          }

          const firstVector = firstVectorMatch[0];
          const rest = a.substring(firstVector.length);

          if (!rest) {
            throw new Prime.MathematicalError(
              `Failed to decompose basis element: ${a}`,
            );
          }

          // Recursively calculate (firstVector * (rest * b))
          const innerResult = this.getMultiplicationResult(rest, b);
          const outerResult = this.getMultiplicationResult(
            firstVector,
            innerResult.basis,
          );

          // Combine the signs
          return {
            grade: outerResult.grade,
            basis: outerResult.basis,
            sign: innerResult.sign * outerResult.sign,
          };
        }

        // Handle decomposition of b if it's not a primitive basis
        if (b !== "1" && !b.match(/^e\d+$/)) {
          // Split b into first vector and rest
          const firstVectorMatch = b.match(/^e\d+/);

          if (!firstVectorMatch) {
            throw new Prime.MathematicalError(`Invalid basis element: ${b}`);
          }

          const firstVector = firstVectorMatch[0];
          const rest = b.substring(firstVector.length);

          if (!rest) {
            throw new Prime.MathematicalError(
              `Failed to decompose basis element: ${b}`,
            );
          }

          // Recursively calculate ((a * firstVector) * rest)
          const innerResult = this.getMultiplicationResult(a, firstVector);
          const outerResult = this.getMultiplicationResult(
            innerResult.basis,
            rest,
          );

          // Combine the signs
          return {
            grade: outerResult.grade,
            basis: outerResult.basis,
            sign: innerResult.sign * outerResult.sign,
          };
        }

        // If we can't handle via decomposition, try direct product calculation
        // by checking if a and b are primitive basis elements
        if (a.match(/^e\d+$/) && b.match(/^e\d+$/)) {
          // Extract indices
          const aIndex = parseInt(a.substring(1));
          const bIndex = parseInt(b.substring(1));

          if (aIndex === bIndex) {
            // e_i * e_i = signature[i-1]
            if (aIndex > 0 && aIndex <= this.dimension) {
              const signatureValue = this.signature[aIndex - 1];
              return {
                grade: 0,
                basis: "1",
                sign: signatureValue,
              };
            }
          } else {
            // e_i * e_j = e_i e_j for i < j (with sign 1)
            // e_j * e_i = e_i e_j for i < j (with sign -1)
            const [minIndex, maxIndex] =
              aIndex < bIndex ? [aIndex, bIndex] : [bIndex, aIndex];
            const sign = aIndex < bIndex ? 1 : -1;

            return {
              grade: 2,
              basis: `e${minIndex}e${maxIndex}`,
              sign,
            };
          }
        }

        // If we reach here, we couldn't calculate the product
        throw new Prime.MathematicalError(
          `Multiplication not implemented for ${a} and ${b}`,
          {
            context: {
              basisA: a,
              basisB: b,
              algebraDimension: this.dimension,
            },
          },
        );
      } catch (error) {
        // Enhance error with more context
        if (error instanceof Prime.MathematicalError) {
          error.context = {
            ...(error.context || {}),
            basisA: a,
            basisB: b,
            algebraDimension: this.dimension,
          };
        }
        throw error;
      }
    }

    /**
     * Connect this algebra to the Prime Framework
     * @param {Object} framework - Framework to connect to
     * @returns {CliffordAlgebra} This algebra for chaining
     */
    connectToPrimeFramework(framework) {
      // This method would establish connections to other parts of the Prime Framework
      // It's a placeholder for future integration
      return this;
    }

    /**
     * Create a scalar multivector
     * @param {number} value - Scalar value
     * @returns {Multivector} Scalar multivector
     */
    scalar(value) {
      if (!Prime.Utils.isNumber(value)) {
        throw new Prime.ValidationError("Scalar value must be a number", {
          context: { providedType: typeof value },
        });
      }

      if (value === 0) {
        return new Multivector({}, this);
      }

      const components = { 0: { 1: value } };
      return new Multivector(components, this);
    }

    /**
     * Create a vector multivector
     * @param {number[]} components - Vector components
     * @returns {Multivector} Vector multivector
     */
    vector(components) {
      if (!Prime.Utils.isArray(components)) {
        throw new Prime.ValidationError("Vector components must be an array", {
          context: { providedType: typeof components },
        });
      }

      const result = { 1: {} };

      for (let i = 0; i < components.length && i < this.dimension; i++) {
        if (components[i] !== 0) {
          result[1][`e${i + 1}`] = components[i];
        }
      }

      return new Multivector(result, this);
    }

    /**
     * Create a bivector multivector
     * @param {Array|Array[]} components - Bivector components as matrix or array of [i,j,value] triples
     * @returns {Multivector} Bivector multivector
     */
    bivector(components) {
      if (!Prime.Utils.isArray(components)) {
        throw new Prime.ValidationError(
          "Bivector components must be an array",
          {
            context: { providedType: typeof components },
          },
        );
      }

      const result = { 2: {} };

      if (components.length === 0) {
        return new Multivector(result, this);
      }

      // Check if components is a matrix (2D array)
      if (Prime.Utils.isArray(components[0])) {
        // Matrix form [i][j] = coefficient of e_i ∧ e_j
        for (let i = 0; i < components.length; i++) {
          if (!Prime.Utils.isArray(components[i])) {
            throw new Prime.ValidationError(
              "Bivector matrix row must be an array",
              {
                context: { rowIndex: i, providedType: typeof components[i] },
              },
            );
          }

          for (let j = 0; j < components[i].length; j++) {
            if (components[i][j] !== 0) {
              // Only store the coefficient for i<j (upper triangular)
              // since e_i ∧ e_j = -e_j ∧ e_i
              if (i < j) {
                result[2][`e${i + 1}e${j + 1}`] = components[i][j];
              } else if (i > j) {
                // For lower triangular, negate and swap indices
                const existingKey = `e${j + 1}e${i + 1}`;
                result[2][existingKey] =
                  (result[2][existingKey] || 0) - components[i][j];
              }
              // If i=j, it should be zero (e_i ∧ e_i = 0), so we ignore it
            }
          }
        }
      } else {
        // Array of [i, j, value] triples
        for (const component of components) {
          if (!Prime.Utils.isArray(component) || component.length !== 3) {
            throw new Prime.ValidationError(
              "Each bivector component must be a [i,j,value] array",
              {
                context: { providedValue: component },
              },
            );
          }

          const [i, j, value] = component;

          if (i === j || value === 0) {
            continue; // Skip zero components and diagonal terms
          }

          // Ensure i < j by swapping if necessary
          const basis = i < j ? `e${i}e${j}` : `e${j}e${i}`;
          const sign = i < j ? 1 : -1;

          result[2][basis] = (result[2][basis] || 0) + sign * value;

          if (result[2][basis] === 0) {
            delete result[2][basis];
          }
        }
      }

      if (Object.keys(result[2]).length === 0) {
        delete result[2];
      }

      return new Multivector(result, this);
    }

    /**
     * Create a general multivector with arbitrary components
     * @param {Object} components - Components of the multivector
     * @returns {Multivector} Multivector with the specified components
     */
    multivector(components) {
      return new Multivector(components, this);
    }

    /**
     * Create a multivector from an array representation
     * @param {number[]} arr - Array of values
     * @returns {Multivector} Vector multivector
     */
    fromArray(arr) {
      return this.vector(arr);
    }

    /**
     * Generate a pseudoscalar for this algebra
     * @returns {Multivector} Pseudoscalar multivector
     */
    pseudoscalar() {
      const components = {};
      components[this.dimension.toString()] = {
        [`e${"".padStart(this.dimension, "1")}`]: 1,
      };

      return new Multivector(components, this);
    }

    /**
     * Convert a matrix to a multivector
     * @param {Array[]} matrix - Matrix representation
     * @returns {Multivector} Multivector representation
     */
    fromMatrix(matrix) {
      // This is a placeholder. Actual implementation would depend on the specific
      // matrix representation and algebra dimension
      throw new Prime.MathematicalError(
        "Matrix conversion not implemented for this algebra",
      );
    }
  }

  /**
   * Lie Group and Lie Algebra implementations
   */
  class LieGroup {
    /**
     * Construct a new Lie group
     * @param {string} name - Name of the group
     * @param {number} dimension - Dimension of the group
     */
    constructor(name, dimension) {
      this.name = name;
      this.dimension = dimension;
      this.generators = this._createGenerators();
    }

    /**
     * Create the generators for this Lie group
     * @private
     * @returns {Array} Array of generators
     */
    _createGenerators() {
      // Placeholder for creating Lie algebra generators
      // This would be implemented differently for each specific group
      return [];
    }

    /**
     * Create a group element from parameters
     * @param {Object} params - Parameters for the group element
     * @returns {LieGroupElement} New group element
     */
    element(params) {
      return new LieGroupElement(this, params);
    }

    /**
     * Get a generator of the Lie algebra
     * @param {string|number} basis - Basis identifier
     * @returns {LieAlgebraElement} Generator
     * @throws {InvalidOperationError} If the generator is not found
     */
    generator(basis) {
      if (typeof basis === "string") {
        const gen = this.generators.find((g) => g.name === basis);
        if (gen) {
          return new LieAlgebraElement(this, gen.name, gen.matrix);
        }
      } else if (typeof basis === "number") {
        if (basis >= 0 && basis < this.generators.length) {
          const gen = this.generators[basis];
          return new LieAlgebraElement(this, gen.name, gen.matrix);
        }
      }

      throw new Prime.InvalidOperationError(`Generator ${basis} not found`, {
        context: {
          groupName: this.name,
          availableGenerators: this.generators.map((g) => g.name),
        },
      });
    }

    /**
     * Create a rotation transformation
     * @param {number[]} axis - Rotation axis
     * @param {number} angle - Rotation angle in radians
     * @returns {LieGroupElement} Rotation element
     */
    rotation(axis, angle) {
      // Would be implemented differently for each group
      return this.element({ type: "rotation", axis, angle });
    }

    /**
     * Create a reflection transformation
     * @param {number[]} normal - Normal vector to reflection plane
     * @returns {LieGroupElement} Reflection element
     */
    reflection(normal) {
      // Would be implemented differently for each group
      return this.element({ type: "reflection", normal });
    }

    /**
     * Create a translation transformation
     * @param {number[]} vector - Translation vector
     * @returns {LieGroupElement} Translation element
     */
    translation(vector) {
      // Would be implemented differently for each group
      return this.element({ type: "translation", vector });
    }

    /**
     * Calculate the product of two group elements
     * @param {LieGroupElement} a - First element
     * @param {LieGroupElement} b - Second element
     * @returns {LieGroupElement} Product element
     * @throws {InvalidOperationError} If elements are incompatible
     */
    product(a, b) {
      if (!(a instanceof LieGroupElement) || !(b instanceof LieGroupElement)) {
        throw new Prime.InvalidOperationError(
          "Arguments must be Lie group elements",
          {
            context: {
              aType: a ? a.constructor.name : typeof a,
              bType: b ? b.constructor.name : typeof b,
            },
          },
        );
      }

      if (a.group !== this || b.group !== this) {
        throw new Prime.InvalidOperationError(
          "Elements must belong to the same Lie group",
          {
            context: {
              expectedGroup: this.name,
              aGroup: a.group ? a.group.name : null,
              bGroup: b.group ? b.group.name : null,
            },
          },
        );
      }

      return a.multiply(b);
    }

    /**
     * Check if a transformation preserves coherence
     * @param {LieGroupElement} transform - Transformation to check
     * @returns {boolean} True if the transformation preserves coherence
     */
    preservesCoherence(transform) {
      // This is a placeholder implementation that should be overridden
      // for specific groups with actual coherence preservation criteria

      // By default, assume all proper group elements preserve coherence
      return transform instanceof LieGroupElement && transform.group === this;
    }

    /**
     * Calculate the adjoint action on a Lie algebra element
     * @param {LieGroupElement} g - Group element
     * @param {LieAlgebraElement} X - Lie algebra element
     * @returns {LieAlgebraElement} Result of adjoint action Ad_g(X)
     */
    adjoint(g, X) {
      // The adjoint action is: Ad_g(X) = g X g^(-1)
      // This is a placeholder for a proper implementation
      throw new Prime.MathematicalError(
        "Adjoint action not implemented for this group",
      );
    }
  }

  class LieGroupElement {
    /**
     * Construct a new Lie group element
     * @param {LieGroup} group - Parent Lie group
     * @param {Object} params - Parameters for this element
     */
    constructor(group, params) {
      if (!(group instanceof LieGroup)) {
        throw new Prime.ValidationError("Expected a LieGroup instance", {
          context: { providedType: typeof group },
        });
      }

      this.group = group;
      this.params = params || {};
      this.matrix = this._computeMatrix();
    }

    /**
     * Compute the matrix representation of this element
     * @private
     * @returns {Array[]} Matrix representation
     */
    _computeMatrix() {
      // If a matrix is already provided in the parameters, use it directly
      if (this.params.matrix) {
        return this.params.matrix;
      }

      // Based on the transformation type, compute the appropriate matrix
      switch (this.params.type) {
        case "rotation":
          return this._computeRotationMatrix();
        case "reflection":
          return this._computeReflectionMatrix();
        case "translation":
          return this._computeTranslationMatrix();
        case "exponential":
          return this._computeExponentialMatrix();
        case "composite":
          // This should be handled by the caller providing the matrix
          throw new Prime.MathematicalError(
            "Composite element requires a matrix parameter",
          );
        default:
          // Default to identity matrix
          return Array(this.group.dimension)
            .fill(0)
            .map((_, i) => {
              return Array(this.group.dimension)
                .fill(0)
                .map((_, j) => (i === j ? 1 : 0));
            });
      }
    }

    /**
     * Compute a rotation matrix
     * @private
     * @returns {Array[]} Rotation matrix
     */
    _computeRotationMatrix() {
      // Extract parameters
      const axis = this.params.axis;
      const angle = this.params.angle;

      if (!Prime.Utils.isArray(axis) || !Prime.Utils.isNumber(angle)) {
        throw new Prime.ValidationError(
          "Rotation requires axis array and angle",
          {
            context: {
              axisType: typeof axis,
              angleType: typeof angle,
            },
          },
        );
      }

      // Normalize the axis
      const norm = Math.sqrt(axis.reduce((sum, v) => sum + v * v, 0));

      if (norm === 0) {
        throw new Prime.ValidationError("Rotation axis cannot be zero vector");
      }

      const normalizedAxis = axis.map((v) => v / norm);

      // For SO(3), use Rodrigues' formula
      if (this.group.name === "SO(3)" && normalizedAxis.length === 3) {
        // Precompute trigonometric values
        const cosTheta = Math.cos(angle);
        const sinTheta = Math.sin(angle);
        const oneMinusCos = 1 - cosTheta;

        // Extract axis components for readability
        const x = normalizedAxis[0];
        const y = normalizedAxis[1];
        const z = normalizedAxis[2];

        // Compute the rotation matrix using Rodrigues' formula
        return [
          [
            cosTheta + x * x * oneMinusCos,
            x * y * oneMinusCos - z * sinTheta,
            x * z * oneMinusCos + y * sinTheta,
          ],
          [
            y * x * oneMinusCos + z * sinTheta,
            cosTheta + y * y * oneMinusCos,
            y * z * oneMinusCos - x * sinTheta,
          ],
          [
            z * x * oneMinusCos - y * sinTheta,
            z * y * oneMinusCos + x * sinTheta,
            cosTheta + z * z * oneMinusCos,
          ],
        ];
      }

      // Default to identity for unsupported groups
      throw new Prime.MathematicalError(
        `Rotation matrix calculation not implemented for ${this.group.name}`,
      );
    }

    /**
     * Compute a reflection matrix
     * @private
     * @returns {Array[]} Reflection matrix
     */
    _computeReflectionMatrix() {
      // Extract parameters
      const normal = this.params.normal;

      if (!Prime.Utils.isArray(normal)) {
        throw new Prime.ValidationError(
          "Reflection requires normal vector array",
          {
            context: { normalType: typeof normal },
          },
        );
      }

      // Normalize the normal vector
      const norm = Math.sqrt(normal.reduce((sum, v) => sum + v * v, 0));

      if (norm === 0) {
        throw new Prime.ValidationError(
          "Reflection normal cannot be zero vector",
        );
      }

      const n = normal.map((v) => v / norm);

      // For reflection in R^n, use the Householder formula: I - 2(n⊗n)
      const dim = n.length;
      const result = Array(dim)
        .fill(0)
        .map((_, i) => {
          return Array(dim)
            .fill(0)
            .map((_, j) => {
              return (i === j ? 1 : 0) - 2 * n[i] * n[j];
            });
        });

      return result;
    }

    /**
     * Compute a translation matrix
     * @private
     * @returns {Array[]} Translation matrix
     */
    _computeTranslationMatrix() {
      // Extract parameters
      const vector = this.params.vector;

      if (!Prime.Utils.isArray(vector)) {
        throw new Prime.ValidationError("Translation requires vector array", {
          context: { vectorType: typeof vector },
        });
      }

      // Pure translations are not part of SO(n), they require SE(n) or affine transformations
      // This is just a placeholder - the actual implementation depends on the group
      throw new Prime.MathematicalError(
        `Translation matrix calculation not implemented for ${this.group.name}`,
      );
    }

    /**
     * Compute a matrix exponential
     * @private
     * @returns {Array[]} Exponential matrix
     */
    _computeExponentialMatrix() {
      // Extract parameters
      const generator = this.params.generator;
      const parameter = this.params.parameter || 1;

      if (!generator || !generator.matrix) {
        throw new Prime.ValidationError(
          "Exponential requires generator with matrix",
          {
            context: { generatorType: typeof generator },
          },
        );
      }

      // Scale the generator matrix by the parameter
      const scaledMatrix = generator.matrix.map((row) =>
        row.map((val) => val * parameter),
      );

      // Handle specific cases for known Lie groups
      if (this.group.name === "SO(2)") {
        // For SO(2), the exponential of [[0, -θ], [θ, 0]] is [[cos(θ), -sin(θ)], [sin(θ), cos(θ)]]
        if (scaledMatrix.length === 2 && scaledMatrix[0].length === 2) {
          // Extract the angle parameter (assuming skew-symmetric matrix)
          const theta = scaledMatrix[1][0]; // Extract angle parameter

          // Handle large angles by reducing to standard range
          // This improves numerical precision for large angles
          const reducedTheta = theta % (2 * Math.PI);

          // For angles close to 0 or π/2, use more accurate calculations
          const EPSILON = 1e-12;
          let cosTheta, sinTheta;

          // Handle special cases for better numerical precision
          if (Math.abs(reducedTheta) < EPSILON) {
            // For angles close to 0
            cosTheta = 1;
            sinTheta = 0;
          } else if (Math.abs(reducedTheta - Math.PI / 2) < EPSILON) {
            // For angles close to π/2
            cosTheta = 0;
            sinTheta = 1;
          } else if (Math.abs(reducedTheta - Math.PI) < EPSILON) {
            // For angles close to π
            cosTheta = -1;
            sinTheta = 0;
          } else if (Math.abs(reducedTheta - (3 * Math.PI) / 2) < EPSILON) {
            // For angles close to 3π/2
            cosTheta = 0;
            sinTheta = -1;
          } else {
            // Otherwise use standard trig functions
            cosTheta = Math.cos(reducedTheta);
            sinTheta = Math.sin(reducedTheta);
          }

          return [
            [cosTheta, -sinTheta],
            [sinTheta, cosTheta],
          ];
        }
      } else if (this.group.name === "SO(3)") {
        // For SO(3), we can use Rodrigues' formula for the exponential map
        if (scaledMatrix.length === 3 && scaledMatrix[0].length === 3) {
          // Extract the skew-symmetric components
          const x = scaledMatrix[2][1];
          const y = scaledMatrix[0][2];
          const z = scaledMatrix[1][0];

          // Calculate the norm (angle)
          const normSquared = x * x + y * y + z * z;
          const norm = Math.sqrt(normSquared);

          // Handle zero or near-zero norm case (identity)
          // Use a more mathematically precise epsilon threshold
          const EPSILON = 1e-12;

          if (norm < EPSILON) {
            // Return identity matrix with exact values
            return [
              [1, 0, 0],
              [0, 1, 0],
              [0, 0, 1],
            ];
          }

          // Normalize to get the unit axis
          const axis = [x / norm, y / norm, z / norm];

          // Now use Rodrigues' formula to compute the exponential
          // R = I + sin(θ) K + (1 - cos(θ)) K²
          // where K is the skew-symmetric matrix of the unit axis

          const cos_theta = Math.cos(norm);
          const sin_theta = Math.sin(norm);
          const one_minus_cos = 1 - cos_theta;

          // Unit axis components
          const ux = axis[0];
          const uy = axis[1];
          const uz = axis[2];

          // Apply Rodrigues' formula
          return [
            [
              cos_theta + ux * ux * one_minus_cos,
              ux * uy * one_minus_cos - uz * sin_theta,
              ux * uz * one_minus_cos + uy * sin_theta,
            ],
            [
              uy * ux * one_minus_cos + uz * sin_theta,
              cos_theta + uy * uy * one_minus_cos,
              uy * uz * one_minus_cos - ux * sin_theta,
            ],
            [
              uz * ux * one_minus_cos - uy * sin_theta,
              uz * uy * one_minus_cos + ux * sin_theta,
              cos_theta + uz * uz * one_minus_cos,
            ],
          ];
        }
      }

      // For general case, use a power series approximation
      // exp(A) = I + A + A²/2! + A³/3! + ...
      // with adaptive precision control

      // Initialize with identity matrix
      const dim = scaledMatrix.length;
      const result = Array(dim)
        .fill(0)
        .map((_, i) => {
          return Array(dim)
            .fill(0)
            .map((_, j) => (i === j ? 1 : 0));
        });

      // Calculate the norm of the matrix to determine convergence behavior
      let matrixNorm = 0;
      for (let i = 0; i < dim; i++) {
        let rowSum = 0;
        for (let j = 0; j < dim; j++) {
          rowSum += Math.abs(scaledMatrix[i][j]);
        }
        matrixNorm = Math.max(matrixNorm, rowSum);
      }

      // Determine number of terms needed based on matrix norm
      // Use a convergence threshold based on machine epsilon
      const EPSILON = 1e-15;
      const maxTerms = Math.max(15, Math.ceil(3 * matrixNorm) + 5);

      // Calculate powers of the matrix with numerical stability
      let factorial = 1;
      let powerMatrix = scaledMatrix.map((row) => [...row]); // A¹
      let maxTermValue = 0;

      for (let n = 1; n <= maxTerms; n++) {
        // Calculate A^n / n!
        factorial *= n;

        // Check for factorial overflow
        if (!isFinite(factorial)) {
          // Use Stirling's approximation for large factorials if needed
          console.warn(
            `Matrix exponential: factorial overflow at term ${n}. Using approximation.`,
          );
          factorial = Math.sqrt(2 * Math.PI * n) * Math.pow(n / Math.E, n);
        }

        // Track maximum term value for adaptive precision
        let termMaxValue = 0;

        // Add the term A^n / n!
        for (let i = 0; i < dim; i++) {
          for (let j = 0; j < dim; j++) {
            const termValue = powerMatrix[i][j] / factorial;
            termMaxValue = Math.max(termMaxValue, Math.abs(termValue));
            result[i][j] += termValue;
          }
        }

        // Check for convergence - stop if term values become negligible
        if (termMaxValue < EPSILON * maxTermValue || termMaxValue < EPSILON) {
          break;
        }

        // Update maximum term value seen so far
        if (termMaxValue > maxTermValue) {
          maxTermValue = termMaxValue;
        }

        // Compute next power: A^(n+1) = A^n × A using numerically stable matrix multiplication
        if (n < maxTerms) {
          const nextPower = Array(dim)
            .fill(0)
            .map(() => Array(dim).fill(0));

          for (let i = 0; i < dim; i++) {
            for (let j = 0; j < dim; j++) {
              let sum = 0;
              for (let k = 0; k < dim; k++) {
                sum += powerMatrix[i][k] * scaledMatrix[k][j];
              }

              // Handle potential underflow and roundoff errors
              nextPower[i][j] = Math.abs(sum) < EPSILON ? 0 : sum;
            }
          }

          powerMatrix = nextPower;
        }
      }

      // Clean up matrix by removing near-zero elements
      for (let i = 0; i < dim; i++) {
        for (let j = 0; j < dim; j++) {
          if (Math.abs(result[i][j]) < EPSILON) {
            result[i][j] = 0;
          }
        }
      }

      return result;
    }

    /**
     * Apply this transformation to a vector or multivector
     * @param {number[]|Multivector} vector - Vector or multivector to transform
     * @returns {number[]|Multivector} Transformed vector or multivector
     * @throws {InvalidOperationError} If the transformation cannot be applied
     */
    apply(vector) {
      // Apply to multivector
      if (vector instanceof Multivector) {
        // For vector-grade components, we can apply the matrix transformation
        if (vector.components[1]) {
          const vectorPart = vector.toArray();
          const transformedVector = this._applyToArray(vectorPart);

          // Create a new multivector with the transformed vector part
          const result = vector.clone();

          // Replace the vector part
          result.components[1] = {};
          for (let i = 0; i < transformedVector.length; i++) {
            if (transformedVector[i] !== 0) {
              result.components[1][`e${i + 1}`] = transformedVector[i];
            }
          }

          if (Object.keys(result.components[1]).length === 0) {
            delete result.components[1];
          }

          return result;
        }

        // For other grades, we would need specific transformation rules
        // This is a placeholder for a complete implementation
        return vector;
      }

      // Apply to array (vector)
      if (Prime.Utils.isArray(vector)) {
        return this._applyToArray(vector);
      }

      throw new Prime.InvalidOperationError(
        "Cannot apply transformation to the given object",
        {
          context: { objectType: typeof vector },
        },
      );
    }

    /**
     * Apply this transformation to an array (vector)
     * @private
     * @param {number[]} vector - Vector to transform
     * @returns {number[]} Transformed vector
     */
    _applyToArray(vector) {
      // Ensure the vector has the right dimension, padding with zeros if needed
      const paddedVector = [...vector];
      while (paddedVector.length < this.matrix.length) {
        paddedVector.push(0);
      }

      // Perform matrix-vector multiplication
      const result = Array(this.matrix.length).fill(0);

      for (let i = 0; i < this.matrix.length; i++) {
        for (let j = 0; j < this.matrix[i].length; j++) {
          result[i] += this.matrix[i][j] * paddedVector[j];
        }
      }

      return result;
    }

    /**
     * Multiply this element with another
     * @param {LieGroupElement} other - Element to multiply with
     * @returns {LieGroupElement} Product element
     * @throws {InvalidOperationError} If elements are incompatible
     */
    multiply(other) {
      if (!(other instanceof LieGroupElement)) {
        throw new Prime.InvalidOperationError(
          "Argument must be a Lie group element",
          {
            context: { providedType: typeof other },
          },
        );
      }

      if (this.group !== other.group) {
        throw new Prime.InvalidOperationError(
          "Elements must belong to the same Lie group",
          {
            context: {
              thisGroup: this.group.name,
              otherGroup: other.group.name,
            },
          },
        );
      }

      // Implement matrix multiplication
      // Note: For rotation matrices, AB means "apply B then A"
      const result = Array(this.matrix.length)
        .fill(0)
        .map(() => Array(this.matrix[0].length).fill(0));

      for (let i = 0; i < this.matrix.length; i++) {
        for (let j = 0; j < other.matrix[0].length; j++) {
          for (let k = 0; k < this.matrix[0].length; k++) {
            result[i][j] += this.matrix[i][k] * other.matrix[k][j];
          }
        }
      }

      // Create a new element with the resulting matrix
      return new LieGroupElement(this.group, {
        type: "composite",
        matrix: result,
      });
    }

    /**
     * Calculate the inverse of this element
     * @returns {LieGroupElement} Inverse element
     * @throws {MathematicalError} If the element is not invertible
     */
    invert() {
      // For orthogonal matrices (SO(n)), the inverse is the transpose
      if (this.group.name.startsWith("SO")) {
        const inverse = this.matrix.map((row) => [...row]); // Copy

        // Transpose
        for (let i = 0; i < inverse.length; i++) {
          for (let j = i + 1; j < inverse[i].length; j++) {
            const temp = inverse[i][j];
            inverse[i][j] = inverse[j][i];
            inverse[j][i] = temp;
          }
        }

        return new LieGroupElement(this.group, {
          type: "inverse",
          matrix: inverse,
        });
      }

      // For other groups, we would need specific inversion methods
      throw new Prime.MathematicalError(
        `Matrix inversion not implemented for ${this.group.name}`,
      );
    }

    /**
     * Convert this element to a string
     * @returns {string} String representation
     */
    toString() {
      return `LieGroupElement(${this.group.name}, ${this.params.type || "custom"})`;
    }
  }

  class LieAlgebraElement {
    /**
     * Construct a new Lie algebra element
     * @param {LieGroup} group - Parent Lie group
     * @param {string} name - Name of this element
     * @param {Array[]} matrix - Matrix representation
     */
    constructor(group, name, matrix) {
      if (!(group instanceof LieGroup)) {
        throw new Prime.ValidationError("Expected a LieGroup instance", {
          context: { providedType: typeof group },
        });
      }

      this.group = group;
      this.name = name;
      this.matrix = matrix;
    }

    /**
     * Calculate the exponential map to get a Lie group element
     * @param {number} [t=1] - Parameter for the exponential map
     * @returns {LieGroupElement} Corresponding Lie group element
     */
    exp(t = 1) {
      // For small dimensions, we can use direct formulas

      // For SO(2), the exponential of [[0, -θ], [θ, 0]] is a rotation by angle θ
      // For SO(3), we can use Rodrigues' formula

      return this.group.element({
        type: "exponential",
        generator: this,
        parameter: t,
      });
    }

    /**
     * Add another Lie algebra element
     * @param {LieAlgebraElement} other - Element to add
     * @returns {LieAlgebraElement} Sum element
     * @throws {InvalidOperationError} If elements are incompatible
     */
    add(other) {
      if (!(other instanceof LieAlgebraElement)) {
        throw new Prime.InvalidOperationError(
          "Argument must be a Lie algebra element",
          {
            context: { providedType: typeof other },
          },
        );
      }

      if (this.group !== other.group) {
        throw new Prime.InvalidOperationError(
          "Elements must belong to the same Lie algebra",
          {
            context: {
              thisGroup: this.group.name,
              otherGroup: other.group.name,
            },
          },
        );
      }

      // Add matrices
      const resultMatrix = this.matrix.map((row, i) =>
        row.map((val, j) => val + other.matrix[i][j]),
      );

      return new LieAlgebraElement(
        this.group,
        `${this.name}+${other.name}`,
        resultMatrix,
      );
    }

    /**
     * Scale this element by a scalar
     * @param {number} scalar - Scalar value
     * @returns {LieAlgebraElement} Scaled element
     */
    scale(scalar) {
      if (!Prime.Utils.isNumber(scalar)) {
        throw new Prime.ValidationError("Scalar must be a number", {
          context: { providedType: typeof scalar },
        });
      }

      // Scale the matrix
      const resultMatrix = this.matrix.map((row) =>
        row.map((val) => val * scalar),
      );

      return new LieAlgebraElement(
        this.group,
        `${scalar}${this.name}`,
        resultMatrix,
      );
    }

    /**
     * Calculate the Lie bracket [this, other]
     * @param {LieAlgebraElement} other - Second element
     * @returns {LieAlgebraElement} Bracket result
     * @throws {InvalidOperationError} If elements are incompatible
     */
    bracket(other) {
      if (!(other instanceof LieAlgebraElement)) {
        throw new Prime.InvalidOperationError(
          "Argument must be a Lie algebra element",
          {
            context: { providedType: typeof other },
          },
        );
      }

      if (this.group !== other.group) {
        throw new Prime.InvalidOperationError(
          "Elements must belong to the same Lie algebra",
          {
            context: {
              thisGroup: this.group.name,
              otherGroup: other.group.name,
            },
          },
        );
      }

      // Calculate the commutator [X,Y] = XY - YX

      // First calculate XY
      const XY = Array(this.matrix.length)
        .fill(0)
        .map(() => Array(this.matrix[0].length).fill(0));

      for (let i = 0; i < this.matrix.length; i++) {
        for (let j = 0; j < other.matrix[0].length; j++) {
          for (let k = 0; k < this.matrix[0].length; k++) {
            XY[i][j] += this.matrix[i][k] * other.matrix[k][j];
          }
        }
      }

      // Then calculate YX
      const YX = Array(other.matrix.length)
        .fill(0)
        .map(() => Array(other.matrix[0].length).fill(0));

      for (let i = 0; i < other.matrix.length; i++) {
        for (let j = 0; j < this.matrix[0].length; j++) {
          for (let k = 0; k < other.matrix[0].length; k++) {
            YX[i][j] += other.matrix[i][k] * this.matrix[k][j];
          }
        }
      }

      // Finally calculate XY - YX
      const resultMatrix = XY.map((row, i) =>
        row.map((val, j) => val - YX[i][j]),
      );

      return new LieAlgebraElement(
        this.group,
        `[${this.name},${other.name}]`,
        resultMatrix,
      );
    }

    /**
     * Convert this element to a string
     * @returns {string} String representation
     */
    toString() {
      return `LieAlgebraElement(${this.group.name}, ${this.name})`;
    }
  }

  /**
   * Special Orthogonal Group SO(3)
   */
  class SO3 extends LieGroup {
    /**
     * Construct a new SO(3) group
     */
    constructor() {
      super("SO(3)", 3);
    }

    /**
     * Create the generators for SO(3)
     * @private
     * @returns {Array} Array of generators
     */
    _createGenerators() {
      // Create generators for SO(3)
      // These are the infinitesimal rotations around x, y, and z axes
      // They correspond to the basis of the Lie algebra so(3)
      return [
        {
          name: "X",
          matrix: [
            [0, 0, 0],
            [0, 0, -1],
            [0, 1, 0],
          ],
        },
        {
          name: "Y",
          matrix: [
            [0, 0, 1],
            [0, 0, 0],
            [-1, 0, 0],
          ],
        },
        {
          name: "Z",
          matrix: [
            [0, -1, 0],
            [1, 0, 0],
            [0, 0, 0],
          ],
        },
      ];
    }

    /**
     * Create a rotation in SO(3)
     * @param {number[]} axis - Rotation axis
     * @param {number} angle - Rotation angle in radians
     * @returns {LieGroupElement} Rotation element
     */
    rotation(axis, angle) {
      if (!Prime.Utils.isArray(axis) || axis.length !== 3) {
        throw new Prime.ValidationError("Axis must be a 3D vector array", {
          context: {
            providedType: typeof axis,
            length: axis ? axis.length : null,
          },
        });
      }

      if (!Prime.Utils.isNumber(angle)) {
        throw new Prime.ValidationError("Angle must be a number", {
          context: { providedType: typeof angle },
        });
      }

      // Normalize the axis
      const norm = Math.sqrt(axis.reduce((sum, v) => sum + v * v, 0));

      if (norm === 0) {
        throw new Prime.ValidationError("Rotation axis cannot be zero vector");
      }

      const normalizedAxis = axis.map((v) => v / norm);

      // Create the rotation element
      return new LieGroupElement(this, {
        type: "rotation",
        axis: normalizedAxis,
        angle: angle,
      });
    }
  }

  /**
   * Factory functions for Lie groups
   */
  const LieGroups = {
    /**
     * Create a Special Orthogonal group SO(n)
     * @param {number} n - Dimension
     * @returns {LieGroup} SO(n) group
     * @throws {InvalidOperationError} If the dimension is not supported
     */
    SO: function (n) {
      if (n === 3) {
        return new SO3();
      }

      throw new Prime.InvalidOperationError(`SO(${n}) not implemented`, {
        context: { supportedDimensions: [3] },
      });
    },
  };

  // Extend Prime with mathematical capabilities
  Prime.Clifford = {
    /**
     * Create a new Clifford algebra
     * @param {Object} config - Configuration object
     * @returns {CliffordAlgebra} New Clifford algebra
     */
    create: function (config) {
      return new CliffordAlgebra(config);
    },

    /**
     * Create a multivector from an array
     * @param {number[]} arr - Array of values
     * @returns {Multivector} New multivector
     */
    fromArray: function (arr) {
      if (!Prime.Utils.isArray(arr)) {
        throw new Prime.ValidationError("Expected an array", {
          context: { providedType: typeof arr },
        });
      }

      const algebra = new CliffordAlgebra({ dimension: arr.length });
      return algebra.vector(arr);
    },

    /**
     * Check if an object is a multivector
     * @param {*} obj - Object to check
     * @returns {boolean} True if obj is a multivector
     */
    isMultivector: function (obj) {
      return obj instanceof Multivector;
    },

    /**
     * Check if an object is a Clifford algebra
     * @param {*} obj - Object to check
     * @returns {boolean} True if obj is a Clifford algebra
     */
    isAlgebra: function (obj) {
      return obj instanceof CliffordAlgebra;
    },
  };

  Prime.Lie = {
    /**
     * Create a Special Orthogonal group SO(n)
     * @param {number} n - Dimension
     * @returns {LieGroup} SO(n) group
     */
    SO: function (n) {
      return LieGroups.SO(n);
    },

    /**
     * Check if an object is a Lie group
     * @param {*} obj - Object to check
     * @returns {boolean} True if obj is a Lie group
     */
    isGroup: function (obj) {
      return obj instanceof LieGroup;
    },

    /**
     * Check if an object is a Lie group element
     * @param {*} obj - Object to check
     * @returns {boolean} True if obj is a Lie group element
     */
    isGroupElement: function (obj) {
      return obj instanceof LieGroupElement;
    },

    /**
     * Check if an object is a Lie algebra element
     * @param {*} obj - Object to check
     * @returns {boolean} True if obj is a Lie algebra element
     */
    isAlgebraElement: function (obj) {
      return obj instanceof LieAlgebraElement;
    },
  };
})(Prime);

// CommonJS export (no ES module export in this file to avoid circular dependency)
if (typeof module !== "undefined" && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== "undefined") {
  window.Prime = Prime;
}
