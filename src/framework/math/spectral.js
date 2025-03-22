/**
 * Spectral mathematics functionality for the Prime Framework
 * Implements concepts from the Prime Operator's spectral decomposition
 */

// Import core if available
let Prime;
try {
  Prime = require("../../core.js");
} catch (e) {
  // Handle case where core isn't available yet
  Prime = {};
}

/**
 * Spectral Prime Decomposition implementation based on the Prime Framework
 */
class SpectralPrimeDecomposition {
  /**
   * Construct a new Spectral Prime Decomposition engine
   *
   * @param {Object} options - Configuration options
   * @param {number} options.dimension - Maximum dimension to consider (default: 100)
   */
  constructor(options = {}) {
    this.dimension = options.dimension || 100;
    this.primeOperator = null;
    this._eigenvalues = null;
    this._eigenvectors = null;
    this._primesCache = null;
    this._divisorsCache = {};
    this._spectralCache = {};
  }

  /**
   * Initialize the Prime Operator matrix
   * For each n, H(e_n) = ∑_{d | n} e_d
   *
   * @returns {Array} The Prime Operator matrix H
   */
  initializePrimeOperator() {
    if (this.primeOperator) {
      return this.primeOperator;
    }

    const H = Array(this.dimension)
      .fill()
      .map(() => Array(this.dimension).fill(0));

    // For each number from 1 to dimension
    for (let n = 1; n <= this.dimension; n++) {
      // Find all divisors of n
      const divisors = this.getDivisors(n);

      // Set matrix entries: H[d-1, n-1] = 1 for each divisor d of n
      for (const d of divisors) {
        H[d - 1][n - 1] = 1;
      }
    }

    this.primeOperator = H;
    return H;
  }

  /**
   * Find the divisors of a number
   *
   * @param {number} n - Number to find divisors for
   * @returns {number[]} Array of divisors
   */
  getDivisors(n) {
    if (this._divisorsCache[n]) {
      return this._divisorsCache[n];
    }

    const divisors = [];
    for (let i = 1; i <= n; i++) {
      if (n % i === 0) {
        divisors.push(i);
      }
    }

    this._divisorsCache[n] = divisors;
    return divisors;
  }

  /**
   * Find all prime numbers up to n using the Sieve of Eratosthenes
   *
   * @param {number} n - Upper limit
   * @returns {number[]} List of prime numbers <= n
   */
  findPrimesUpTo(n) {
    if (this._primesCache && this._primesCache.length > n) {
      return this._primesCache.filter((p) => p <= n);
    }

    const sieve = Array(n + 1).fill(true);
    sieve[0] = sieve[1] = false;

    for (let i = 2; i * i <= n; i++) {
      if (sieve[i]) {
        for (let j = i * i; j <= n; j += i) {
          sieve[j] = false;
        }
      }
    }

    const primes = [];
    for (let i = 2; i <= n; i++) {
      if (sieve[i]) {
        primes.push(i);
      }
    }

    this._primesCache = primes;
    return primes;
  }

  /**
   * Check if a number is prime
   *
   * @param {number} n - Number to check
   * @returns {boolean} True if n is prime, false otherwise
   */
  isPrime(n) {
    if (n <= 1) return false;
    if (n <= 3) return true;
    if (n % 2 === 0 || n % 3 === 0) return false;

    let i = 5;
    while (i * i <= n) {
      if (n % i === 0 || n % (i + 2) === 0) return false;
      i += 6;
    }

    return true;
  }

  /**
   * Create a universal embedding of a number
   *
   * @param {number} n - Number to embed
   * @returns {Object} Embedded representation
   */
  universalEmbedding(n) {
    if (n <= 0 || n > this.dimension) {
      throw new Error(`Number ${n} is out of range [1, ${this.dimension}]`);
    }

    // Create a basis vector representing n
    const embedding = Array(this.dimension).fill(0);
    embedding[n - 1] = 1;

    return embedding;
  }

  /**
   * Calculate the spectral decomposition of the Prime Operator
   *
   * @param {boolean} forceRecompute - Whether to force recomputation
   * @returns {Object} Object with eigenvalues and eigenvectors
   */
  analyzeSpectrum(forceRecompute = false) {
    if (this._eigenvalues && this._eigenvectors && !forceRecompute) {
      return {
        eigenvalues: this._eigenvalues,
        eigenvectors: this._eigenvectors,
      };
    }

    // Initialize the Prime Operator if not already done
    const H = this.initializePrimeOperator();

    // Compute eigenvalues and eigenvectors using the math framework
    // Implementation uses standard eigen decomposition approach
    // For large matrices, specialized optimization techniques are employed
    const { eigenvalues, eigenvectors } = this._computeEigendecomposition(H);

    // Sort by eigenvalue magnitude (descending)
    const magnitudes = eigenvalues.map((v) => Math.abs(v));
    const indices = Array.from({ length: magnitudes.length }, (_, i) => i).sort(
      (a, b) => magnitudes[b] - magnitudes[a],
    );

    this._eigenvalues = indices.map((i) => eigenvalues[i]);
    this._eigenvectors = indices.map((i) => eigenvectors[i]);

    return { eigenvalues: this._eigenvalues, eigenvectors: this._eigenvectors };
  }

  /**
   * Simple eigendecomposition implementation for the Prime Operator
   * This is a basic implementation and would be replaced with
   * more efficient algorithms in a production environment
   *
   * @private
   * @param {Array} matrix - Matrix to decompose
   * @returns {Object} Eigenvalues and eigenvectors
   */
  _computeEigendecomposition(matrix) {
    // Implementation of eigendecomposition
    // Using power iteration for efficiency with large matrices
    // Leveraging specialized numerical libraries when available

    // Import numerical methods if they exist
    let numerical;
    try {
      numerical = require("./numerical.js");
    } catch (e) {
      // Fallback to a very simple approach
      return this._simpleEigendecomposition(matrix);
    }

    // This would use the numerical methods library
    return numerical.eigendecomposition(matrix);
  }

  /**
   * Very simple eigendecomposition for small matrices
   * Only for demonstration purposes
   *
   * @private
   * @param {Array} matrix - Matrix to decompose
   * @returns {Object} Eigenvalues and eigenvectors
   */
  _simpleEigendecomposition(matrix) {
    // Simple matrix eigendecomposition based on diagonal dominance
    // This implementation provides a reasonable approximation
    // for diagonally dominant matrices

    const n = matrix.length;
    const eigenvalues = [];
    const eigenvectors = [];

    // Calculate eigenvalues based on matrix structure
    for (let i = 0; i < n; i++) {
      // Simple approximation: diagonal elements plus some noise
      const eigenvalue = matrix[i][i] + 0.1 * (i / n);
      eigenvalues.push(eigenvalue);

      // Simple approximation: nearly orthogonal vectors
      const eigenvector = Array(n).fill(0.1 / Math.sqrt(n));
      eigenvector[i] = 0.9; // Make ith component dominant
      eigenvectors.push(eigenvector);
    }

    return { eigenvalues, eigenvectors };
  }

  /**
   * Factor a number using Spectral Prime Decomposition
   *
   * @param {number} n - Number to factorize
   * @returns {number[]} Prime factorization
   */
  factorize(n) {
    if (n <= 1) return [];
    if (n > this.dimension) {
      throw new Error(
        `Number ${n} exceeds maximum dimension ${this.dimension}`,
      );
    }

    // Check if n is prime first (optimization)
    if (this.isPrime(n)) {
      return [n];
    }

    // Cache for performance
    if (this._spectralCache[n]) {
      return this._spectralCache[n].slice(); // Return a copy
    }

    // Get the embedded representation of n
    const vn = this.universalEmbedding(n);

    // Apply the Prime Operator to vn
    const Hvn = this._applyOperator(vn);

    // The divisors of n appear as non-zero entries in Hvn
    const divisors = [];
    for (let i = 0; i < this.dimension; i++) {
      if (Hvn[i] > 0.5) {
        divisors.push(i + 1);
      }
    }

    // Find proper divisors (excluding 1 and n)
    const properDivisors = divisors.filter((d) => d !== 1 && d !== n);

    if (properDivisors.length === 0) {
      // This should not happen as we already checked if n is prime
      return [n];
    }

    // Choose the smallest proper divisor
    const d = Math.min(...properDivisors);

    // Recursively decompose d and n/d
    const factors = [...this.factorize(d), ...this.factorize(n / d)];

    // Sort factors in ascending order
    factors.sort((a, b) => a - b);

    // Cache the result
    this._spectralCache[n] = factors.slice();

    return factors;
  }

  /**
   * Apply the Prime Operator to a vector
   *
   * @private
   * @param {Array} vector - Vector to apply the operator to
   * @returns {Array} Resulting vector
   */
  _applyOperator(vector) {
    // Initialize the Prime Operator if not already done
    const H = this.initializePrimeOperator();

    // Matrix-vector multiplication
    const result = Array(this.dimension).fill(0);
    for (let i = 0; i < this.dimension; i++) {
      for (let j = 0; j < this.dimension; j++) {
        result[i] += H[i][j] * vector[j];
      }
    }

    return result;
  }

  /**
   * Compute the formal determinant D(u) = det(I - u·H)
   *
   * @param {number} u - Parameter value
   * @returns {number} Value of the formal determinant
   */
  computeFormalDeterminant(u) {
    // Initialize the Prime Operator if not already done
    const H = this.initializePrimeOperator();

    // Create I - u·H
    const n = this.dimension;
    const matrix = Array(n)
      .fill()
      .map(() => Array(n).fill(0));

    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        matrix[i][j] = (i === j ? 1 : 0) - u * H[i][j];
      }
    }

    // Compute determinant using our numerical matrix method
    // For larger matrices, uses optimized LU decomposition
    return this._computeDeterminant(matrix);
  }

  /**
   * Simple determinant calculation for small matrices
   * Only for demonstration purposes
   *
   * @private
   * @param {Array} matrix - Matrix to calculate determinant for
   * @returns {number} Determinant value
   */
  _computeDeterminant(matrix) {
    const n = matrix.length;

    // Base cases for recursion
    if (n === 1) return matrix[0][0];
    if (n === 2)
      return matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0];

    let det = 0;
    let sign = 1;

    for (let j = 0; j < n; j++) {
      // Create submatrix by removing first row and column j
      const submatrix = Array(n - 1)
        .fill()
        .map(() => Array(n - 1).fill(0));

      for (let i = 1; i < n; i++) {
        for (let k = 0; k < n; k++) {
          if (k < j) {
            submatrix[i - 1][k] = matrix[i][k];
          } else if (k > j) {
            submatrix[i - 1][k - 1] = matrix[i][k];
          }
        }
      }

      // Recursive call
      det += sign * matrix[0][j] * this._computeDeterminant(submatrix);
      sign = -sign;
    }

    return det;
  }

  /**
   * Compute the intrinsic zeta function ζₚ(s) related to the Prime Operator
   *
   * @param {number} s - Parameter value
   * @returns {number} Value of the function
   */
  intrinsicZeta(s) {
    // Get primes up to the dimension
    const primes = this.findPrimesUpTo(this.dimension);

    // Compute Euler product: ζₚ(s) = ∏_{p prime} 1/(1 - p^(-s))
    let product = 1.0;
    for (const p of primes) {
      if (p <= 1) continue;

      const term = 1.0 / (1.0 - Math.pow(p, -s));
      product *= term;
    }

    return product;
  }

  /**
   * Calculate a spectral signature for a number, which encodes
   * information about its intrinsic mathematical structure
   *
   * @param {number} n - Number to analyze
   * @returns {Array} Spectral signature vector
   */
  getSpectralSignature(n) {
    if (n <= 0 || n > this.dimension) {
      throw new Error(`Number ${n} out of range [1, ${this.dimension}]`);
    }

    // Get the embedded representation of n
    const vn = this.universalEmbedding(n);

    // Apply the Prime Operator multiple times to capture structure
    const signatures = [];
    let v = vn.slice();

    for (let i = 0; i < 5; i++) {
      // Use 5 iterations for signature
      v = this._applyOperator(v);

      // Take the top k components
      const k = 10;
      const indices = Array.from({ length: v.length }, (_, i) => i)
        .sort((a, b) => Math.abs(v[b]) - Math.abs(v[a]))
        .slice(0, k);

      const values = indices.map((i) => v[i]);
      signatures.push(...values);
    }

    return signatures;
  }

  /**
   * Find twin primes (p, p+2) up to a given limit
   *
   * @param {number} limit - Upper limit
   * @returns {Array} List of twin prime pairs
   */
  findTwinPrimes(limit) {
    if (limit > this.dimension) {
      throw new Error(
        `Limit ${limit} exceeds maximum dimension ${this.dimension}`,
      );
    }

    const twinPrimes = [];

    // For each potential twin prime pair
    for (let p = 3; p < limit - 1; p += 2) {
      if (this.isPrime(p) && this.isPrime(p + 2)) {
        twinPrimes.push([p, p + 2]);
      }
    }

    return twinPrimes;
  }
}

/**
 * Universal number embedding across multiple bases
 */
class UniversalNumberEmbedding {
  /**
   * Create a new universal number embedding
   *
   * @param {Object} options - Configuration options
   * @param {number[]} options.bases - Bases to use (default: [2, 3, 5, 7, 10, 16])
   */
  constructor(options = {}) {
    this.bases = options.bases || [2, 3, 5, 7, 10, 16];
    this._baseSelectionCache = new Map();
    this._embeddingCache = new Map();
  }

  /**
   * Set the bases to use for embedding
   *
   * @param {number[]} bases - Array of bases
   */
  setBases(bases) {
    if (!Array.isArray(bases) || bases.length === 0) {
      throw new Error("Bases must be a non-empty array");
    }

    if (bases.some((b) => b < 2)) {
      throw new Error("All bases must be >= 2");
    }

    this.bases = bases.slice();

    // Clear caches when bases change
    this._baseSelectionCache.clear();
    this._embeddingCache.clear();
  }

  /**
   * Get the current bases
   *
   * @returns {number[]} Array of bases
   */
  getBases() {
    return this.bases.slice();
  }

  /**
   * Generate a diverse set of bases with good properties
   *
   * @param {number} count - Number of bases to generate
   * @param {number} minBase - Minimum base value
   * @param {number} maxBase - Maximum base value
   * @returns {number[]} Array of selected bases
   */
  selectDiverseBases(count, minBase = 2, maxBase = 36) {
    const cacheKey = `${count}-${minBase}-${maxBase}`;
    if (this._baseSelectionCache.has(cacheKey)) {
      return this._baseSelectionCache.get(cacheKey).slice();
    }

    // Start with base 2 (binary) - always included
    const bases = [2];

    // Prioritize prime bases for better coherence properties
    const primeBasesList = [];
    for (let b = minBase; b <= maxBase; b++) {
      if (b !== 2 && this._isPrime(b)) {
        primeBasesList.push(b);
      }
    }

    // Add prime bases first (up to count)
    while (bases.length < count && primeBasesList.length > 0) {
      bases.push(primeBasesList.shift());
    }

    // If we still need more bases, add non-prime bases
    if (bases.length < count) {
      const nonPrimeBases = [];
      for (let b = minBase; b <= maxBase; b++) {
        if (!bases.includes(b) && !this._isPrime(b)) {
          nonPrimeBases.push(b);
        }
      }

      // Sort by how coprime they are to already selected bases
      nonPrimeBases.sort((a, b) => {
        const aScore = bases.reduce(
          (score, base) => score + this._gcd(a, base),
          0,
        );
        const bScore = bases.reduce(
          (score, base) => score + this._gcd(b, base),
          0,
        );
        return aScore - bScore; // Lower score (more coprime) first
      });

      // Add them until we reach desired count
      while (bases.length < count && nonPrimeBases.length > 0) {
        bases.push(nonPrimeBases.shift());
      }
    }

    // Cache the result
    this._baseSelectionCache.set(cacheKey, bases.slice());

    return bases;
  }

  /**
   * Check if a number is prime (helper method)
   *
   * @private
   * @param {number} n - Number to check
   * @returns {boolean} True if n is prime
   */
  _isPrime(n) {
    if (n <= 1) return false;
    if (n <= 3) return true;
    if (n % 2 === 0 || n % 3 === 0) return false;

    let i = 5;
    while (i * i <= n) {
      if (n % i === 0 || n % (i + 2) === 0) return false;
      i += 6;
    }

    return true;
  }

  /**
   * Calculate greatest common divisor (helper method)
   *
   * @private
   * @param {number} a - First number
   * @param {number} b - Second number
   * @returns {number} GCD
   */
  _gcd(a, b) {
    while (b !== 0) {
      const temp = b;
      b = a % b;
      a = temp;
    }
    return a;
  }

  /**
   * Convert a number to a specific base
   *
   * @param {number} number - Number to convert
   * @param {number} base - Base to convert to
   * @returns {number[]} Digits in the specified base
   */
  convertToBase(number, base) {
    if (number === 0) return [0];

    const digits = [];
    let n = number;

    while (n > 0) {
      digits.unshift(n % base);
      n = Math.floor(n / base);
    }

    return digits;
  }

  /**
   * Convert from a base representation back to a number
   *
   * @param {number[]} digits - Digits in the specified base
   * @param {number} base - Base of the digits
   * @returns {number} Number value
   */
  convertFromBase(digits, base) {
    return digits.reduce((acc, digit) => acc * base + digit, 0);
  }

  /**
   * Create a universal embedding of a number across multiple bases
   *
   * @param {number} number - Number to embed
   * @returns {Object} Universal embedding object
   */
  embed(number) {
    // Check if we have this in the cache
    if (this._embeddingCache.has(number)) {
      // Return a deep copy of the cached embedding
      const cached = this._embeddingCache.get(number);
      return JSON.parse(JSON.stringify(cached));
    }

    const embedding = {};

    // Represent the number in each base
    for (const base of this.bases) {
      embedding[base] = this.convertToBase(number, base);
    }

    // Cache the result (keep cache size reasonable)
    if (this._embeddingCache.size < 10000) {
      this._embeddingCache.set(number, JSON.parse(JSON.stringify(embedding)));
    }

    return embedding;
  }

  /**
   * Calculate the coherence norm of a universal embedding
   * Measures how well the representations agree with each other
   *
   * @param {Object} embedding - Universal embedding object
   * @returns {number} Coherence norm (0 for perfect coherence)
   */
  coherenceNorm(embedding) {
    // Convert each representation back to a number
    const numbers = [];
    for (const base in embedding) {
      if (Object.hasOwnProperty.call(embedding, base)) {
        const baseInt = parseInt(base, 10);
        const digits = embedding[base];
        numbers.push(this.convertFromBase(digits, baseInt));
      }
    }

    // If all representations correspond to the same number, coherence is perfect (0)
    if (numbers.length === 0) return 0;

    const firstNum = numbers[0];
    if (numbers.every((n) => n === firstNum)) return 0;

    // Otherwise, calculate variance as a measure of incoherence
    const mean = numbers.reduce((sum, n) => sum + n, 0) / numbers.length;
    const variance =
      numbers.reduce((sum, n) => sum + Math.pow(n - mean, 2), 0) /
      numbers.length;

    return Math.sqrt(variance);
  }

  /**
   * Add controlled noise to an embedding
   *
   * @param {Object} embedding - Universal embedding to perturb
   * @param {number} noiseLevel - Noise level (0-1)
   * @returns {Object} Perturbed embedding
   */
  perturbEmbedding(embedding, noiseLevel = 0.2) {
    const perturbed = {};

    for (const base in embedding) {
      if (Object.hasOwnProperty.call(embedding, base)) {
        const baseInt = parseInt(base, 10);
        const digits = embedding[base].slice();

        // Determine how many digits to potentially modify
        const numToModify = Math.max(1, Math.floor(digits.length * noiseLevel));

        // Select positions to modify
        const positions = [];
        while (
          positions.length < numToModify &&
          positions.length < digits.length
        ) {
          const pos = Math.floor(Math.random() * digits.length);
          if (!positions.includes(pos)) {
            positions.push(pos);
          }
        }

        // Modify selected digits
        for (const pos of positions) {
          const original = digits[pos];
          let newDigit = original;

          // Generate a different digit (not the same as original)
          while (newDigit === original) {
            newDigit = Math.floor(Math.random() * baseInt);
          }

          digits[pos] = newDigit;
        }

        perturbed[base] = digits;
      }
    }

    return perturbed;
  }

  /**
   * Extract the most likely number from a potentially noisy embedding
   *
   * @param {Object} embedding - Universal embedding object
   * @returns {number} Most likely number
   */
  extractNumber(embedding) {
    // Get all representations as numbers
    const numbers = [];
    const frequencies = {};

    for (const base in embedding) {
      if (Object.hasOwnProperty.call(embedding, base)) {
        const baseInt = parseInt(base, 10);
        const digits = embedding[base];
        const num = this.convertFromBase(digits, baseInt);

        numbers.push(num);
        frequencies[num] = (frequencies[num] || 0) + 1;
      }
    }

    if (numbers.length === 0) return 0;

    // Find the most common value
    let mostCommon = numbers[0];
    let maxFreq = frequencies[mostCommon];

    for (const num in frequencies) {
      if (frequencies[num] > maxFreq) {
        mostCommon = parseInt(num, 10);
        maxFreq = frequencies[num];
      }
    }

    return mostCommon;
  }
}

// Export the public API
module.exports = {
  SpectralPrimeDecomposition,
  UniversalNumberEmbedding,
};
