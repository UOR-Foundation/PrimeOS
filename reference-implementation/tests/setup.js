/**
 * PrimeOS Reference Implementation - Test Setup
 * 
 * Global setup for Jest tests. This is imported by Jest before any tests run.
 */

// Add a simple test to ensure Jest doesn't complain about missing tests
// This trick allows us to use this file purely for setup without Jest errors
test('Jest initialized with setup config', () => {
  expect(true).toBe(true);
});

// Mock setTimeout and clearTimeout for testing
global.setTimeout = jest.fn((fn) => {
  // Don't actually call the function during tests
  return 123; // Return dummy timeout ID
});

global.clearTimeout = jest.fn();

// Add TextEncoder and TextDecoder polyfills for Node.js environment
if (typeof TextEncoder === 'undefined') {
  const { TextEncoder, TextDecoder } = require('util');
  global.TextEncoder = TextEncoder;
  global.TextDecoder = TextDecoder;
}

// Mock crypto API for browser-compatibility tests
if (typeof crypto === 'undefined' || !crypto.subtle) {
  const nodeCrypto = require('crypto');
  
  global.crypto = {
    getRandomValues: function(buffer) {
      return nodeCrypto.randomFillSync(buffer);
    },
    subtle: {
      importKey: jest.fn().mockResolvedValue('mock-imported-key'),
      deriveKey: jest.fn().mockResolvedValue('mock-derived-key'),
      generateKey: jest.fn().mockResolvedValue('mock-generated-key'),
      encrypt: jest.fn().mockResolvedValue(new Uint8Array([1, 2, 3, 4])),
      decrypt: jest.fn().mockResolvedValue(new Uint8Array([1, 2, 3, 4]))
    }
  };
}

// Add mock localStorage for browser-compatibility tests
if (typeof localStorage === 'undefined') {
  class LocalStorageMock {
    constructor() {
      this.store = {};
      this.length = 0;
    }

    key(n) {
      return Object.keys(this.store)[n];
    }

    getItem(key) {
      return this.store[key] || null;
    }

    setItem(key, value) {
      this.store[key] = String(value);
      this.length = Object.keys(this.store).length;
    }

    removeItem(key) {
      delete this.store[key];
      this.length = Object.keys(this.store).length;
    }

    clear() {
      this.store = {};
      this.length = 0;
    }
  }

  global.localStorage = new LocalStorageMock();
}

// Add Prime error classes for testing
if (typeof Prime === 'undefined') {
  global.Prime = {
    PrimeError: class PrimeError extends Error {
      constructor(message, options = {}) {
        super(message);
        this.name = 'PrimeError';
        this.timestamp = new Date();
        this.code = options.code || 'GENERIC_ERROR';
        this.context = options.context || {};
      }
    },
    CoherenceViolationError: class CoherenceViolationError extends Error {
      constructor(message, constraint, magnitude, options = {}) {
        super(message);
        this.name = 'CoherenceViolationError';
        this.timestamp = new Date();
        this.code = options.code || 'COHERENCE_VIOLATION';
        this.constraint = constraint;
        this.magnitude = magnitude;
        this.context = options.context || { constraint, magnitude };
      }
    },
    CoherenceError: class CoherenceError extends Error {
      constructor(message, options = {}) {
        super(message);
        this.name = 'CoherenceError';
        this.timestamp = new Date();
        this.code = options.code || 'COHERENCE_ERROR';
        this.context = options.context || {};
      }
    },
    ValidationError: class ValidationError extends Error {
      constructor(message, options = {}) {
        super(message);
        this.name = 'ValidationError';
        this.timestamp = new Date();
        this.code = options.code || 'VALIDATION_ERROR';
        this.context = options.context || {};
      }
    }
  };
}


// Mock console methods for cleaner test output
global.console = {
  ...console,
  log: jest.fn(),
  warn: jest.fn(),
  error: jest.fn(),
  info: jest.fn(),
  debug: jest.fn()
};

// Add a helper to reset mocks between tests
beforeEach(() => {
  jest.clearAllMocks();
});

// Custom matchers
expect.extend({
  toBeValidComponent(received) {
    const pass = received && 
      typeof received === 'object' &&
      typeof received.id === 'string' &&
      received.variant !== undefined &&
      received.invariant !== undefined;
    
    if (pass) {
      return {
        message: () => `expected ${received} not to be a valid component`,
        pass: true
      };
    } else {
      return {
        message: () => `expected ${received} to be a valid component with id, variant, and invariant properties`,
        pass: false
      };
    }
  }
});