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