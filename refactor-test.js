/**
 * PrimeOS Refactoring Test
 * 
 * This file tests the refactored modules to ensure they work correctly.
 * Run with: node refactor-test.js
 */

// Import the refactored Prime object
const Prime = require('./src/core');
require('./src/math');

console.log('Testing refactored PrimeOS modules...');

// Test Core modules
console.log('\n--- Testing Core Modules ---');
console.log('Prime version:', Prime.version);
console.log('Utils.isObject({}):', Prime.Utils.isObject({}));
console.log('Utils.uuid() generates UUID:', !!Prime.Utils.uuid());

// Test simple error creation
try {
  throw new Prime.ValidationError('Test validation error');
} catch (e) {
  console.log('Error test passed:', e.name === 'ValidationError');
}

// Test Event Bus
console.log('\n--- Testing EventBus ---');
const unsubscribe = Prime.EventBus.subscribe('test-event', (data) => {
  console.log('Event received with data:', data);
});
Prime.EventBus.publish('test-event', { message: 'Hello World' });
unsubscribe();
console.log('EventBus unsubscribe successful');

// Test Logger
console.log('\n--- Testing Logger ---');
Prime.Logger.setLevel('INFO');
Prime.Logger.info('This is a test info message');
console.log('Logger level set to:', 
  Object.keys(Prime.Logger.levels)[Prime.Logger.currentLevel]);

// Test Math Vector operations
console.log('\n--- Testing Math Vector ---');
const v1 = [1, 2, 3];
const v2 = [4, 5, 6];
console.log('Vector add:', Prime.Math.Vector.add(v1, v2));
console.log('Vector dot product:', Prime.Math.Vector.dot(v1, v2));
console.log('Vector magnitude:', Prime.Math.Vector.magnitude(v1));

// Test Math Matrix operations
console.log('\n--- Testing Math Matrix ---');
const m1 = [[1, 2], [3, 4]];
const m2 = [[5, 6], [7, 8]];
console.log('Matrix add:', Prime.Math.Matrix.add(m1, m2));
console.log('Matrix multiply:', Prime.Math.Matrix.multiply(m1, m2));
console.log('Matrix determinant:', Prime.Math.Matrix.determinant(m1));

// Test Clifford Algebra
console.log('\n--- Testing Clifford Algebra ---');
const scalar = Prime.Math.Clifford.scalar(5);
console.log('Clifford scalar:', scalar.toString());
const vector = Prime.Math.Clifford.vector([1, 2, 3]);
console.log('Clifford vector:', vector.toString());

console.log('\nAll tests completed.');