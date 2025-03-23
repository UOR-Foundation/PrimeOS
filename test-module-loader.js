/**
 * Test script for ModuleLoader
 */

// Load PrimeOS core
const Prime = require('./src/core');

// Check if ModuleLoader is available
console.log('ModuleLoader exists:', Prime.ModuleLoader !== undefined);

// Try to register a module
try {
  Prime.ModuleLoader.register('TestModule', { test: true });
  console.log('Module registered successfully');
  console.log('TestModule exists:', Prime.TestModule !== undefined);
} catch (e) {
  console.error('Registration failed:', e.message);
}

// Try invalid registrations
try {
  Prime.ModuleLoader.register(123, {});
  console.log('Invalid registration succeeded (should fail)');
} catch (e) {
  console.log('Invalid registration failed as expected with message:', e.message);
}