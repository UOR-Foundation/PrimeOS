/**
 * Basic test script to verify the refactored coherence validator components
 */

// Import the coherence validator components
const { 
  CoherenceValidator,
  MathematicalCoherenceValidator,
  CoherenceConstraints,
  CoherenceNorms
} = require('../src/framework/base0/coherence-validator.js');

// Test basic functionality
function runBasicTests() {
  console.log('=== Running Basic Coherence Validator Tests ===');
  
  // Create a validator
  const validator = new CoherenceValidator();
  
  // Test numeric validation
  const numericResult = validator.validate('numeric', 42);
  console.log('Numeric validation:', numericResult.valid ? 'PASS' : 'FAIL');
  
  // Test vector validation
  const vectorResult = validator.validate('vectorSpace', [1, 2, 3]);
  console.log('Vector validation:', vectorResult.valid ? 'PASS' : 'FAIL');
  
  // Test invalid value
  const invalidNumeric = validator.validate('numeric', NaN);
  console.log('Invalid numeric validation (should fail):', !invalidNumeric.valid ? 'PASS' : 'FAIL');
  
  // Test UOR constraints validation
  const uorResult = validator.validateWithUorConstraints([1, 2, 3], 'vector');
  console.log('UOR validation:', uorResult.valid ? 'PASS' : 'FAIL');
  
  // Test stats collection
  const stats = validator.getStats();
  console.log('Stats collection:', stats.totalChecks === 4 ? 'PASS' : 'FAIL');
  
  console.log('Basic tests completed');
}

// Test mathematical coherence validator
function runMathValidatorTests() {
  console.log('\n=== Running Mathematical Coherence Validator Tests ===');
  
  // Create a validator
  const mathValidator = new MathematicalCoherenceValidator({
    numericalTolerance: 1e-12,
    strictMode: true
  });
  
  // Test numeric validation
  const numericResult = mathValidator.validateNumeric(42);
  console.log('Math numeric validation:', numericResult.valid ? 'PASS' : 'FAIL');
  
  // Test vector validation
  const vectorResult = mathValidator.validateVector([1, 2, 3]);
  console.log('Math vector validation:', vectorResult.valid ? 'PASS' : 'FAIL');
  
  // Test matrix validation
  const matrixResult = mathValidator.validateMatrix([[1, 2], [3, 4]]);
  console.log('Math matrix validation:', matrixResult.valid ? 'PASS' : 'FAIL');
  
  // Test stats
  const stats = mathValidator.getStats();
  console.log('Math validator stats collection:', stats.totalChecks === 3 ? 'PASS' : 'FAIL');
  
  console.log('Math validator tests completed');
}

// Test coherence constraints directly
function testCoherenceConstraints() {
  console.log('\n=== Testing Coherence Constraints ===');
  
  // Numeric constraints
  const isFinite = CoherenceConstraints.numeric.finiteness.validator(42);
  console.log('Numeric finiteness constraint:', isFinite ? 'PASS' : 'FAIL');
  
  // Vector constraints
  const isArrayOfNumbers = CoherenceConstraints.vectorSpace.arrayElements.validator([1, 2, 3]);
  console.log('Vector array elements constraint:', isArrayOfNumbers ? 'PASS' : 'FAIL');
  
  // Matrix constraints
  const isValidMatrix = CoherenceConstraints.matrixAlgebra.matrixStructure.validator([[1, 2], [3, 4]]);
  console.log('Matrix structure constraint:', isValidMatrix ? 'PASS' : 'FAIL');
  
  console.log('Constraint tests completed');
}

// Run all tests
function runAllTests() {
  console.log('Starting coherence validator refactoring verification tests...\n');
  
  runBasicTests();
  runMathValidatorTests();
  testCoherenceConstraints();
  
  console.log('\nAll tests completed');
}

// Execute tests
runAllTests();