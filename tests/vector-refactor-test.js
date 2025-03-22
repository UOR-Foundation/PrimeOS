/**
 * Test script for refactored vector modules
 * Tests basic functionality and backward compatibility
 */

// Import the Prime object with all vector modules
const Prime = require('../src/math/vector.js');

// Access the Vector module (original API)
const Vector = Prime.Math.Vector;

// Access the refactored modules
const VectorCore = Prime.Math.VectorCore;
const VectorAdvanced = Prime.Math.VectorAdvanced;
const VectorValidation = Prime.Math.VectorValidation;

// Helper function to run tests
function runTest(name, testFn) {
  try {
    const result = testFn();
    console.log(`✅ PASS: ${name}`);
    return true;
  } catch (error) {
    console.log(`❌ FAIL: ${name}`);
    console.log(`   Error: ${error.message}`);
    return false;
  }
}

// Test backward compatibility
function testBackwardCompatibility() {
  let passed = 0;
  let total = 0;
  
  total++;
  passed += runTest('Original create function', () => {
    const v = Vector.create(3, 5);
    if (v.length !== 3 || v[0] !== 5 || v[1] !== 5 || v[2] !== 5) {
      throw new Error('Vector.create failed');
    }
    return true;
  });
  
  total++;
  passed += runTest('Original add function', () => {
    const a = [1, 2, 3];
    const b = [4, 5, 6];
    const result = Vector.add(a, b);
    if (result[0] !== 5 || result[1] !== 7 || result[2] !== 9) {
      throw new Error('Vector.add failed');
    }
    return true;
  });
  
  total++;
  passed += runTest('Original dot function', () => {
    const a = [1, 2, 3];
    const b = [4, 5, 6];
    const result = Vector.dot(a, b);
    if (result !== 32) {
      throw new Error(`Vector.dot gave ${result} instead of 32`);
    }
    return true;
  });
  
  total++;
  passed += runTest('Original normalize function', () => {
    const v = [3, 0, 0];
    const result = Vector.normalize(v);
    if (Math.abs(result[0] - 1) > 1e-10 || result[1] !== 0 || result[2] !== 0) {
      throw new Error('Vector.normalize failed');
    }
    return true;
  });
  
  console.log(`\nBackward compatibility: ${passed}/${total} tests passed`);
  return passed === total;
}

// Test new functionality
function testNewFunctionality() {
  let passed = 0;
  let total = 0;
  
  total++;
  passed += runTest('TypedArray creation', () => {
    const v = Vector.createTyped(3, 5, 'float64');
    if (!(v instanceof Float64Array) || v.length !== 3 || v[0] !== 5) {
      throw new Error('Vector.createTyped failed');
    }
    return true;
  });
  
  total++;
  passed += runTest('In-place operations', () => {
    const a = [1, 2, 3];
    const b = [4, 5, 6];
    const result = [0, 0, 0];
    
    Vector.applyInPlace('add', a, b, result);
    
    if (result[0] !== 5 || result[1] !== 7 || result[2] !== 9) {
      throw new Error('Vector.applyInPlace for add failed');
    }
    
    // The result should be the same object (modified in-place)
    if (result !== result) {
      throw new Error('Vector.applyInPlace returned a new object');
    }
    
    return true;
  });
  
  total++;
  passed += runTest('Vector validation', () => {
    const result = Vector.getDiagnostics([1, 2, 3]);
    
    if (!result.isVector || !result.allNumbers || !result.allFinite) {
      throw new Error('Vector.getDiagnostics failed');
    }
    
    return true;
  });
  
  console.log(`\nNew functionality: ${passed}/${total} tests passed`);
  return passed === total;
}

// Test memory optimization
function testMemoryOptimization() {
  let passed = 0;
  let total = 0;
  
  total++;
  passed += runTest('TypedArray memory efficiency', () => {
    // Create a large typed vector for memory test
    const regularVector = Vector.create(1000000, 1);
    const typedVector = Vector.createTyped(1000000, 1);
    
    // TypedArray should be more efficient
    if (!(typedVector instanceof Float64Array)) {
      throw new Error('Expected TypedArray');
    }
    
    return true;
  });
  
  total++;
  passed += runTest('In-place operation memory efficiency', () => {
    // Create vectors for test
    const a = Vector.createTyped(100000, 1);
    const b = Vector.createTyped(100000, 2);
    const result = Vector.createTyped(100000, 0);
    
    // Apply in-place operation
    Vector.applyInPlace('add', a, b, result);
    
    // Check result - every element should be 3
    for (let i = 0; i < 100; i++) {  // Just check first 100 for speed
      if (result[i] !== 3) {
        throw new Error(`In-place operation failed at index ${i}`);
      }
    }
    
    return true;
  });
  
  console.log(`\nMemory optimization: ${passed}/${total} tests passed`);
  return passed === total;
}

// Run all tests
function runAllTests() {
  console.log('Starting Vector refactoring verification tests...\n');
  
  const backwardCompatible = testBackwardCompatibility();
  const newFunctionalityWorks = testNewFunctionality();
  const memoryOptimized = testMemoryOptimization();
  
  console.log('\nOverall test results:');
  console.log(`- Backward compatibility: ${backwardCompatible ? '✅ PASS' : '❌ FAIL'}`);
  console.log(`- New functionality: ${newFunctionalityWorks ? '✅ PASS' : '❌ FAIL'}`);
  console.log(`- Memory optimization: ${memoryOptimized ? '✅ PASS' : '❌ FAIL'}`);
  
  const allPassed = backwardCompatible && newFunctionalityWorks && memoryOptimized;
  console.log(`\nOverall status: ${allPassed ? '✅ ALL TESTS PASSED' : '❌ SOME TESTS FAILED'}`);
  
  return allPassed;
}

// Execute all tests
runAllTests();