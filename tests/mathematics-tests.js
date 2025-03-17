/**
 * PrimeOS JavaScript Library - Mathematics Tests
 * Test suite for the mathematics.js module
 */

import { Prime } from '../src/mathematics.js';

// Simple test framework
const Test = {
  passed: 0,
  failed: 0,
  skipped: 0,
  
  assert: function(condition, message) {
    if (condition) {
      this.passed++;
      console.log(`✓ PASS: ${message}`);
    } else {
      this.failed++;
      console.error(`✗ FAIL: ${message}`);
    }
  },
  
  assertThrows: function(fn, errorType, message) {
    try {
      fn();
      this.failed++;
      console.error(`✗ FAIL: ${message} - Expected to throw ${errorType.name}`);
    } catch (error) {
      if (error instanceof errorType) {
        this.passed++;
        console.log(`✓ PASS: ${message}`);
      } else {
        this.failed++;
        console.error(`✗ FAIL: ${message} - Expected error of type ${errorType.name}, got ${error.constructor.name}`);
        console.error(error);
      }
    }
  },
  
  assertApproximatelyEqual: function(actual, expected, epsilon, message) {
    const isApproxEqual = Math.abs(actual - expected) < (epsilon || 1e-6);
    
    if (isApproxEqual) {
      this.passed++;
      console.log(`✓ PASS: ${message}`);
    } else {
      this.failed++;
      console.error(`✗ FAIL: ${message} - Expected approximately ${expected}, got ${actual}`);
    }
  },
  
  skip: function(message) {
    this.skipped++;
    console.warn(`○ SKIP: ${message}`);
  },
  
  run: function(name, tests) {
    console.log(`\n=== Running Test Suite: ${name} ===`);
    tests();
    console.log(`\n=== Test Summary: ${name} ===`);
    console.log(`Passed: ${this.passed}, Failed: ${this.failed}, Skipped: ${this.skipped}`);
    
    // Reset counters for next suite
    const total = this.passed + this.failed;
    const oldPassed = this.passed;
    const oldFailed = this.failed;
    const oldSkipped = this.skipped;
    this.passed = 0;
    this.failed = 0;
    this.skipped = 0;
    
    return {
      suite: name,
      passed: oldPassed,
      failed: oldFailed,
      skipped: oldSkipped,
      total: total,
      success: oldFailed === 0
    };
  }
};

// Test suites
const testResults = [];

// Test Clifford Algebra
testResults.push(Test.run("Clifford Algebra", function() {
  // Test CliffordAlgebra creation
  const Cl3 = Prime.Clifford.create({ dimension: 3 });
  Test.assert(Cl3.dimension === 3, "Algebra has correct dimension");
  Test.assert(Array.isArray(Cl3.signature), "Algebra has signature array");
  Test.assert(Cl3.signature.length === 3, "Signature has correct length");
  Test.assert(Array.isArray(Cl3.basis), "Algebra has basis array");
  
  // Test validation on creation
  Test.assertThrows(
    () => Prime.Clifford.create({ dimension: -1 }),
    Prime.ValidationError,
    "create throws for negative dimension"
  );
  
  Test.assertThrows(
    () => Prime.Clifford.create({ dimension: 3, signature: [1, 1] }),
    Prime.ValidationError,
    "create throws for mismatched signature length"
  );
  
  // Test creating multivectors
  const scalar = Cl3.scalar(5);
  Test.assert(Prime.Clifford.isMultivector(scalar), "scalar creates a multivector");
  Test.assert(scalar.components[0] && scalar.components[0]["1"] === 5, "scalar has correct value");
  
  const vector = Cl3.vector([1, 2, 3]);
  Test.assert(Prime.Clifford.isMultivector(vector), "vector creates a multivector");
  Test.assert(vector.components[1] && vector.components[1]["e1"] === 1, "vector has correct x component");
  Test.assert(vector.components[1] && vector.components[1]["e2"] === 2, "vector has correct y component");
  Test.assert(vector.components[1] && vector.components[1]["e3"] === 3, "vector has correct z component");
  
  // Test bivector creation - using matrix form
  const bivectorMatrix = Cl3.bivector([
    [0, 1, 2],
    [0, 0, 3],
    [0, 0, 0]
  ]);
  
  Test.assert(Prime.Clifford.isMultivector(bivectorMatrix), "bivector creates a multivector");
  Test.assert(bivectorMatrix.components[2] && bivectorMatrix.components[2]["e1e2"] === 1, "bivector has correct e1^e2 component");
  Test.assert(bivectorMatrix.components[2] && bivectorMatrix.components[2]["e1e3"] === 2, "bivector has correct e1^e3 component");
  Test.assert(bivectorMatrix.components[2] && bivectorMatrix.components[2]["e2e3"] === 3, "bivector has correct e2^e3 component");
  
  // Test general multivector creation
  const general = Cl3.multivector({
    0: { "1": 1 },
    1: { "e1": 2, "e3": 3 },
    2: { "e1e2": 4 }
  });
  
  Test.assert(Prime.Clifford.isMultivector(general), "multivector creates a multivector");
  Test.assert(general.components[0] && general.components[0]["1"] === 1, "multivector has correct scalar component");
  Test.assert(general.components[1] && general.components[1]["e1"] === 2, "multivector has correct e1 component");
  Test.assert(general.components[1] && general.components[1]["e3"] === 3, "multivector has correct e3 component");
  Test.assert(general.components[2] && general.components[2]["e1e2"] === 4, "multivector has correct e1^e2 component");
  
  // Test fromArray
  const fromArray = Prime.Clifford.fromArray([4, 5, 6]);
  Test.assert(Prime.Clifford.isMultivector(fromArray), "fromArray creates a multivector");
  Test.assert(fromArray.components[1] && fromArray.components[1]["e1"] === 4, "fromArray has correct x component");
  Test.assert(fromArray.components[1] && fromArray.components[1]["e2"] === 5, "fromArray has correct y component");
  Test.assert(fromArray.components[1] && fromArray.components[1]["e3"] === 6, "fromArray has correct z component");
  
  // Test type detection
  Test.assert(Prime.Clifford.isMultivector(scalar), "isMultivector detects multivectors");
  Test.assert(!Prime.Clifford.isMultivector({}), "isMultivector rejects non-multivectors");
  Test.assert(Prime.Clifford.isAlgebra(Cl3), "isAlgebra detects Clifford algebras");
  Test.assert(!Prime.Clifford.isAlgebra({}), "isAlgebra rejects non-algebras");
}));

// Test Multivector Operations
testResults.push(Test.run("Multivector Operations", function() {
  const Cl3 = Prime.Clifford.create({ dimension: 3 });
  
  // Basic scalar operations
  const s1 = Cl3.scalar(5);
  const s2 = Cl3.scalar(3);
  
  const sum = s1.add(s2);
  Test.assert(sum.components[0] && sum.components[0]["1"] === 8, "scalar addition works");
  
  const diff = s1.subtract(s2);
  Test.assert(diff.components[0] && diff.components[0]["1"] === 2, "scalar subtraction works");
  
  const scaled = s1.scale(2);
  Test.assert(scaled.components[0] && scaled.components[0]["1"] === 10, "scalar scaling works");
  
  // Basic vector operations
  const v1 = Cl3.vector([1, 2, 3]);
  const v2 = Cl3.vector([4, 5, 6]);
  
  const vSum = v1.add(v2);
  Test.assert(vSum.components[1]["e1"] === 5, "vector addition works for x");
  Test.assert(vSum.components[1]["e2"] === 7, "vector addition works for y");
  Test.assert(vSum.components[1]["e3"] === 9, "vector addition works for z");
  
  const vDiff = v1.subtract(v2);
  Test.assert(vDiff.components[1]["e1"] === -3, "vector subtraction works for x");
  Test.assert(vDiff.components[1]["e2"] === -3, "vector subtraction works for y");
  Test.assert(vDiff.components[1]["e3"] === -3, "vector subtraction works for z");
  
  const vScaled = v1.scale(2);
  Test.assert(vScaled.components[1]["e1"] === 2, "vector scaling works for x");
  Test.assert(vScaled.components[1]["e2"] === 4, "vector scaling works for y");
  Test.assert(vScaled.components[1]["e3"] === 6, "vector scaling works for z");
  
  // Geometric product
  const gp = v1.multiply(v2);
  // v1·v2 = 1*4 + 2*5 + 3*6 = 4 + 10 + 18 = 32
  // v1∧v2 = (1*5 - 2*4)e1∧e2 + (1*6 - 3*4)e1∧e3 + (2*6 - 3*5)e2∧e3
  //       = (5 - 8)e1∧e2 + (6 - 12)e1∧e3 + (12 - 15)e2∧e3
  //       = -3e1∧e2 - 6e1∧e3 - 3e2∧e3
  Test.assert(gp.components[0] && gp.components[0]["1"] === 32, "geometric product has correct scalar part");
  Test.assert(gp.components[2] && gp.components[2]["e1e2"] === -3, "geometric product has correct e1^e2 component");
  Test.assert(gp.components[2] && gp.components[2]["e1e3"] === -6, "geometric product has correct e1^e3 component");
  Test.assert(gp.components[2] && gp.components[2]["e2e3"] === -3, "geometric product has correct e2^e3 component");
  
  // Inner product (dot product for vectors)
  const dp = v1.dot(v2);
  Test.assert(dp.components[0] && dp.components[0]["1"] === 32, "dot product has correct value");
  
  // Outer product (wedge product)
  const wp = v1.wedge(v2);
  Test.assert(wp.components[2] && wp.components[2]["e1e2"] === -3, "wedge product has correct e1^e2 component");
  Test.assert(wp.components[2] && wp.components[2]["e1e3"] === -6, "wedge product has correct e1^e3 component");
  Test.assert(wp.components[2] && wp.components[2]["e2e3"] === -3, "wedge product has correct e2^e3 component");
  
  // Grade extraction
  const grade0 = gp.grade(0);
  Test.assert(grade0.components[0] && grade0.components[0]["1"] === 32, "grade(0) extracts scalar part");
  Test.assert(!grade0.components[1], "grade(0) has no vector part");
  Test.assert(!grade0.components[2], "grade(0) has no bivector part");
  
  const grade1 = Cl3.vector([1, 2, 3]).grade(1);
  Test.assert(!grade1.components[0], "grade(1) has no scalar part");
  Test.assert(grade1.components[1] && grade1.components[1]["e1"] === 1, "grade(1) extracts vector part");
  Test.assert(!grade1.components[2], "grade(1) has no bivector part");
  
  const grade2 = gp.grade(2);
  Test.assert(!grade2.components[0], "grade(2) has no scalar part");
  Test.assert(!grade2.components[1], "grade(2) has no vector part");
  Test.assert(grade2.components[2] && grade2.components[2]["e1e2"] === -3, "grade(2) extracts bivector part");
  
  // Convenience grade extractors
  const scalar = gp.scalar();
  Test.assert(scalar.components[0] && scalar.components[0]["1"] === 32, "scalar() extracts scalar part");
  
  const vector = Cl3.vector([1, 2, 3]).vector();
  Test.assert(vector.components[1] && vector.components[1]["e1"] === 1, "vector() extracts vector part");
  
  const bivector = gp.bivector();
  Test.assert(bivector.components[2] && bivector.components[2]["e1e2"] === -3, "bivector() extracts bivector part");
  
  // Reverse
  const v = Cl3.vector([1, 2, 3]);
  const b = Cl3.bivector([[0, 1, 0], [0, 0, 0], [0, 0, 0]]); // e1^e2
  
  const vRev = v.reverse();
  Test.assert(vRev.components[1] && vRev.components[1]["e1"] === 1, "reverse of vector preserves components");
  
  const bRev = b.reverse();
  Test.assert(bRev.components[2] && bRev.components[2]["e1e2"] === -1, "reverse of bivector flips sign");
  
  // Conjugate
  const vConj = v.conjugate();
  Test.assert(vConj.components[1] && vConj.components[1]["e1"] === -1, "conjugate of vector flips sign");
  
  const bConj = b.conjugate();
  Test.assert(bConj.components[2] && bConj.components[2]["e1e2"] === 1, "conjugate of bivector preserves sign");
  
  // Norm
  const norm1 = Cl3.vector([3, 4, 0]).norm();
  Test.assertApproximatelyEqual(norm1, 5, 1e-6, "norm of vector calculates Euclidean length");
  
  const norm2 = Cl3.scalar(5).norm();
  Test.assertApproximatelyEqual(norm2, 5, 1e-6, "norm of scalar is its absolute value");
  
  // Convenience methods
  Test.assert(v.isZero() === false, "isZero returns false for non-zero multivector");
  Test.assert(Cl3.scalar(0).isZero() === true, "isZero returns true for zero multivector");
  
  Test.assert(Cl3.scalar(5).isScalar() === true, "isScalar returns true for scalar");
  Test.assert(v.isScalar() === false, "isScalar returns false for vector");
  
  Test.assert(Cl3.scalar(5).scalarValue() === 5, "scalarValue returns scalar value");
  Test.assertThrows(
    () => v.scalarValue(),
    Prime.MathematicalError,
    "scalarValue throws for non-scalar"
  );
  
  // Clone
  const original = Cl3.vector([1, 2, 3]);
  const clone = original.clone();
  
  Test.assert(original !== clone, "clone creates a different object");
  Test.assert(clone.components[1]["e1"] === 1, "clone preserves components");
  
  // toArray
  const array = v.toArray();
  Test.assert(Array.isArray(array), "toArray returns an array");
  Test.assert(array.length === 3, "toArray has correct length");
  Test.assert(array[0] === 1 && array[1] === 2 && array[2] === 3, "toArray has correct values");
  
  // toString
  const str = Cl3.scalar(5).add(Cl3.vector([1, 0, 0])).toString();
  Test.assert(typeof str === 'string', "toString returns a string");
  Test.assert(str.includes('5') && str.includes('e1'), "toString includes components");
}));

// Test Lie Groups
testResults.push(Test.run("Lie Groups", function() {
  // Test SO(3) creation
  const so3 = Prime.Lie.SO(3);
  Test.assert(Prime.Lie.isGroup(so3), "SO(3) is a Lie group");
  Test.assert(so3.name === "SO(3)", "SO(3) has correct name");
  Test.assert(so3.dimension === 3, "SO(3) has correct dimension");
  Test.assert(Array.isArray(so3.generators), "SO(3) has generators");
  Test.assert(so3.generators.length === 3, "SO(3) has 3 generators");
  
  // Test generator access
  const genX = so3.generator('X');
  Test.assert(Prime.Lie.isAlgebraElement(genX), "generator returns a Lie algebra element");
  Test.assert(genX.name === 'X', "generator has correct name");
  Test.assert(Array.isArray(genX.matrix), "generator has matrix representation");
  
  // Test rotation creation
  const rot = so3.rotation([0, 0, 1], Math.PI / 2);
  Test.assert(Prime.Lie.isGroupElement(rot), "rotation returns a Lie group element");
  Test.assert(rot.group === so3, "rotation element belongs to correct group");
  Test.assert(rot.params.type === 'rotation', "rotation has correct type");
  Test.assert(Array.isArray(rot.matrix), "rotation has matrix representation");
  
  // Test applying rotation to a vector
  const vec = [1, 0, 0];
  const rotated = rot.apply(vec);
  
  Test.assert(Array.isArray(rotated), "apply returns an array for vector input");
  Test.assertApproximatelyEqual(rotated[0], 0, 1e-6, "rotation transforms x component correctly");
  Test.assertApproximatelyEqual(rotated[1], 1, 1e-6, "rotation transforms y component correctly");
  Test.assertApproximatelyEqual(rotated[2], 0, 1e-6, "rotation transforms z component correctly");
  
  // Test element multiplication
  const rot1 = so3.rotation([0, 0, 1], Math.PI / 4);
  const rot2 = so3.rotation([0, 0, 1], Math.PI / 4);
  const composed = rot1.multiply(rot2);
  
  Test.assert(Prime.Lie.isGroupElement(composed), "multiply returns a Lie group element");
  Test.assert(composed.group === so3, "product belongs to correct group");
  
  // Test the composition is correct (should be equivalent to rotation by PI/2)
  const vec2 = [1, 0, 0];
  const composedRotated = composed.apply(vec2);
  
  Test.assertApproximatelyEqual(composedRotated[0], 0, 1e-6, "composed rotation transforms x component correctly");
  Test.assertApproximatelyEqual(composedRotated[1], 1, 1e-6, "composed rotation transforms y component correctly");
  Test.assertApproximatelyEqual(composedRotated[2], 0, 1e-6, "composed rotation transforms z component correctly");
  
  // Test inversion
  const inv = rot1.invert();
  Test.assert(Prime.Lie.isGroupElement(inv), "invert returns a Lie group element");
  
  // Test multiplication by inverse should give identity (approximately)
  const prod = rot1.multiply(inv);
  
  // Identity matrix should have 1s on diagonal and 0s elsewhere
  Test.assertApproximatelyEqual(prod.matrix[0][0], 1, 1e-6, "product with inverse has 1 at [0,0]");
  Test.assertApproximatelyEqual(prod.matrix[1][1], 1, 1e-6, "product with inverse has 1 at [1,1]");
  Test.assertApproximatelyEqual(prod.matrix[2][2], 1, 1e-6, "product with inverse has 1 at [2,2]");
  Test.assertApproximatelyEqual(prod.matrix[0][1], 0, 1e-6, "product with inverse has 0 at [0,1]");
  
  // Test applying to a multivector
  const Cl3 = Prime.Clifford.create({ dimension: 3 });
  const mv = Cl3.vector([1, 0, 0]);
  
  const rotatedMv = rot.apply(mv);
  Test.assert(Prime.Clifford.isMultivector(rotatedMv), "apply returns a multivector for multivector input");
  
  // Extract the vector components to check the rotation
  const mvArray = rotatedMv.toArray();
  Test.assertApproximatelyEqual(mvArray[0], 0, 1e-6, "rotation transforms multivector x component correctly");
  Test.assertApproximatelyEqual(mvArray[1], 1, 1e-6, "rotation transforms multivector y component correctly");
  Test.assertApproximatelyEqual(mvArray[2], 0, 1e-6, "rotation transforms multivector z component correctly");
  
  // Test Lie algebra operations
  const scaledGen = genX.scale(2);
  Test.assert(Prime.Lie.isAlgebraElement(scaledGen), "scale returns a Lie algebra element");
  Test.assert(scaledGen.matrix[1][2] === -2, "scale correctly multiplies matrix elements");
  
  const genY = so3.generator('Y');
  const sum = genX.add(genY);
  Test.assert(Prime.Lie.isAlgebraElement(sum), "add returns a Lie algebra element");
  Test.assert(sum.matrix[1][2] === -1 && sum.matrix[0][2] === 1, "add correctly combines matrices");
  
  const bracket = genX.bracket(genY);
  Test.assert(Prime.Lie.isAlgebraElement(bracket), "bracket returns a Lie algebra element");
  // [X,Y] = Z in so(3)
  Test.assert(bracket.matrix[0][1] !== 0, "bracket correctly computes Lie bracket");
}));

// Test SO(3) Rotations
testResults.push(Test.run("SO(3) Rotations", function() {
  const so3 = Prime.Lie.SO(3);
  
  // Test rotation around X axis
  const rotX = so3.rotation([1, 0, 0], Math.PI / 2);
  const vecY = [0, 1, 0];
  const rotatedY = rotX.apply(vecY);
  
  Test.assertApproximatelyEqual(rotatedY[0], 0, 1e-6, "X-rotation preserves x component");
  Test.assertApproximatelyEqual(rotatedY[1], 0, 1e-6, "X-rotation maps y to z");
  Test.assertApproximatelyEqual(rotatedY[2], 1, 1e-6, "X-rotation maps y to z");
  
  // Test rotation around Y axis
  const rotY = so3.rotation([0, 1, 0], Math.PI / 2);
  const vecZ = [0, 0, 1];
  const rotatedZ = rotY.apply(vecZ);
  
  Test.assertApproximatelyEqual(rotatedZ[0], 1, 1e-6, "Y-rotation maps z to x");
  Test.assertApproximatelyEqual(rotatedZ[1], 0, 1e-6, "Y-rotation preserves y component");
  Test.assertApproximatelyEqual(rotatedZ[2], 0, 1e-6, "Y-rotation maps z to x");
  
  // Test rotation around Z axis
  const rotZ = so3.rotation([0, 0, 1], Math.PI / 2);
  const vecX = [1, 0, 0];
  const rotatedX = rotZ.apply(vecX);
  
  Test.assertApproximatelyEqual(rotatedX[0], 0, 1e-6, "Z-rotation maps x to y");
  Test.assertApproximatelyEqual(rotatedX[1], 1, 1e-6, "Z-rotation maps x to y");
  Test.assertApproximatelyEqual(rotatedX[2], 0, 1e-6, "Z-rotation preserves z component");
  
  // Test rotation around arbitrary axis
  const axis = [1, 1, 1]; // Not normalized
  const rot = so3.rotation(axis, Math.PI);
  const v = [1, 0, 0];
  const rotated = rot.apply(v);
  
  // This is a 180° rotation around [1,1,1], which maps [1,0,0] to [1/3, 2/3, -2/3]
  // after accounting for normalization of the axis to [1/√3, 1/√3, 1/√3]
  Test.assertApproximatelyEqual(rotated[0], 1/3, 1e-6, "Arbitrary rotation transforms x correctly");
  Test.assertApproximatelyEqual(rotated[1], 2/3, 1e-6, "Arbitrary rotation transforms y correctly");
  Test.assertApproximatelyEqual(rotated[2], -2/3, 1e-6, "Arbitrary rotation transforms z correctly");
  
  // Test rotation by 360° (should be identity)
  const full = so3.rotation([0, 1, 0], 2 * Math.PI);
  const v2 = [1, 2, 3];
  const rotated2 = full.apply(v2);
  
  Test.assertApproximatelyEqual(rotated2[0], 1, 1e-6, "360° rotation preserves x component");
  Test.assertApproximatelyEqual(rotated2[1], 2, 1e-6, "360° rotation preserves y component");
  Test.assertApproximatelyEqual(rotated2[2], 3, 1e-6, "360° rotation preserves z component");
  
  // Test rotation composition (rotX then rotY)
  const composed = rotX.multiply(rotY); // Remember this means apply rotY then rotX
  const v3 = [1, 0, 0];
  const result = composed.apply(v3);
  
  // rotY maps [1,0,0] to [0,0,-1], then rotX maps [0,0,-1] to [0,1,0]
  Test.assertApproximatelyEqual(result[0], 0, 1e-6, "Composed rotation transforms x correctly");
  Test.assertApproximatelyEqual(result[1], 1, 1e-6, "Composed rotation transforms y correctly");
  Test.assertApproximatelyEqual(result[2], 0, 1e-6, "Composed rotation transforms z correctly");
}));

// Output final test summary
let overallPassed = 0;
let overallFailed = 0;
let overallSkipped = 0;

console.log("\n=== OVERALL TEST SUMMARY ===");
testResults.forEach(result => {
  console.log(`${result.suite}: ${result.passed}/${result.total} passed, ${result.failed} failed, ${result.skipped} skipped`);
  overallPassed += result.passed;
  overallFailed += result.failed;
  overallSkipped += result.skipped;
});

console.log(`\nTOTAL: ${overallPassed}/${overallPassed + overallFailed} passed, ${overallFailed} failed, ${overallSkipped} skipped`);
console.log(`OVERALL STATUS: ${overallFailed === 0 ? 'SUCCESS' : 'FAILURE'}`);

// Export test results
export const testSummary = {
  suites: testResults,
  total: {
    passed: overallPassed,
    failed: overallFailed,
    skipped: overallSkipped,
    success: overallFailed === 0
  }
};