/**
 * PrimeOS Math Module Test
 * Tests the matrix and vector modules after refactoring
 */

const Prime = require("./src/index");

// Check basic module loading
console.log("Math module diagnostics:");
console.log("- Prime.Math exists:", !!Prime.Math);
console.log("- Prime.Math.Vector exists:", !!Prime.Math.Vector);
console.log("- Prime.Math.Matrix exists:", !!Prime.Math.Matrix);
console.log();

// Test Vector operations
console.log("Testing Vector operations:");
try {
  // Create a vector
  const v1 = Prime.Math.Vector.create(3, 1);
  console.log("Vector creation successful:", v1);

  // Create another vector
  const v2 = Prime.Math.Vector.create(3, 2);
  console.log("Second vector created:", v2);

  // Test operations
  const v3 = Prime.Math.Vector.add(v1, v2);
  console.log("Vector addition:", v3);

  const v4 = Prime.Math.Vector.scale(v1, 2);
  console.log("Vector scaling:", v4);

  const dot = Prime.Math.Vector.dot(v1, v2);
  console.log("Vector dot product:", dot);
  console.log("Vector operations successful!");
} catch (error) {
  console.error("Vector operations failed:", error.message);
  console.error(error.stack);
}
console.log();

// Test Matrix operations
console.log("Testing Matrix operations:");
try {
  // Create a matrix
  const m1 = Prime.Math.Matrix.create(2, 2, 1);
  console.log("Matrix creation successful:", m1);

  // Create another matrix
  const m2 = Prime.Math.Matrix.create(2, 2, 2);
  console.log("Second matrix created:", m2);

  // Test operations
  const m3 = Prime.Math.Matrix.add(m1, m2);
  console.log("Matrix addition:", m3);

  const m4 = Prime.Math.Matrix.scale(m1, 2);
  console.log("Matrix scaling:", m4);

  const m5 = Prime.Math.Matrix.multiply(m1, m2);
  console.log("Matrix multiplication:", m5);
  console.log("Matrix operations successful!");
} catch (error) {
  console.error("Matrix operations failed:", error.message);
  console.error(error.stack);
}
console.log();

// Test advanced operations
console.log("Testing advanced operations:");
try {
  // Create entities
  const v = Prime.Math.Vector.create(3, 1);
  const m = Prime.Math.Matrix.create(3, 3, 1);

  // Test Vector Advanced
  const v_norm = Prime.Math.Vector.normalize(v);
  console.log("Vector normalization:", v_norm);

  const vectors = [
    Prime.Math.Vector.create(3, 1),
    Prime.Math.Vector.create(3, 2),
    Prime.Math.Vector.create(3, 3),
  ];

  if (Prime.Math.VectorAdvanced) {
    const avg = Prime.Math.VectorAdvanced.average(vectors);
    console.log("Vector average:", avg);
  } else {
    console.log("VectorAdvanced not directly accessible (lazy loading)");
  }

  // Test Matrix Advanced
  const det = Prime.Math.Matrix.determinant(m);
  console.log("Matrix determinant:", det);

  // Create a specific matrix for inversion
  const invertible = Prime.Math.Matrix.create(2, 2);
  invertible[0][0] = 4;
  invertible[0][1] = 7;
  invertible[1][0] = 2;
  invertible[1][1] = 6;

  const inv = Prime.Math.Matrix.inverse(invertible);
  console.log("Matrix inverse:", inv);

  console.log("Advanced operations successful!");
} catch (error) {
  console.error("Advanced operations failed:", error.message);
  console.error(error.stack);
}
