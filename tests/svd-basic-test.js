/**
 * Basic SVD Test
 */

const Prime = require("../src/core");
require("../src/mathematics");
require("../src/math/matrix");
require("../src/framework/math");

// Simple debugging test
console.log("Prime:", Object.keys(Prime));
console.log("Prime.Math:", Prime.Math ? Object.keys(Prime.Math) : "undefined");
console.log("Prime.math:", Prime.math ? Object.keys(Prime.math) : "undefined");

try {
  // Test matrix creation
  const A = [
    [1, 2],
    [3, 4],
  ];

  // First try with Prime.Math
  if (Prime.Math && Prime.Math.createMatrix) {
    console.log("Using Prime.Math.createMatrix");
    const matrixMath = Prime.Math.createMatrix(A);
    console.log("Matrix created with Prime.Math:", matrixMath !== null);
    if (matrixMath.svd) {
      const svdResult = matrixMath.svd();
      console.log("SVD result with Prime.Math:", svdResult !== null);
    } else {
      console.log("No SVD method on Matrix created with Prime.Math");
    }
  }

  // Now try with Prime.math
  if (Prime.math && Prime.math.createMatrix) {
    console.log("Using Prime.math.createMatrix");
    const matrixMath = Prime.math.createMatrix(A);
    console.log("Matrix created with Prime.math:", matrixMath !== null);
    if (matrixMath.svd) {
      const svdResult = matrixMath.svd();
      console.log("SVD result with Prime.math:", svdResult !== null);
    } else {
      console.log("No SVD method on Matrix created with Prime.math");
    }
  }

  // Try Matrix directly
  if (Prime.Math && Prime.Math.Matrix) {
    console.log("Using Prime.Math.Matrix");
    if (Prime.Math.Matrix.svd) {
      const svdResult = Prime.Math.Matrix.svd(A);
      console.log("SVD result with Prime.Math.Matrix.svd:", svdResult !== null);
    } else {
      console.log("No static SVD method on Prime.Math.Matrix");
    }
  }

  // Try Matrix directly with lowercase
  if (Prime.math && Prime.math.Matrix) {
    console.log("Using Prime.math.Matrix");
    if (Prime.math.Matrix.svd) {
      const svdResult = Prime.math.Matrix.svd(A);
      console.log("SVD result with Prime.math.Matrix.svd:", svdResult !== null);
    } else {
      console.log("No static SVD method on Prime.math.Matrix");
    }
  }
} catch (error) {
  console.error("Error testing SVD:", error);
}
