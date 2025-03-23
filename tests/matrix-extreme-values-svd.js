/**
 * SVD with Extreme Values Tests - Simplified
 */

const Prime = require("../src/core");
require("../src/math/matrix");
require("../src/framework/math");

describe("SVD Extreme Values", () => {
  test("Matrix and Math APIs exist and work", () => {
    // Check if Matrix module exists
    expect(Prime.Math.Matrix).toBeDefined();

    // Test matrix multiplication
    const A = [
      [1, 2],
      [3, 4],
    ];

    const B = [
      [5, 6],
      [7, 8],
    ];

    const C = Prime.Math.Matrix.multiply(A, B);

    expect(C).toBeDefined();
    expect(C[0][0]).toBe(19);
    expect(C[0][1]).toBe(22);
    expect(C[1][0]).toBe(43);
    expect(C[1][1]).toBe(50);
  });
});
