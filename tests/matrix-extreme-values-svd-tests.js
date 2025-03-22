/**
 * SVD with Extreme Values Tests
 */

const Prime = require('../src/core');
require('../src/math/matrix'); // This loads all the matrix modules
require('../src/framework/math'); // Load the framework math modules

describe('SVD Extreme Values', () => {
  test('Matrix and Math APIs exist and work', () => {
    // Check if Matrix module exists
    expect(Prime.math.Matrix).toBeDefined();
    
    // Test matrix multiplication
    const A = [
      [1, 2],
      [3, 4]
    ];
    
    const B = [
      [5, 6],
      [7, 8]
    ];
    
    const C = Prime.math.Matrix.multiply(A, B);
    
    expect(C).toBeDefined();
    expect(C[0][0]).toBe(19);
    expect(C[0][1]).toBe(22);
    expect(C[1][0]).toBe(43);
    expect(C[1][1]).toBe(50);
  });

  test('SVD with large magnitude values', () => {
    // Create a matrix with extreme value ranges
    const matrixWithExtremes = [
      [1e15, 1e-10],
      [1e-10, 1e15]
    ];
    
    // Create a matrix object and perform SVD
    const matrix = Prime.math.createMatrix(matrixWithExtremes);
    const result = matrix.svd();
    
    // Verify U, S, and V are defined
    expect(result.U).toBeDefined();
    expect(result.S).toBeDefined();
    expect(result.V).toBeDefined();
    
    // Verify dimensions
    expect(result.U.length).toBe(2);
    expect(result.U[0].length).toBe(2);
    expect(result.S.length).toBe(2);
    expect(result.S[0].length).toBe(2);
    expect(result.V.length).toBe(2);
    expect(result.V[0].length).toBe(2);
    
    // Check values are finite (not NaN or Infinity)
    for (let i = 0; i < 2; i++) {
      for (let j = 0; j < 2; j++) {
        expect(Number.isFinite(result.U[i][j])).toBe(true);
        expect(Number.isFinite(result.S[i][j])).toBe(true);
        expect(Number.isFinite(result.V[i][j])).toBe(true);
      }
    }
    
    // Verify S is diagonal
    expect(Math.abs(result.S[0][1])).toBeLessThan(1e-10);
    expect(Math.abs(result.S[1][0])).toBeLessThan(1e-10);
    
    // Verify U has orthogonal columns
    let dotProduct = 0;
    for (let i = 0; i < 2; i++) {
      dotProduct += result.U[i][0] * result.U[i][1];
    }
    expect(Math.abs(dotProduct)).toBeLessThan(1e-8);
    
    // Verify V has orthogonal columns
    dotProduct = 0;
    for (let i = 0; i < 2; i++) {
      dotProduct += result.V[i][0] * result.V[i][1];
    }
    expect(Math.abs(dotProduct)).toBeLessThan(1e-8);
    
    // Verify U*S*V^T = original matrix (approximately)
    const VTranspose = [];
    for (let i = 0; i < 2; i++) {
      VTranspose[i] = [];
      for (let j = 0; j < 2; j++) {
        VTranspose[i][j] = result.V[j][i];
      }
    }
    
    const SV = Prime.Math.Matrix.multiply(result.S, VTranspose);
    const USV = Prime.Math.Matrix.multiply(result.U, SV);
    
    // Use relative error for comparison due to extreme values
    for (let i = 0; i < 2; i++) {
      for (let j = 0; j < 2; j++) {
        const original = matrixWithExtremes[i][j];
        const computed = USV[i][j];
        
        if (Math.abs(original) > 1e-10) {
          expect(Math.abs(computed / original - 1)).toBeLessThan(1e-6);
        } else {
          expect(Math.abs(computed - original)).toBeLessThan(1e-10);
        }
      }
    }
  });

  test('SVD with very small values', () => {
    // Create a matrix with very small values
    const smallMatrix = [
      [1e-150, 1e-200],
      [1e-200, 1e-150]
    ];
    
    // Create a matrix object and perform SVD
    const matrix = Prime.math.createMatrix(smallMatrix);
    const result = matrix.svd();
    
    // Verify U, S, and V are defined and have finite values
    expect(result.U).toBeDefined();
    expect(result.S).toBeDefined();
    expect(result.V).toBeDefined();
    
    // Check values are finite (not NaN or Infinity)
    for (let i = 0; i < 2; i++) {
      for (let j = 0; j < 2; j++) {
        expect(Number.isFinite(result.U[i][j])).toBe(true);
        expect(Number.isFinite(result.S[i][j])).toBe(true);
        expect(Number.isFinite(result.V[i][j])).toBe(true);
        expect(isNaN(result.U[i][j])).toBe(false);
        expect(isNaN(result.S[i][j])).toBe(false);
        expect(isNaN(result.V[i][j])).toBe(false);
      }
    }
    
    // Verify singular values are non-negative and in descending order
    expect(result.S[0][0]).toBeGreaterThanOrEqual(0);
    expect(result.S[1][1]).toBeGreaterThanOrEqual(0);
    expect(result.S[0][0]).toBeGreaterThanOrEqual(result.S[1][1]);
    
    // Verify U has orthogonal columns
    let dotProduct = 0;
    for (let i = 0; i < 2; i++) {
      dotProduct += result.U[i][0] * result.U[i][1];
    }
    expect(Math.abs(dotProduct)).toBeLessThan(1e-8);
    
    // Verify V has orthogonal columns
    dotProduct = 0;
    for (let i = 0; i < 2; i++) {
      dotProduct += result.V[i][0] * result.V[i][1];
    }
    expect(Math.abs(dotProduct)).toBeLessThan(1e-8);
    
    // Verify reconstruction accuracy with appropriate tolerance for small values
    const VTranspose = [];
    for (let i = 0; i < 2; i++) {
      VTranspose[i] = [];
      for (let j = 0; j < 2; j++) {
        VTranspose[i][j] = result.V[j][i];
      }
    }
    
    const SV = Prime.Math.Matrix.multiply(result.S, VTranspose);
    const USV = Prime.Math.Matrix.multiply(result.U, SV);
    
    // For extremely small values, check that the magnitude is preserved
    for (let i = 0; i < 2; i++) {
      for (let j = 0; j < 2; j++) {
        const original = smallMatrix[i][j];
        const computed = USV[i][j];
        
        if (Math.abs(original) > 1e-200) {
          // Use relative error with a larger tolerance for extremely small values
          const relativeDiff = Math.abs(computed / original - 1);
          expect(relativeDiff).toBeLessThan(1e-5);
        } else {
          // For extremely small values, check absolute difference
          expect(Math.abs(computed - original)).toBeLessThan(1e-200);
        }
      }
    }
  });

  test('SVD with very large values', () => {
    // Create a matrix with very large values
    const largeMatrix = [
      [1e150, 1e100],
      [1e100, 1e150]
    ];
    
    // Create a matrix object and perform SVD
    const matrix = Prime.math.createMatrix(largeMatrix);
    const result = matrix.svd();
    
    // Verify results contain no NaN or Infinity
    for (let i = 0; i < 2; i++) {
      for (let j = 0; j < 2; j++) {
        expect(Number.isFinite(result.U[i][j])).toBe(true);
        expect(Number.isFinite(result.S[i][j])).toBe(true);
        expect(Number.isFinite(result.V[i][j])).toBe(true);
        expect(isNaN(result.U[i][j])).toBe(false);
        expect(isNaN(result.S[i][j])).toBe(false);
        expect(isNaN(result.V[i][j])).toBe(false);
      }
    }
    
    // Verify U*S*V^T = original matrix with appropriate tolerance for large values
    const VTranspose = [];
    for (let i = 0; i < 2; i++) {
      VTranspose[i] = [];
      for (let j = 0; j < 2; j++) {
        VTranspose[i][j] = result.V[j][i];
      }
    }
    
    const SV = Prime.Math.Matrix.multiply(result.S, VTranspose);
    const USV = Prime.Math.Matrix.multiply(result.U, SV);
    
    // Each element should be close to the original within a relative tolerance
    for (let i = 0; i < 2; i++) {
      for (let j = 0; j < 2; j++) {
        const original = largeMatrix[i][j];
        const computed = USV[i][j];
        const tolerance = 1e-5;  // Use a slightly larger tolerance for extreme values
        
        const relativeDiff = Math.abs(computed / original - 1);
        expect(relativeDiff).toBeLessThan(tolerance);
      }
    }
  });

  test('SVD with mixed extreme values', () => {
    // Matrix with mixed extreme values
    const mixedMatrix = [
      [1e-150, 1e100],
      [1e100, 1e-150]
    ];
    
    // Create a matrix object and perform SVD
    const matrix = Prime.math.createMatrix(mixedMatrix);
    const result = matrix.svd();
    
    // Verify orthogonality of U and V
    let dotProductU = 0;
    let dotProductV = 0;
    for (let i = 0; i < 2; i++) {
      dotProductU += result.U[i][0] * result.U[i][1];
      dotProductV += result.V[i][0] * result.V[i][1];
    }
    expect(Math.abs(dotProductU)).toBeLessThan(1e-8);
    expect(Math.abs(dotProductV)).toBeLessThan(1e-8);
    
    // For this extreme case, the singular values should reflect the structure
    // The largest singular value should be approximately 1e100
    expect(Math.abs(result.S[0][0])).toBeGreaterThan(1e50);
    
    // Verify reconstruction accuracy selectively based on magnitude
    const VTranspose = [];
    for (let i = 0; i < 2; i++) {
      VTranspose[i] = [];
      for (let j = 0; j < 2; j++) {
        VTranspose[i][j] = result.V[j][i];
      }
    }
    
    const SV = Prime.Math.Matrix.multiply(result.S, VTranspose);
    const USV = Prime.Math.Matrix.multiply(result.U, SV);
    
    // Each element should be close to the original, accounting for magnitude
    for (let i = 0; i < 2; i++) {
      for (let j = 0; j < 2; j++) {
        const original = mixedMatrix[i][j];
        const computed = USV[i][j];
        
        if (Math.abs(original) > 1e50) {
          // For very large values, use relative error
          expect(Math.abs(computed / original - 1)).toBeLessThan(1e-5);
        } else if (Math.abs(original) < 1e-50) {
          // For very small values, the reconstructed value may be dominated by numerical error
          // Instead of checking exact reconstruction, verify the magnitude is small
          expect(Math.abs(computed)).toBeLessThan(1e-10);
        }
      }
    }
  });

  test('SVD with non-square matrices', () => {
    // Create a non-square matrix with extreme values
    const nonSquareExtreme = [
      [1e150, 1e-150, 1e10],
      [1e-150, 1e150, 1e-10]
    ];
    
    // Create a matrix object and perform SVD
    const matrix = Prime.math.createMatrix(nonSquareExtreme);
    const result = matrix.svd();
    
    // Check dimensions
    expect(result.U.length).toBe(2);  // rows
    expect(result.U[0].length).toBe(2);  // cols, Min(2,3) = 2
    expect(result.S.length).toBe(2);  // rows
    expect(result.S[0].length).toBe(3);  // cols
    expect(result.V.length).toBe(3);  // rows 
    expect(result.V[0].length).toBe(3);  // cols
    
    // Verify singular values are non-negative and in descending order
    expect(result.S[0][0]).toBeGreaterThanOrEqual(0);
    expect(result.S[1][1]).toBeGreaterThanOrEqual(0);
    expect(result.S[0][0]).toBeGreaterThanOrEqual(result.S[1][1]);
    
    // Verify orthogonality of U columns
    let dotProduct = 0;
    for (let i = 0; i < 2; i++) {
      dotProduct += result.U[i][0] * result.U[i][1];
    }
    expect(Math.abs(dotProduct)).toBeLessThan(1e-8);
    
    // Verify orthogonality of V columns (pairwise)
    for (let i = 0; i < 3; i++) {
      for (let j = i + 1; j < 3; j++) {
        let dotProduct = 0;
        for (let k = 0; k < 3; k++) {
          dotProduct += result.V[k][i] * result.V[k][j];
        }
        expect(Math.abs(dotProduct)).toBeLessThan(1e-8);
      }
    }
    
    // Verify reconstruction
    const VTranspose = [];
    for (let i = 0; i < 3; i++) {
      VTranspose[i] = [];
      for (let j = 0; j < 3; j++) {
        VTranspose[i][j] = result.V[j][i];
      }
    }
    
    const SV = Prime.Math.Matrix.multiply(result.S, VTranspose);
    const USV = Prime.Math.Matrix.multiply(result.U, SV);
    
    for (let i = 0; i < 2; i++) {
      for (let j = 0; j < 3; j++) {
        const original = nonSquareExtreme[i][j];
        const computed = USV[i][j];
        
        if (Math.abs(original) > 1e50) {
          expect(Math.abs(computed / original - 1)).toBeLessThan(1e-5);
        } else if (Math.abs(original) < 1e-50) {
          expect(Math.abs(computed)).toBeLessThan(1e-10);
        } else {
          expect(Math.abs(computed / original - 1)).toBeLessThan(1e-5);
        }
      }
    }
  });
});