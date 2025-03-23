/**
 * PrimeOS Unit Tests - Vector Operations
 * 
 * Tests for vector operations in the Mathematics module.
 */

const Prime = require('../../../src/mathematics.js');
const { Assertions } = require('../../utils');

describe('Vector Operations', () => {
  describe('Vector Creation', () => {
    test('creates vectors from arrays', () => {
      const vector = [1, 2, 3];
      expect(vector.length).toBe(3);
      expect(vector[0]).toBe(1);
      expect(vector[1]).toBe(2);
      expect(vector[2]).toBe(3);
    });
    
    test('creates zero vectors', () => {
      const zeroVector = Prime.Math.Vector.zeros(3);
      expect(zeroVector.length).toBe(3);
      expect(zeroVector[0]).toBe(0);
      expect(zeroVector[1]).toBe(0);
      expect(zeroVector[2]).toBe(0);
    });
    
    test('creates ones vectors', () => {
      const onesVector = Prime.Math.Vector.ones(3);
      expect(onesVector.length).toBe(3);
      expect(onesVector[0]).toBe(1);
      expect(onesVector[1]).toBe(1);
      expect(onesVector[2]).toBe(1);
    });
    
    test('creates filled vectors', () => {
      const filledVector = Prime.Math.Vector.fill(3, 5);
      expect(filledVector.length).toBe(3);
      expect(filledVector[0]).toBe(5);
      expect(filledVector[1]).toBe(5);
      expect(filledVector[2]).toBe(5);
    });
  });
  
  describe('Vector Basic Operations', () => {
    test('adds vectors correctly', () => {
      const a = [1, 2, 3];
      const b = [4, 5, 6];
      
      const result = Prime.Math.Vector.add(a, b);
      expect(result).toEqual([5, 7, 9]);
    });
    
    test('subtracts vectors correctly', () => {
      const a = [4, 5, 6];
      const b = [1, 2, 3];
      
      const result = Prime.Math.Vector.subtract(a, b);
      expect(result).toEqual([3, 3, 3]);
    });
    
    test('scales vectors correctly', () => {
      const a = [1, 2, 3];
      const scalar = 2;
      
      const result = Prime.Math.Vector.scale(a, scalar);
      expect(result).toEqual([2, 4, 6]);
    });
    
    test('calculates dot product correctly', () => {
      const a = [1, 2, 3];
      const b = [4, 5, 6];
      
      const dotProduct = Prime.Math.Vector.dot(a, b);
      // 1*4 + 2*5 + 3*6 = 4 + 10 + 18 = 32
      expect(dotProduct).toBe(32);
    });
    
    test('calculates magnitude correctly', () => {
      const a = [3, 4];
      const magnitude = Prime.Math.Vector.magnitude(a);
      expect(magnitude).toBe(5);
    });
    
    test('normalizes vectors correctly', () => {
      const a = [3, 4];
      const normalized = Prime.Math.Vector.normalize(a);
      
      Assertions.assertAdaptivePrecision(normalized[0], 0.6, 1e-10);
      Assertions.assertAdaptivePrecision(normalized[1], 0.8, 1e-10);
      
      // Check that magnitude of normalized vector is 1
      const magnitude = Prime.Math.Vector.magnitude(normalized);
      Assertions.assertAdaptivePrecision(magnitude, 1, 1e-10);
    });
  });
  
  describe('Vector Cross Product', () => {
    test('calculates cross product of 3D vectors correctly', () => {
      const a = [1, 0, 0];
      const b = [0, 1, 0];
      
      const crossProduct = Prime.Math.Vector.cross(a, b);
      expect(crossProduct).toEqual([0, 0, 1]);
    });
    
    test('cross product is anticommutative', () => {
      const a = [1, 2, 3];
      const b = [4, 5, 6];
      
      const crossAB = Prime.Math.Vector.cross(a, b);
      const crossBA = Prime.Math.Vector.cross(b, a);
      
      // a × b = -(b × a)
      const negatedCrossBA = Prime.Math.Vector.scale(crossBA, -1);
      
      for (let i = 0; i < 3; i++) {
        Assertions.assertAdaptivePrecision(crossAB[i], negatedCrossBA[i], 1e-10);
      }
    });
    
    test('cross product with parallel vectors is zero', () => {
      const a = [1, 2, 3];
      const parallel = Prime.Math.Vector.scale(a, 2); // [2, 4, 6]
      
      const crossProduct = Prime.Math.Vector.cross(a, parallel);
      
      expect(Math.abs(crossProduct[0])).toBeLessThan(1e-10);
      expect(Math.abs(crossProduct[1])).toBeLessThan(1e-10);
      expect(Math.abs(crossProduct[2])).toBeLessThan(1e-10);
    });
    
    test('throws error for non-3D vectors', () => {
      const a = [1, 2];
      const b = [3, 4];
      
      expect(() => Prime.Math.Vector.cross(a, b)).toThrow();
    });
  });
  
  describe('Vector Angle', () => {
    test('calculates angle between vectors', () => {
      const a = [1, 0, 0];
      const b = [0, 1, 0];
      
      const angle = Prime.Math.Vector.angle(a, b);
      Assertions.assertAdaptivePrecision(angle, Math.PI / 2, 1e-10);
    });
    
    test('angle between parallel vectors is 0', () => {
      const a = [1, 2, 3];
      const parallel = Prime.Math.Vector.scale(a, 2);
      
      const angle = Prime.Math.Vector.angle(a, parallel);
      Assertions.assertAdaptivePrecision(angle, 0, 1e-10);
    });
    
    test('angle between antiparallel vectors is PI', () => {
      const a = [1, 2, 3];
      const antiparallel = Prime.Math.Vector.scale(a, -1);
      
      const angle = Prime.Math.Vector.angle(a, antiparallel);
      Assertions.assertAdaptivePrecision(angle, Math.PI, 1e-10);
    });
  });
  
  describe('Vector Projection', () => {
    test('calculates projection correctly', () => {
      const a = [3, 3];
      const b = [0, 1];
      
      const proj = Prime.Math.Vector.project(a, b);
      
      Assertions.assertAdaptivePrecision(proj[0], 0, 1e-10);
      Assertions.assertAdaptivePrecision(proj[1], 3, 1e-10);
    });
    
    test('projecting onto zero vector returns zero vector', () => {
      const a = [1, 2, 3];
      const zero = [0, 0, 0];
      
      expect(() => Prime.Math.Vector.project(a, zero)).toThrow();
    });
  });
  
  describe('Vector Distance', () => {
    test('calculates euclidean distance', () => {
      const a = [0, 0];
      const b = [3, 4];
      
      const distance = Prime.Math.Vector.distance(a, b);
      expect(distance).toBe(5);
    });
    
    test('calculates manhattan distance', () => {
      const a = [0, 0];
      const b = [3, 4];
      
      const distance = Prime.Math.Vector.manhattanDistance(a, b);
      expect(distance).toBe(7); // |3-0| + |4-0| = 3 + 4 = 7
    });
  });
  
  describe('Vector Extreme Values', () => {
    test('handles very large values', () => {
      const a = [1e15, 2e15];
      const b = [3e15, 4e15];
      
      const dotProduct = Prime.Math.Vector.dot(a, b);
      const expected = 1e15 * 3e15 + 2e15 * 4e15;
      Assertions.assertAdaptivePrecision(dotProduct, expected, 1e5);
    });
    
    test('handles very small values', () => {
      const a = [1e-15, 2e-15];
      const b = [3e-15, 4e-15];
      
      const dotProduct = Prime.Math.Vector.dot(a, b);
      const expected = 1e-15 * 3e-15 + 2e-15 * 4e-15;
      Assertions.assertAdaptivePrecision(dotProduct, expected, 1e-29);
    });
    
    test('avoids catastrophic cancellation in subtracting nearly identical vectors', () => {
      const epsilon = 1e-10;
      const a = [1, 2, 3];
      const b = [1 + epsilon, 2 + epsilon, 3 + epsilon];
      
      const diff = Prime.Math.Vector.subtract(b, a);
      
      for (let i = 0; i < diff.length; i++) {
        Assertions.assertAdaptivePrecision(diff[i], epsilon, 1e-15);
      }
    });
  });
});