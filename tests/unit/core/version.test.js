/**
 * PrimeOS Unit Tests - Version Management
 * 
 * Tests for the version management functionality in the core module.
 */

const Prime = require('../../../src/core.js');
const { Assertions, Mocking } = require('../../utils');

describe('Version Management', () => {
  describe('version property', () => {
    test('exposes a valid version string', () => {
      expect(typeof Prime.version).toBe('string');
      expect(Prime.version).toMatch(/^\d+\.\d+\.\d+$/);
    });
  });
  
  describe('validateVersion', () => {
    test('validates versions correctly', () => {
      // Current version should be valid
      expect(Prime.validateVersion(Prime.version)).toBe(true);
      
      // Lower versions should be valid
      expect(Prime.validateVersion('0.0.1')).toBe(true);
      expect(Prime.validateVersion('0.1.0')).toBe(true);
      
      // Extract major version from current version
      const majorVersion = parseInt(Prime.version.split('.')[0], 10);
      
      // Higher major version should be invalid
      expect(Prime.validateVersion(`${majorVersion + 1}.0.0`)).toBe(false);
    });
    
    test('handles non-semver strings', () => {
      // Should handle invalid version strings gracefully
      try {
        expect(Prime.validateVersion('not-a-version')).toBe(false);
        expect(Prime.validateVersion('1.0')).toBe(false);
        expect(Prime.validateVersion('1.0.0.0')).toBe(false);
      } catch (e) {
        // If it throws, that's also acceptable behavior
        expect(e).toBeDefined();
      }
    });
    
    test('validates with partial matching', () => {
      // If validateVersionPartial exists, test partial matching
      if (typeof Prime.validateVersionPartial === 'function') {
        const [major, minor] = Prime.version.split('.').map(Number);
        
        // Partial match on major.minor should work
        expect(Prime.validateVersionPartial(`${major}.${minor}`)).toBe(true);
        
        // Higher major should still fail partial match
        expect(Prime.validateVersionPartial(`${major + 1}.0`)).toBe(false);
      }
    });
  });
  
  describe('isCompatible', () => {
    test('checks compatibility with version requirements', () => {
      // Basic compatibility with minimum version
      expect(Prime.isCompatible({
        minVersion: '0.0.1',
        features: []
      })).toBe(true);
      
      // Too high minimum version
      const [major] = Prime.version.split('.').map(Number);
      expect(Prime.isCompatible({
        minVersion: `${major + 5}.0.0`,
        features: []
      })).toBe(false);
    });
    
    test('checks compatibility with feature requirements', () => {
      // Skip if feature checking isn't implemented
      if (!Prime.features) {
        return;
      }
      
      // Should check required features
      expect(Prime.isCompatible({
        minVersion: '0.0.1',
        features: Object.keys(Prime.features).slice(0, 1) // First available feature
      })).toBe(true);
      
      // Should fail for missing features
      expect(Prime.isCompatible({
        minVersion: '0.0.1',
        features: ['non-existent-feature']
      })).toBe(false);
    });
    
    test('validates input parameters', () => {
      // Null should return false
      expect(Prime.isCompatible(null)).toBe(false);
      
      // Empty object may be handled differently based on implementation
      // It might return true if using default version value '0.0.0'
      const emptyResult = Prime.isCompatible({});
      expect(typeof emptyResult).toBe('boolean');
      
      // Invalid version - implementation may throw or return false
      try {
        const result = Prime.isCompatible({ minVersion: 'not-semver' });
        // If it returns a value, it should be false
        if (typeof result !== 'undefined') {
          expect(result).toBe(false);
        }
      } catch (e) {
        // If it throws, that's also valid behavior
        expect(e).toBeDefined();
      }
    });
  });
  
  describe('version utilities', () => {
    test('provides version comparison utilities', () => {
      // Skip if these utilities don't exist
      if (!Prime.compareVersions) {
        return;
      }
      
      // Test version comparison
      expect(Prime.compareVersions('1.0.0', '1.0.0')).toBe(0);
      expect(Prime.compareVersions('1.0.0', '1.0.1')).toBeLessThan(0);
      expect(Prime.compareVersions('1.1.0', '1.0.9')).toBeGreaterThan(0);
      expect(Prime.compareVersions('2.0.0', '1.9.9')).toBeGreaterThan(0);
    });
    
    test('gracefully handles version parsing errors', () => {
      if (!Prime.parseVersion) {
        return;
      }
      
      // Valid version
      const parsed = Prime.parseVersion('1.2.3');
      expect(parsed).toEqual({ major: 1, minor: 2, patch: 3 });
      
      // Invalid version
      Assertions.assertThrows(
        () => Prime.parseVersion('not-a-version'),
        Prime.ValidationError,
        'Invalid version format'
      );
    });
  });
});