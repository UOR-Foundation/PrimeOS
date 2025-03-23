/**
 * PrimeOS Unit Tests - Module Loader
 * 
 * Tests for the ModuleLoader component in the core module.
 */

const Prime = require('../../../src/core.js');
const { Assertions, Mocking } = require('../../utils');

describe('ModuleLoader', () => {
  // Cleanup any test modules after each test
  afterEach(() => {
    // Remove any test modules we added
    delete Prime.testModule;
    delete Prime.anotherTestModule;
  });
  
  describe('detectEnvironment', () => {
    test('returns environment string', () => {
      const env = Prime.ModuleLoader.detectEnvironment();
      expect(typeof env).toBe('string');
      
      // Should be 'node' in the test environment
      expect(['node', 'browser']).toContain(env);
    });
  });
  
  describe('register', () => {
    test('registers a module successfully', () => {
      const mockModule = { test: true };
      const result = Prime.ModuleLoader.register('testModule', mockModule);
      
      expect(result).toBe(true);
      expect(Prime.testModule).toBe(mockModule);
    });
    
    test('validates module name', () => {
      Assertions.assertThrows(
        () => Prime.ModuleLoader.register(123, {}),
        Prime.ValidationError,
        'register should validate module name'
      );
      
      Assertions.assertThrows(
        () => Prime.ModuleLoader.register('', {}),
        Prime.ValidationError,
        'register should validate module name is not empty'
      );
    });
    
    test('validates module object', () => {
      Assertions.assertThrows(
        () => Prime.ModuleLoader.register('testModule', 'not an object'),
        Prime.ValidationError,
        'register should validate module is an object'
      );
      
      Assertions.assertThrows(
        () => Prime.ModuleLoader.register('testModule', null),
        Prime.ValidationError,
        'register should validate module is not null'
      );
    });
    
    test('prevents overwriting existing modules', () => {
      // First registration should succeed
      Prime.ModuleLoader.register('testModule', { first: true });
      
      // Second registration should fail or return false
      try {
        const result = Prime.ModuleLoader.register('testModule', { second: true });
        expect(result).toBe(false);
      } catch (e) {
        expect(e instanceof Prime.ConfigurationError).toBe(true);
      }
      
      // Module should still be the first one
      expect(Prime.testModule.first).toBe(true);
      expect(Prime.testModule.second).toBeUndefined();
    });
    
    test('registers multiple modules', () => {
      const module1 = { id: 1 };
      const module2 = { id: 2 };
      
      Prime.ModuleLoader.register('testModule', module1);
      Prime.ModuleLoader.register('anotherTestModule', module2);
      
      expect(Prime.testModule.id).toBe(1);
      expect(Prime.anotherTestModule.id).toBe(2);
    });
  });
  
  describe('require', () => {
    // Skip if require isn't implemented
    const testRequire = () => {
      if (typeof Prime.ModuleLoader.require !== 'function') {
        return;
      }
      
      test('loads an existing module', () => {
        // Register a test module
        Prime.ModuleLoader.register('testModule', { value: 42 });
        
        // Require the module
        const module = Prime.ModuleLoader.require('testModule');
        
        expect(module).toBeDefined();
        expect(module.value).toBe(42);
      });
      
      test('throws for non-existent module', () => {
        Assertions.assertThrows(
          () => Prime.ModuleLoader.require('nonExistentModule'),
          Prime.ConfigurationError,
          'require should throw for non-existent module'
        );
      });
      
      test('validates module name', () => {
        Assertions.assertThrows(
          () => Prime.ModuleLoader.require(123),
          Prime.ValidationError,
          'require should validate module name'
        );
      });
    };
    
    // Execute the tests if require is implemented
    if (Prime.ModuleLoader.require) {
      testRequire();
    }
  });
  
  describe('unregister', () => {
    // Skip if unregister isn't implemented
    const testUnregister = () => {
      if (typeof Prime.ModuleLoader.unregister !== 'function') {
        return;
      }
      
      test('unregisters an existing module', () => {
        // Register a test module
        Prime.ModuleLoader.register('testModule', { value: 42 });
        
        // Unregister the module
        const result = Prime.ModuleLoader.unregister('testModule');
        
        expect(result).toBe(true);
        expect(Prime.testModule).toBeUndefined();
      });
      
      test('returns false for non-existent module', () => {
        const result = Prime.ModuleLoader.unregister('nonExistentModule');
        expect(result).toBe(false);
      });
      
      test('validates module name', () => {
        Assertions.assertThrows(
          () => Prime.ModuleLoader.unregister(123),
          Prime.ValidationError,
          'unregister should validate module name'
        );
      });
    };
    
    // Execute the tests if unregister is implemented
    if (Prime.ModuleLoader.unregister) {
      testUnregister();
    }
  });
  
  describe('getModules', () => {
    // Skip if getModules isn't implemented
    const testGetModules = () => {
      if (typeof Prime.ModuleLoader.getModules !== 'function') {
        return;
      }
      
      test('returns list of registered modules', () => {
        // Register test modules
        Prime.ModuleLoader.register('testModule1', { id: 1 });
        Prime.ModuleLoader.register('testModule2', { id: 2 });
        
        const modules = Prime.ModuleLoader.getModules();
        
        expect(Array.isArray(modules)).toBe(true);
        expect(modules).toContain('testModule1');
        expect(modules).toContain('testModule2');
      });
    };
    
    // Execute the tests if getModules is implemented
    if (Prime.ModuleLoader.getModules) {
      testGetModules();
    }
  });
});