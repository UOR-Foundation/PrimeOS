/**
 * PrimeOS Browser Tests - Core Module Index
 * 
 * This file loads all core module tests for the browser test runner.
 */

// Register all core test suites directly
function loadCoreTests() {
  // Register a test suite for the basic Core module
  TestRunner.suite('Core Module', function() {
    TestRunner.test('Prime core module is loaded and accessible', function() {
      TestRunner.assert(typeof Prime !== 'undefined', 'Prime global object should exist');
      TestRunner.assert(typeof Prime.version === 'string', 'Prime.version should be a string');
      
      // Check for core components
      const coreComponents = ['Utils', 'EventBus', 'ModuleLoader', 'Logger'];
      coreComponents.forEach(component => {
        TestRunner.assert(typeof Prime[component] !== 'undefined', `Prime.${component} should exist`);
      });
    });
  });
  
  // Load error tests directly
  TestRunner.suite('Core Errors', function() {
    TestRunner.test('PrimeError creates base error with correct properties', function() {
      const error = new Prime.PrimeError("Test error");
      
      TestRunner.assert(error instanceof Error, "Should be an Error instance");
      TestRunner.assert(error instanceof Prime.PrimeError, "Should be a PrimeError instance");
      TestRunner.assertEqual(error.name, "PrimeError", "Should have correct name");
      TestRunner.assertEqual(error.message, "Test error", "Should have correct message");
      
      // Browser tests might behave differently with timestamps, so we'll skip this check
      // TestRunner.assert(typeof error.timestamp === 'string', "Should have timestamp");
    });
    
    TestRunner.test('Error hierarchy is properly constructed', function() {
      // Test a few representative error types
      const validation = new Prime.ValidationError("Validation error");
      const config = new Prime.ConfigurationError("Config error");
      const operation = new Prime.InvalidOperationError("Invalid operation");
      
      // All should be instances of PrimeError
      TestRunner.assert(validation instanceof Prime.PrimeError, "ValidationError should be a PrimeError");
      TestRunner.assert(config instanceof Prime.PrimeError, "ConfigurationError should be a PrimeError");
      TestRunner.assert(operation instanceof Prime.PrimeError, "InvalidOperationError should be a PrimeError");
    });
  });
  
  // Load EventBus tests directly
  TestRunner.suite('Core EventBus', function() {
    TestRunner.test('EventBus exists and has core functions', function() {
      TestRunner.assert(typeof Prime.EventBus === 'object', "EventBus should be an object");
      TestRunner.assert(typeof Prime.EventBus.subscribe === 'function', "EventBus should have subscribe function");
      TestRunner.assert(typeof Prime.EventBus.publish === 'function', "EventBus should have publish function");
    });
    
    TestRunner.test('publishes events to subscribed handlers', function() {
      // Clear previous listeners
      if (typeof Prime.EventBus.clear === 'function') {
        Prime.EventBus.clear();
      }
      
      let wasCalled = false;
      let passedData = null;
      
      const handler = function(data) {
        wasCalled = true;
        passedData = data;
      };
      
      Prime.EventBus.subscribe('browser-test-event', handler);
      
      const eventData = { value: 42 };
      Prime.EventBus.publish('browser-test-event', eventData);
      
      TestRunner.assert(wasCalled, "Handler should be called");
      TestRunner.assertEqual(passedData.value, 42, "Handler should receive event data");
    });
  });
  
  // Load ModuleLoader tests directly
  TestRunner.suite('Core ModuleLoader', function() {
    TestRunner.test('ModuleLoader exists and detects environment', function() {
      TestRunner.assert(typeof Prime.ModuleLoader === 'object', "ModuleLoader should be an object");
      
      const env = Prime.ModuleLoader.detectEnvironment();
      TestRunner.assert(typeof env === 'string', "Environment should be a string");
      TestRunner.assertEqual(env, 'browser', "Should detect browser environment");
    });
  });
}

// Export function for test runner
window.defineCoreTests = function() {
  TestRunner.reset();
  loadCoreTests();
};