/**
 * PrimeOS Browser Tests - EventBus
 * 
 * Tests for the EventBus component in the core module.
 */

// Register tests with TestRunner
TestRunner.suite('Core EventBus', function() {
  // Clear event bus before each test
  let resetBefore = {};
  
  // Setup function to run before each test
  function beforeTest() {
    // Save original EventBus to restore after tests
    if (Object.keys(resetBefore).length === 0) {
      if (Prime.EventBus) {
        resetBefore = {...Prime.EventBus};
      }
    }
    
    // Clear EventBus for clean tests
    if (Prime.EventBus && typeof Prime.EventBus.clear === 'function') {
      Prime.EventBus.clear();
    }
  }
  
  // Reset EventBus after all tests
  function afterTests() {
    if (Object.keys(resetBefore).length > 0 && Prime.EventBus) {
      // This is a simple reset approach - a more robust version would
      // preserve the original object reference and prototype chain
      Prime.EventBus.clear();
    }
  }

  TestRunner.test('subscribe returns an unsubscribe function', function() {
    beforeTest();
    
    const handler = function() {};
    const unsubscribe = Prime.EventBus.subscribe('test-event', handler);
    
    TestRunner.assert(typeof unsubscribe === 'function', "subscribe should return a function");
    
    // Clean up
    if (typeof unsubscribe === 'function') {
      unsubscribe();
    }
  });
  
  TestRunner.test('publishes events to subscribed handlers', function() {
    beforeTest();
    
    let wasCalled = false;
    let passedData = null;
    
    const handler = function(data) {
      wasCalled = true;
      passedData = data;
    };
    
    Prime.EventBus.subscribe('test-event', handler);
    
    const eventData = { value: 42 };
    Prime.EventBus.publish('test-event', eventData);
    
    TestRunner.assert(wasCalled, "Handler should be called");
    TestRunner.assertEqual(passedData, eventData, "Handler should receive event data");
  });
  
  TestRunner.test('allows multiple handlers for the same event', function() {
    beforeTest();
    
    let handler1Called = false;
    let handler2Called = false;
    
    const handler1 = function() { handler1Called = true; };
    const handler2 = function() { handler2Called = true; };
    
    Prime.EventBus.subscribe('test-event', handler1);
    Prime.EventBus.subscribe('test-event', handler2);
    
    Prime.EventBus.publish('test-event', { value: 'test' });
    
    TestRunner.assert(handler1Called, "First handler should be called");
    TestRunner.assert(handler2Called, "Second handler should be called");
  });
  
  TestRunner.test('only calls handlers for the published event', function() {
    beforeTest();
    
    let handler1Called = false;
    let handler2Called = false;
    
    const handler1 = function() { handler1Called = true; };
    const handler2 = function() { handler2Called = true; };
    
    Prime.EventBus.subscribe('event1', handler1);
    Prime.EventBus.subscribe('event2', handler2);
    
    Prime.EventBus.publish('event1', {});
    
    TestRunner.assert(handler1Called, "Handler for event1 should be called");
    TestRunner.assert(!handler2Called, "Handler for event2 should not be called");
  });
  
  TestRunner.test('unsubscribe stops handler from receiving events', function() {
    beforeTest();
    
    let callCount = 0;
    const handler = function() { callCount++; };
    
    // Store the handler reference for unsubscribing later
    Prime.EventBus.subscribe('test-event', handler);
    
    // First publish should be received
    Prime.EventBus.publish('test-event', { value: 1 });
    TestRunner.assertEqual(callCount, 1, "Handler should be called once");
    
    // Unsubscribe - use the same function reference
    Prime.EventBus.unsubscribe('test-event', handler);
    
    // Second publish should not be received
    Prime.EventBus.publish('test-event', { value: 2 });
    TestRunner.assertEqual(callCount, 1, "Handler should not be called after unsubscribe");
  });
  
  TestRunner.test('unsubscribe returns true if handler was found', function() {
    beforeTest();
    
    const handler = function() {};
    Prime.EventBus.subscribe('test-event', handler);
    
    const result = Prime.EventBus.unsubscribe('test-event', handler);
    TestRunner.assertEqual(result, true, "unsubscribe should return true when handler is found");
  });
  
  TestRunner.test('unsubscribe returns false if handler was not found', function() {
    beforeTest();
    
    const handler = function() {};
    // Not subscribing the handler
    
    const result = Prime.EventBus.unsubscribe('test-event', handler);
    TestRunner.assertEqual(result, false, "unsubscribe should return false when handler is not found");
  });
  
  TestRunner.test('clear removes all handlers for specific event', function() {
    beforeTest();
    
    let handler1Called = false;
    let handler2Called = false;
    
    const handler1 = function() { handler1Called = true; };
    const handler2 = function() { handler2Called = true; };
    
    Prime.EventBus.subscribe('event1', handler1);
    Prime.EventBus.subscribe('event2', handler2);
    
    Prime.EventBus.clear('event1');
    
    Prime.EventBus.publish('event1', {});
    Prime.EventBus.publish('event2', {});
    
    TestRunner.assert(!handler1Called, "Handler for cleared event should not be called");
    TestRunner.assert(handler2Called, "Handler for other event should still be called");
  });
  
  TestRunner.test('clear without event name removes all handlers', function() {
    beforeTest();
    
    let handler1Called = false;
    let handler2Called = false;
    
    const handler1 = function() { handler1Called = true; };
    const handler2 = function() { handler2Called = true; };
    
    Prime.EventBus.subscribe('event1', handler1);
    Prime.EventBus.subscribe('event2', handler2);
    
    Prime.EventBus.clear();
    
    Prime.EventBus.publish('event1', {});
    Prime.EventBus.publish('event2', {});
    
    TestRunner.assert(!handler1Called, "Handler should not be called after clear");
    TestRunner.assert(!handler2Called, "Handler should not be called after clear");
  });
  
  TestRunner.test('errors in handlers do not affect other handlers', function() {
    beforeTest();
    
    let normalHandlerCalled = false;
    
    // Create a handler that will throw an error
    const errorHandler = function() {
      throw new Error('Handler error');
    };
    
    const normalHandler = function() {
      normalHandlerCalled = true;
    };
    
    Prime.EventBus.subscribe('test-event', errorHandler);
    Prime.EventBus.subscribe('test-event', normalHandler);
    
    // This should not throw despite error in first handler
    Prime.EventBus.publish('test-event', {});
    
    TestRunner.assert(normalHandlerCalled, "Normal handler should still be called despite error");
  });
  
  // Run after all tests
  afterTests();
});