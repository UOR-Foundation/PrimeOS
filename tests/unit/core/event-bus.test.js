/**
 * PrimeOS Unit Tests - EventBus
 * 
 * Tests for the EventBus component in the core module.
 */

const Prime = require('../../../src/core.js');
const { Assertions, Mocking } = require('../../utils');

describe('EventBus', () => {
  beforeEach(() => {
    // Reset event bus for each test
    Prime.EventBus.clear();
  });

  describe('subscribe and publish', () => {
    test('subscribe returns an unsubscribe function', () => {
      const handler = jest.fn();
      const unsubscribe = Prime.EventBus.subscribe('test-event', handler);
      
      expect(typeof unsubscribe).toBe('function');
    });
    
    test('publishes events to subscribed handlers', () => {
      const handler = jest.fn();
      Prime.EventBus.subscribe('test-event', handler);
      
      const eventData = { value: 42 };
      Prime.EventBus.publish('test-event', eventData);
      
      expect(handler).toHaveBeenCalledTimes(1);
      expect(handler).toHaveBeenCalledWith(eventData);
    });
    
    test('allows multiple handlers for the same event', () => {
      const handler1 = jest.fn();
      const handler2 = jest.fn();
      
      Prime.EventBus.subscribe('test-event', handler1);
      Prime.EventBus.subscribe('test-event', handler2);
      
      Prime.EventBus.publish('test-event', { value: 'test' });
      
      expect(handler1).toHaveBeenCalledTimes(1);
      expect(handler2).toHaveBeenCalledTimes(1);
    });
    
    test('only calls handlers for the published event', () => {
      const handler1 = jest.fn();
      const handler2 = jest.fn();
      
      Prime.EventBus.subscribe('event1', handler1);
      Prime.EventBus.subscribe('event2', handler2);
      
      Prime.EventBus.publish('event1', {});
      
      expect(handler1).toHaveBeenCalledTimes(1);
      expect(handler2).not.toHaveBeenCalled();
    });
    
    test('publishes to non-existent event without errors', () => {
      // Should not throw
      expect(() => {
        Prime.EventBus.publish('non-existent-event', {});
      }).not.toThrow();
    });
  });
  
  describe('unsubscribe', () => {
    test('unsubscribe stops handler from receiving events', () => {
      const handler = jest.fn();
      const unsubscribe = Prime.EventBus.subscribe('test-event', handler);
      
      // First publish should be received
      Prime.EventBus.publish('test-event', { value: 1 });
      expect(handler).toHaveBeenCalledTimes(1);
      
      // Unsubscribe
      unsubscribe();
      
      // Second publish should not be received
      Prime.EventBus.publish('test-event', { value: 2 });
      expect(handler).toHaveBeenCalledTimes(1); // Still just 1 call
    });
    
    test('unsubscribe returns true if handler was found', () => {
      const handler = jest.fn();
      Prime.EventBus.subscribe('test-event', handler);
      
      const result = Prime.EventBus.unsubscribe('test-event', handler);
      expect(result).toBe(true);
    });
    
    test('unsubscribe returns false if handler was not found', () => {
      const handler = jest.fn();
      // Not subscribing the handler
      
      const result = Prime.EventBus.unsubscribe('test-event', handler);
      expect(result).toBe(false);
    });
    
    test('unsubscribe only removes the specific handler', () => {
      const handler1 = jest.fn();
      const handler2 = jest.fn();
      
      Prime.EventBus.subscribe('test-event', handler1);
      Prime.EventBus.subscribe('test-event', handler2);
      
      Prime.EventBus.unsubscribe('test-event', handler1);
      
      Prime.EventBus.publish('test-event', {});
      
      expect(handler1).not.toHaveBeenCalled();
      expect(handler2).toHaveBeenCalledTimes(1);
    });
  });
  
  describe('clear', () => {
    test('clear removes all handlers for specific event', () => {
      const handler1 = jest.fn();
      const handler2 = jest.fn();
      
      Prime.EventBus.subscribe('event1', handler1);
      Prime.EventBus.subscribe('event2', handler2);
      
      Prime.EventBus.clear('event1');
      
      Prime.EventBus.publish('event1', {});
      Prime.EventBus.publish('event2', {});
      
      expect(handler1).not.toHaveBeenCalled();
      expect(handler2).toHaveBeenCalledTimes(1);
    });
    
    test('clear without event name removes all handlers', () => {
      const handler1 = jest.fn();
      const handler2 = jest.fn();
      
      Prime.EventBus.subscribe('event1', handler1);
      Prime.EventBus.subscribe('event2', handler2);
      
      Prime.EventBus.clear();
      
      Prime.EventBus.publish('event1', {});
      Prime.EventBus.publish('event2', {});
      
      expect(handler1).not.toHaveBeenCalled();
      expect(handler2).not.toHaveBeenCalled();
    });
  });
  
  describe('error handling', () => {
    test('errors in handlers do not affect other handlers', () => {
      const errorHandler = jest.fn().mockImplementation(() => {
        throw new Error('Handler error');
      });
      
      const normalHandler = jest.fn();
      
      Prime.EventBus.subscribe('test-event', errorHandler);
      Prime.EventBus.subscribe('test-event', normalHandler);
      
      // Should not throw despite error in first handler
      expect(() => {
        Prime.EventBus.publish('test-event', {});
      }).not.toThrow();
      
      // Normal handler should still be called
      expect(normalHandler).toHaveBeenCalledTimes(1);
    });
    
    test('throws ValidationError for invalid event name', () => {
      Assertions.assertThrows(
        () => Prime.EventBus.subscribe(123, () => {}),
        Prime.ValidationError,
        'subscribe should validate event name'
      );
    });
    
    test('throws ValidationError for invalid callback', () => {
      Assertions.assertThrows(
        () => Prime.EventBus.subscribe('test-event', 'not a function'),
        Prime.ValidationError,
        'subscribe should validate callback'
      );
    });
  });
  
  describe('integration with Mocking utilities', () => {
    test('can use mocked EventBus for testing', () => {
      // Create a mock EventBus
      const mockEventBus = Mocking.createMockEventBus();
      
      // Subscribe a handler
      const handler = jest.fn();
      mockEventBus.subscribe('test-event', handler);
      
      // Publish an event
      mockEventBus.publish('test-event', { value: 'test' });
      
      // Verify handler was called
      expect(handler).toHaveBeenCalledTimes(1);
      expect(handler).toHaveBeenCalledWith({ value: 'test' });
      
      // Verify call tracking
      expect(mockEventBus.calls.subscribe.length).toBe(1);
      expect(mockEventBus.calls.publish.length).toBe(1);
      expect(mockEventBus.calls.subscribe[0][0]).toBe('test-event');
      expect(mockEventBus.calls.publish[0][0]).toBe('test-event');
    });
  });
});