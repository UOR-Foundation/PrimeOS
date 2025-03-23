/**
 * PrimeOS Unit Tests - Logger
 * 
 * Tests for the Logger component in the core module.
 */

const Prime = require('../../../src/core.js');
const { Assertions, Mocking } = require('../../utils');

describe('Logger', () => {
  // Store original console methods
  let originalConsole;
  
  // Mock console methods
  let consoleSpies = {};
  
  beforeEach(() => {
    // Save original console methods
    originalConsole = {
      debug: console.debug,
      info: console.info,
      warn: console.warn,
      error: console.error
    };
    
    // Create spies for console methods
    consoleSpies = {
      debug: jest.spyOn(console, 'debug').mockImplementation(() => {}),
      info: jest.spyOn(console, 'info').mockImplementation(() => {}),
      warn: jest.spyOn(console, 'warn').mockImplementation(() => {}),
      error: jest.spyOn(console, 'error').mockImplementation(() => {})
    };
    
    // Reset to default log level
    Prime.Logger.setLevel('INFO');
  });
  
  afterEach(() => {
    // Restore original console methods
    console.debug = originalConsole.debug;
    console.info = originalConsole.info;
    console.warn = originalConsole.warn;
    console.error = originalConsole.error;
    
    // Restore spies
    jest.restoreAllMocks();
  });
  
  describe('logging levels', () => {
    test('default level is INFO', () => {
      // Test default level (INFO)
      Prime.Logger.debug('debug message');
      Prime.Logger.info('info message');
      Prime.Logger.warn('warn message');
      Prime.Logger.error('error message');
      
      expect(consoleSpies.debug).not.toHaveBeenCalled();
      expect(consoleSpies.info).toHaveBeenCalledTimes(1);
      expect(consoleSpies.warn).toHaveBeenCalledTimes(1);
      expect(consoleSpies.error).toHaveBeenCalledTimes(1);
    });
    
    test('setting level to DEBUG enables all logs', () => {
      Prime.Logger.setLevel('DEBUG');
      
      Prime.Logger.debug('debug message');
      Prime.Logger.info('info message');
      Prime.Logger.warn('warn message');
      Prime.Logger.error('error message');
      
      expect(consoleSpies.debug).toHaveBeenCalledTimes(1);
      expect(consoleSpies.info).toHaveBeenCalledTimes(1);
      expect(consoleSpies.warn).toHaveBeenCalledTimes(1);
      expect(consoleSpies.error).toHaveBeenCalledTimes(1);
    });
    
    test('setting level to WARN disables DEBUG and INFO', () => {
      Prime.Logger.setLevel('WARN');
      
      Prime.Logger.debug('debug message');
      Prime.Logger.info('info message');
      Prime.Logger.warn('warn message');
      Prime.Logger.error('error message');
      
      expect(consoleSpies.debug).not.toHaveBeenCalled();
      expect(consoleSpies.info).not.toHaveBeenCalled();
      expect(consoleSpies.warn).toHaveBeenCalledTimes(1);
      expect(consoleSpies.error).toHaveBeenCalledTimes(1);
    });
    
    test('setting level to ERROR disables all except ERROR', () => {
      Prime.Logger.setLevel('ERROR');
      
      Prime.Logger.debug('debug message');
      Prime.Logger.info('info message');
      Prime.Logger.warn('warn message');
      Prime.Logger.error('error message');
      
      expect(consoleSpies.debug).not.toHaveBeenCalled();
      expect(consoleSpies.info).not.toHaveBeenCalled();
      expect(consoleSpies.warn).not.toHaveBeenCalled();
      expect(consoleSpies.error).toHaveBeenCalledTimes(1);
    });
    
    test('setting NONE disables all logs', () => {
      Prime.Logger.setLevel('NONE');
      
      Prime.Logger.debug('debug message');
      Prime.Logger.info('info message');
      Prime.Logger.warn('warn message');
      Prime.Logger.error('error message');
      
      expect(consoleSpies.debug).not.toHaveBeenCalled();
      expect(consoleSpies.info).not.toHaveBeenCalled();
      expect(consoleSpies.warn).not.toHaveBeenCalled();
      expect(consoleSpies.error).not.toHaveBeenCalled();
    });
  });
  
  describe('level validation', () => {
    test('throws ValidationError for invalid level', () => {
      Assertions.assertThrows(
        () => Prime.Logger.setLevel('INVALID_LEVEL'),
        Prime.ValidationError,
        'setLevel should validate level string'
      );
    });
    
    test('accepts valid levels case-insensitively', () => {
      // Should not throw
      expect(() => {
        Prime.Logger.setLevel('debug');
        Prime.Logger.setLevel('INFO');
        Prime.Logger.setLevel('Warn');
        Prime.Logger.setLevel('ERROR');
        Prime.Logger.setLevel('none');
      }).not.toThrow();
    });
  });
  
  describe('message formatting', () => {
    test('formats messages with prefix and timestamp', () => {
      if (!Prime.Logger.formatMessage) {
        // Skip if formatMessage is not exposed
        return;
      }
      
      const message = 'Test message';
      const formattedMessage = Prime.Logger.formatMessage('INFO', message);
      
      expect(formattedMessage).toContain('[INFO]');
      expect(formattedMessage).toContain('Test message');
      expect(formattedMessage).toMatch(/\[\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}/); // ISO timestamp
    });
    
    test('handles multiple arguments', () => {
      Prime.Logger.info('Message with', 'multiple', 'arguments');
      
      expect(consoleSpies.info).toHaveBeenCalledTimes(1);
      
      // Check that all arguments were passed
      const callArgs = consoleSpies.info.mock.calls[0];
      expect(callArgs.length).toBeGreaterThanOrEqual(3);
      expect(callArgs.some(arg => arg.includes('multiple'))).toBe(true);
      expect(callArgs.some(arg => arg.includes('arguments'))).toBe(true);
    });
    
    test('handles object and error arguments', () => {
      const obj = { key: 'value' };
      const error = new Error('Test error');
      
      Prime.Logger.info('Object:', obj, 'Error:', error);
      
      expect(consoleSpies.info).toHaveBeenCalledTimes(1);
      
      // Check that object and error were passed
      const callArgs = consoleSpies.info.mock.calls[0];
      expect(callArgs.some(arg => arg === obj)).toBe(true);
      expect(callArgs.some(arg => arg === error)).toBe(true);
    });
  });
});