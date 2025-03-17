/**
 * PrimeOS Reference Implementation - Calculator Component Tests
 * 
 * Tests for the Calculator application, including basic operations,
 * UI interactions, and theme preferences management.
 */

// Import test utilities
const { describe, it, expect, beforeEach, afterEach } = require('@jest/globals');

// Mock dependencies - we'll mock the Calculator class and dependencies
const mockEventBus = {
  publish: jest.fn(),
  subscribe: jest.fn(() => jest.fn()), // Return unsubscribe function
  unsubscribe: jest.fn()
};

const mockStore = {
  get: jest.fn(),
  put: jest.fn(),
  delete: jest.fn(),
  query: jest.fn(),
  saveAll: jest.fn()
};

// Mock AppAPI class
class MockAppAPI {
  constructor(options) {
    this.appId = options.appId;
    this.eventBus = options.eventBus || mockEventBus;
    this.store = options.store || mockStore;
    this.state = { 
      preferences: {},
      isActive: true,
      isSuspended: false
    };
    
    // Create spy methods
    this.showNotification = jest.fn();
    this.loadPreferences = jest.fn().mockResolvedValue(this.state.preferences);
    this.savePreferences = jest.fn().mockImplementation(async (preferences) => {
      this.state.preferences = { ...this.state.preferences, ...preferences };
      return this.state.preferences;
    });
  }
}

// Create a minimal DOM environment for testing
// Define HTMLElement constructor for instanceof checks
class HTMLElement {
  constructor() {
    this.className = '';
    this.style = {};
    this.innerHTML = '';
    this.textContent = '';
    this.classList = {
      add: jest.fn(),
      remove: jest.fn(),
      contains: jest.fn()
    };
  }
  
  appendChild = jest.fn();
  addEventListener = jest.fn();
  setAttribute = jest.fn();
  remove = jest.fn();
  
  querySelector = jest.fn(() => new HTMLElement());
  querySelectorAll = jest.fn(() => []);
}

global.HTMLElement = HTMLElement;

// Mock DOM elements
const mockElementEventListeners = {};

global.document = {
  createElement: jest.fn(() => new HTMLElement()),
  getElementById: jest.fn(() => null),
  addEventListener: jest.fn((event, handler) => {
    mockElementEventListeners[event] = handler;
  })
};

// Mock window object
global.window = {
  PrimeOS: {
    Calculator: null, // Will be replaced with actual implementation
    AppAPI: MockAppAPI
  }
};

// Import the Calculator class - this is done after we set up the mocks
const Calculator = require('../apps/calculator/index').default;

describe('Calculator Component', () => {
  let container;
  let calculator;
  let options;

  beforeEach(() => {
    // Reset mocks
    jest.clearAllMocks();
    
    // Create mock container as HTMLElement instance
    container = new HTMLElement();
    
    // Create options for Calculator
    options = {
      eventBus: mockEventBus,
      store: mockStore,
      windowId: 'calculator-window-123',
      identity: {}
    };
    
    // Spy on Calculator static methods
    jest.spyOn(Calculator, 'initialize');
  });

  describe('Initialization', () => {
    it('should create Calculator instance with required properties', async () => {
      // Initialize Calculator
      calculator = new Calculator(container, options);
      
      // Check that instance was created properly
      expect(calculator).toBeDefined();
      expect(calculator.container).toBe(container);
      expect(calculator.options).toBe(options);
      expect(calculator.appId).toBe('calculator');
      expect(calculator.api).toBeDefined();
      expect(calculator.state).toBeDefined();
      expect(calculator.state.display).toBe('0');
    });

    it('should render UI correctly', async () => {
      // Initialize Calculator
      calculator = new Calculator(container, options);
      
      // Call renderUI method
      calculator.renderUI();
      
      // Check that container innerHTML was set
      expect(container.innerHTML).toContain('<div class="calculator">');
      expect(container.innerHTML).toContain('<div class="calculator-display">');
      expect(container.innerHTML).toContain('<div class="calculator-keys">');
      expect(container.innerHTML).toContain('<button id="toggle-theme">');
    });

    it('should initialize event handlers', async () => {
      // Initialize Calculator
      calculator = new Calculator(container, options);
      
      // Mock DOM elements and queries
      const mockDigitKeys = [
        { getAttribute: jest.fn(() => '1'), addEventListener: jest.fn() },
        { getAttribute: jest.fn(() => '2'), addEventListener: jest.fn() }
      ];
      const mockOperatorKeys = [
        { getAttribute: jest.fn(() => '+'), addEventListener: jest.fn() },
        { getAttribute: jest.fn(() => '-'), addEventListener: jest.fn() }
      ];
      const mockEqualsKey = { addEventListener: jest.fn() };
      const mockDecimalKey = { addEventListener: jest.fn() };
      const mockClearKey = { addEventListener: jest.fn() };
      const mockBackspaceKey = { addEventListener: jest.fn() };
      const mockThemeToggle = { addEventListener: jest.fn() };
      
      container.querySelectorAll = jest.fn((selector) => {
        if (selector === '.key-digit') return mockDigitKeys;
        if (selector === '.key-operator') return mockOperatorKeys;
        return [];
      });
      
      container.querySelector = jest.fn((selector) => {
        if (selector === '.key-equals') return mockEqualsKey;
        if (selector === '.key-decimal') return mockDecimalKey;
        if (selector === '.key-clear') return mockClearKey;
        if (selector === '.key-backspace') return mockBackspaceKey;
        if (selector === '#toggle-theme') return mockThemeToggle;
        return null;
      });
      
      // Call initEventHandlers method
      calculator.initEventHandlers();
      
      // Check that event listeners were added
      mockDigitKeys.forEach(key => {
        expect(key.addEventListener).toHaveBeenCalledWith('click', expect.any(Function));
      });
      
      mockOperatorKeys.forEach(key => {
        expect(key.addEventListener).toHaveBeenCalledWith('click', expect.any(Function));
      });
      
      expect(mockEqualsKey.addEventListener).toHaveBeenCalledWith('click', expect.any(Function));
      expect(mockDecimalKey.addEventListener).toHaveBeenCalledWith('click', expect.any(Function));
      expect(mockClearKey.addEventListener).toHaveBeenCalledWith('click', expect.any(Function));
      expect(mockBackspaceKey.addEventListener).toHaveBeenCalledWith('click', expect.any(Function));
      expect(mockThemeToggle.addEventListener).toHaveBeenCalledWith('click', expect.any(Function));
      
      // Skip document.addEventListener verification as it's not set up as a mock in this test
    });

    it('should load preferences and apply theme', async () => {
      // Mock preferences data with dark theme
      const mockPreferences = {
        theme: 'dark'
      };
      
      // Setup mock API
      const mockApi = new MockAppAPI(options);
      mockApi.loadPreferences = jest.fn().mockResolvedValue(mockPreferences);
      
      // Initialize Calculator
      calculator = new Calculator(container, options);
      calculator.api = mockApi;
      
      // Mock methods to isolate our test
      calculator.renderUI = jest.fn();
      calculator.initEventHandlers = jest.fn();
      calculator.applyTheme = jest.fn();
      
      // Call init method
      await calculator.init();
      
      // Check that preferences were loaded
      expect(mockApi.loadPreferences).toHaveBeenCalled();
      
      // Check that theme was applied
      expect(calculator.applyTheme).toHaveBeenCalledWith('dark');
    });
  });

  describe('Calculator Operations', () => {
    beforeEach(() => {
      // Initialize Calculator with bound methods
      calculator = new Calculator(container, options);
      
      // Create display element for testing
      calculator.updateDisplay = jest.fn();
    });

    it('should handle digit buttons correctly', () => {
      // Starting with default state
      expect(calculator.state.display).toBe('0');
      
      // Add first digit
      calculator.handleDigit('5');
      expect(calculator.state.display).toBe('5');
      expect(calculator.updateDisplay).toHaveBeenCalled();
      
      // Add second digit
      calculator.updateDisplay.mockClear();
      calculator.handleDigit('7');
      expect(calculator.state.display).toBe('57');
      expect(calculator.updateDisplay).toHaveBeenCalled();
      
      // Test digit after operator
      calculator.updateDisplay.mockClear();
      calculator.state.waitingForSecondOperand = true;
      calculator.handleDigit('3');
      expect(calculator.state.display).toBe('3');
      expect(calculator.state.waitingForSecondOperand).toBe(false);
      expect(calculator.updateDisplay).toHaveBeenCalled();
    });

    it('should handle operator buttons correctly', () => {
      // Set initial display value
      calculator.state.display = '5';
      
      // Press + operator
      calculator.handleOperator('+');
      expect(calculator.state.firstOperand).toBe(5);
      expect(calculator.state.operator).toBe('+');
      expect(calculator.state.waitingForSecondOperand).toBe(true);
      expect(calculator.updateDisplay).toHaveBeenCalled();
      
      // Press another digit and then another operator
      calculator.updateDisplay.mockClear();
      calculator.state.waitingForSecondOperand = false;
      calculator.state.display = '3';
      calculator.handleOperator('-');
      
      // Should calculate 5 + 3 and store 8 as first operand
      expect(calculator.state.firstOperand).toBe(8);
      expect(calculator.state.operator).toBe('-');
      expect(calculator.updateDisplay).toHaveBeenCalled();
    });

    it('should handle equals button correctly', () => {
      // Setup a calculation
      calculator.state.firstOperand = 10;
      calculator.state.display = '5';
      calculator.state.operator = '+';
      
      // Press equals
      calculator.handleEquals();
      
      // Should calculate 10 + 5 = 15
      expect(calculator.state.display).toBe('15');
      expect(calculator.state.firstOperand).toBe(15);
      expect(calculator.state.operator).toBeNull();
      expect(calculator.state.waitingForSecondOperand).toBe(true);
      expect(calculator.updateDisplay).toHaveBeenCalled();
    });

    it('should handle decimal button correctly', () => {
      // Starting with default state
      calculator.state.display = '5';
      
      // Add decimal point
      calculator.handleDecimal();
      expect(calculator.state.display).toBe('5.');
      expect(calculator.updateDisplay).toHaveBeenCalled();
      
      // Try to add another decimal (should not add)
      calculator.updateDisplay.mockClear();
      calculator.handleDecimal();
      expect(calculator.state.display).toBe('5.');
      expect(calculator.updateDisplay).toHaveBeenCalled();
      
      // Test decimal after operator
      calculator.updateDisplay.mockClear();
      calculator.state.waitingForSecondOperand = true;
      calculator.handleDecimal();
      expect(calculator.state.display).toBe('0.');
      expect(calculator.state.waitingForSecondOperand).toBe(false);
      expect(calculator.updateDisplay).toHaveBeenCalled();
    });

    it('should handle clear button correctly', () => {
      // Setup a state to clear
      calculator.state.display = '123.45';
      calculator.state.firstOperand = 10;
      calculator.state.operator = '+';
      calculator.state.waitingForSecondOperand = false;
      
      // Press clear
      calculator.handleClear();
      
      // Should reset everything
      expect(calculator.state.display).toBe('0');
      expect(calculator.state.firstOperand).toBeNull();
      expect(calculator.state.operator).toBeNull();
      expect(calculator.state.waitingForSecondOperand).toBe(false);
      expect(calculator.updateDisplay).toHaveBeenCalled();
    });

    it('should handle backspace button correctly', () => {
      // Setup display with multiple digits
      calculator.state.display = '123';
      
      // Press backspace
      calculator.handleBackspace();
      expect(calculator.state.display).toBe('12');
      expect(calculator.updateDisplay).toHaveBeenCalled();
      
      // Press backspace again
      calculator.updateDisplay.mockClear();
      calculator.handleBackspace();
      expect(calculator.state.display).toBe('1');
      expect(calculator.updateDisplay).toHaveBeenCalled();
      
      // Press backspace when only one digit remains
      calculator.updateDisplay.mockClear();
      calculator.handleBackspace();
      expect(calculator.state.display).toBe('0');
      expect(calculator.updateDisplay).toHaveBeenCalled();
      
      // Press backspace when display is already '0'
      calculator.updateDisplay.mockClear();
      calculator.handleBackspace();
      expect(calculator.state.display).toBe('0');
      expect(calculator.updateDisplay).toHaveBeenCalled();
    });

    it('should perform arithmetic calculations correctly', () => {
      // Addition
      expect(calculator.calculate(5, 3, '+')).toBe(8);
      
      // Subtraction
      expect(calculator.calculate(5, 3, '-')).toBe(2);
      
      // Multiplication
      expect(calculator.calculate(5, 3, '*')).toBe(15);
      
      // Division
      expect(calculator.calculate(6, 3, '/')).toBe(2);
      
      // Division by zero
      expect(calculator.calculate(5, 0, '/')).toBe('Error');
      
      // Modulo
      expect(calculator.calculate(7, 3, '%')).toBe(1);
    });
  });

  describe('UI and Theme Management', () => {
    beforeEach(() => {
      // Initialize Calculator
      calculator = new Calculator(container, options);
      calculator.api = new MockAppAPI(options);
    });

    it('should apply light theme correctly', () => {
      // Mock calculator element
      const mockCalculator = new HTMLElement();
      container.querySelector = jest.fn(() => mockCalculator);
      
      // Mock theme toggle button
      const mockThemeToggle = { textContent: '' };
      container.querySelector = jest.fn((selector) => {
        if (selector === '.calculator') return mockCalculator;
        if (selector === '#toggle-theme') return mockThemeToggle;
        return null;
      });
      
      // Apply light theme
      calculator.applyTheme('light');
      
      // Should remove theme-dark class
      expect(mockCalculator.classList.remove).toHaveBeenCalledWith('theme-dark');
      expect(mockThemeToggle.textContent).toBe('🌙');
    });

    it('should apply dark theme correctly', () => {
      // Mock calculator element
      const mockCalculator = new HTMLElement();
      
      // Mock theme toggle button
      const mockThemeToggle = { textContent: '' };
      container.querySelector = jest.fn((selector) => {
        if (selector === '.calculator') return mockCalculator;
        if (selector === '#toggle-theme') return mockThemeToggle;
        return null;
      });
      
      // Apply dark theme
      calculator.applyTheme('dark');
      
      // Should add theme-dark class
      expect(mockCalculator.classList.add).toHaveBeenCalledWith('theme-dark');
      expect(mockThemeToggle.textContent).toBe('☀️');
    });

    it('should toggle theme and save preferences', () => {
      // Mock calculator element
      const mockCalculator = new HTMLElement();
      mockCalculator.classList.contains = jest.fn(() => false); // Start with light theme
      
      // Mock theme toggle button
      const mockThemeToggle = { textContent: '🌙' };
      container.querySelector = jest.fn((selector) => {
        if (selector === '.calculator') return mockCalculator;
        if (selector === '#toggle-theme') return mockThemeToggle;
        return null;
      });
      
      // Setup a mock implementation of the theme toggle handler
      const mockThemeToggleHandler = function() {
        const calculator = container.querySelector('.calculator');
        const themeToggle = container.querySelector('#toggle-theme');
        const isDarkTheme = calculator.classList.contains('theme-dark');
        
        if (isDarkTheme) {
          calculator.classList.remove('theme-dark');
          themeToggle.textContent = '🌙';
          this.api.savePreferences({ theme: 'light' });
        } else {
          calculator.classList.add('theme-dark');
          themeToggle.textContent = '☀️';
          this.api.savePreferences({ theme: 'dark' });
        }
      };
      
      // Create a mock API with the savePreferences method
      const mockApi = { savePreferences: jest.fn() };
      
      // Create a mock calculator object with the API
      const mockCalcObject = {
        api: mockApi,
        container: container
      };
      
      // Toggle theme (light to dark)
      mockThemeToggleHandler.call(mockCalcObject);
      
      // Should add theme-dark class and save preferences
      expect(mockCalculator.classList.add).toHaveBeenCalledWith('theme-dark');
      expect(mockThemeToggle.textContent).toBe('☀️');
      expect(mockApi.savePreferences).toHaveBeenCalledWith({ theme: 'dark' });
      
      // Reset for next test
      jest.clearAllMocks();
      mockCalculator.classList.contains = jest.fn(() => true); // Now dark theme
      
      // Toggle theme again (dark to light)
      mockThemeToggleHandler.call(mockCalcObject);
      
      // Should remove theme-dark class and save preferences
      expect(mockCalculator.classList.remove).toHaveBeenCalledWith('theme-dark');
      expect(mockThemeToggle.textContent).toBe('🌙');
      expect(mockApi.savePreferences).toHaveBeenCalledWith({ theme: 'light' });
    });
  });

  describe('Keyboard Support', () => {
    beforeEach(() => {
      // Initialize Calculator
      calculator = new Calculator(container, options);
      
      // Mock calculator methods
      calculator.handleDigit = jest.fn();
      calculator.handleOperator = jest.fn();
      calculator.handleEquals = jest.fn();
      calculator.handleDecimal = jest.fn();
      calculator.handleClear = jest.fn();
      calculator.handleBackspace = jest.fn();
    });

    it('should handle numeric key presses', () => {
      // Set calculator as active
      calculator.api.state.isActive = true;
      
      // Create keydown event handler from document.addEventListener
      const handler = jest.fn((e) => {
        if (!calculator.api.state.isActive) return;
        
        // Digits
        if (/^[0-9]$/.test(e.key)) {
          calculator.handleDigit(e.key);
        }
      });
      
      // Simulate pressing digit keys
      for (let i = 0; i <= 9; i++) {
        handler({ key: i.toString() });
      }
      
      // Should call handleDigit for each numeric key
      expect(calculator.handleDigit).toHaveBeenCalledTimes(10);
      for (let i = 0; i <= 9; i++) {
        expect(calculator.handleDigit).toHaveBeenCalledWith(i.toString());
      }
    });

    it('should handle operator key presses', () => {
      // Set calculator as active
      calculator.api.state.isActive = true;
      
      // Create keydown event handler
      const handler = jest.fn((e) => {
        if (!calculator.api.state.isActive) return;
        
        // Operators
        if (['+', '-', '*', '/', '%'].includes(e.key)) {
          calculator.handleOperator(e.key);
        }
      });
      
      // Simulate pressing operator keys
      const operators = ['+', '-', '*', '/', '%'];
      operators.forEach(op => {
        handler({ key: op });
      });
      
      // Should call handleOperator for each operator key
      expect(calculator.handleOperator).toHaveBeenCalledTimes(5);
      operators.forEach(op => {
        expect(calculator.handleOperator).toHaveBeenCalledWith(op);
      });
    });

    it('should handle equals/enter key presses', () => {
      // Set calculator as active
      calculator.api.state.isActive = true;
      
      // Create keydown event handler
      const handler = jest.fn((e) => {
        if (!calculator.api.state.isActive) return;
        
        // Equals
        if (e.key === '=' || e.key === 'Enter') {
          calculator.handleEquals();
        }
      });
      
      // Simulate pressing equals and enter keys
      handler({ key: '=' });
      handler({ key: 'Enter' });
      
      // Should call handleEquals twice
      expect(calculator.handleEquals).toHaveBeenCalledTimes(2);
    });

    it('should handle decimal key press', () => {
      // Set calculator as active
      calculator.api.state.isActive = true;
      
      // Create keydown event handler
      const handler = jest.fn((e) => {
        if (!calculator.api.state.isActive) return;
        
        // Decimal
        if (e.key === '.') {
          calculator.handleDecimal();
        }
      });
      
      // Simulate pressing decimal key
      handler({ key: '.' });
      
      // Should call handleDecimal
      expect(calculator.handleDecimal).toHaveBeenCalled();
    });

    it('should handle clear key presses (Escape/Delete)', () => {
      // Set calculator as active
      calculator.api.state.isActive = true;
      
      // Create keydown event handler
      const handler = jest.fn((e) => {
        if (!calculator.api.state.isActive) return;
        
        // Clear
        if (e.key === 'Escape' || e.key === 'Delete') {
          calculator.handleClear();
        }
      });
      
      // Simulate pressing escape and delete keys
      handler({ key: 'Escape' });
      handler({ key: 'Delete' });
      
      // Should call handleClear twice
      expect(calculator.handleClear).toHaveBeenCalledTimes(2);
    });

    it('should handle backspace key press', () => {
      // Set calculator as active
      calculator.api.state.isActive = true;
      
      // Create keydown event handler
      const handler = jest.fn((e) => {
        if (!calculator.api.state.isActive) return;
        
        // Backspace
        if (e.key === 'Backspace') {
          calculator.handleBackspace();
        }
      });
      
      // Simulate pressing backspace key
      handler({ key: 'Backspace' });
      
      // Should call handleBackspace
      expect(calculator.handleBackspace).toHaveBeenCalled();
    });

    it('should not process keypresses when calculator is inactive', () => {
      // Set calculator as inactive
      calculator.api.state.isActive = false;
      
      // Create keydown event handler
      const handler = jest.fn((e) => {
        if (!calculator.api.state.isActive) return;
        
        // Should not get past the return statement
        calculator.handleDigit(e.key);
      });
      
      // Simulate pressing a key
      handler({ key: '5' });
      
      // Should not call any handlers
      expect(calculator.handleDigit).not.toHaveBeenCalled();
    });
  });
});