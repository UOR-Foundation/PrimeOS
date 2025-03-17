/**
 * PrimeOS Calculator Application
 * 
 * A simple calculator application that demonstrates the PrimeOS application API.
 */

// Import dependencies - use a different variable name to avoid conflicts
let CalculatorAppAPI;

try {
  if (typeof window !== 'undefined' && window.PrimeOS && window.PrimeOS.AppAPI) {
    console.log('Using PrimeOS.AppAPI from global window object');
    CalculatorAppAPI = window.PrimeOS.AppAPI;
  } else {
    // For Node.js or when not available in window
    console.log('Attempting to require app-api module');
    const appApiModule = require('../../core/apps/app-api');
    CalculatorAppAPI = appApiModule.AppAPI;
  }
} catch (error) {
  console.error('Failed to import AppAPI:', error);
  // Mock implementation for testing
  CalculatorAppAPI = class {
    constructor(options) {
      this.appId = options.appId;
      this.container = options.containerElement;
      this.eventBus = options.eventBus || { publish: () => {}, subscribe: () => () => {} };
      this.store = options.store || null;
      this.windowId = options.windowId || null;
      this.state = { preferences: {} };
    }
    
    showNotification(notification) {
      console.log('NOTIFICATION:', notification);
    }
    
    async loadPreferences() {
      return this.state.preferences;
    }
    
    async savePreferences(preferences) {
      this.state.preferences = { ...this.state.preferences, ...preferences };
    }
  };
}

/**
 * Calculator Application
 */
class Calculator {
  /**
   * Initialize the calculator
   * @param {HTMLElement} container - Container element
   * @param {Object} options - Initialization options
   */
  static async initialize(container, options) {
    const calculator = new Calculator(container, options);
    await calculator.init();
    return calculator;
  }
  
  /**
   * Constructor
   * @param {HTMLElement} container - Container element
   * @param {Object} options - Initialization options
   */
  constructor(container, options) {
    this.container = container;
    this.options = options;
    this.appId = 'calculator';
    
    // Calculator state
    this.state = {
      display: '0',
      firstOperand: null,
      secondOperand: null,
      operator: null,
      waitingForSecondOperand: false
    };
    
    // Initialize AppAPI with our renamed constructor
    this.api = new CalculatorAppAPI({
      appId: this.appId,
      containerElement: container,
      eventBus: options.eventBus,
      store: options.store,
      identity: options.identity,
      windowId: options.windowId
    });
    
    // Bind methods
    this.handleDigit = this.handleDigit.bind(this);
    this.handleOperator = this.handleOperator.bind(this);
    this.handleEquals = this.handleEquals.bind(this);
    this.handleDecimal = this.handleDecimal.bind(this);
    this.handleClear = this.handleClear.bind(this);
    this.handleBackspace = this.handleBackspace.bind(this);
    this.updateDisplay = this.updateDisplay.bind(this);
  }
  
  /**
   * Initialize the application
   */
  async init() {
    // Render initial UI
    this.renderUI();
    
    // Load preferences
    const preferences = await this.api.loadPreferences();
    
    // Apply theme if available
    if (preferences.theme) {
      this.applyTheme(preferences.theme);
    }
    
    // Set up event handlers
    this.initEventHandlers();
    
    // Notify shell that we're ready
    this.api.showNotification({
      title: 'Calculator',
      message: 'Calculator initialized successfully',
      type: 'success',
      timeout: 2000
    });
    
    return this;
  }
  
  /**
   * Render the UI
   */
  renderUI() {
    this.container.innerHTML = `
      <div class="calculator">
        <div class="calculator-header">
          <div class="calculator-theme-toggle">
            <button id="toggle-theme">🌙</button>
          </div>
        </div>
        <div class="calculator-display">
          <div id="display" class="display">0</div>
        </div>
        <div class="calculator-keys">
          <button class="key key-clear" data-action="clear">C</button>
          <button class="key key-backspace" data-action="backspace">⌫</button>
          <button class="key key-operator" data-action="operator" data-operator="%">%</button>
          <button class="key key-operator" data-action="operator" data-operator="/">÷</button>
          
          <button class="key key-digit" data-digit="7">7</button>
          <button class="key key-digit" data-digit="8">8</button>
          <button class="key key-digit" data-digit="9">9</button>
          <button class="key key-operator" data-action="operator" data-operator="*">×</button>
          
          <button class="key key-digit" data-digit="4">4</button>
          <button class="key key-digit" data-digit="5">5</button>
          <button class="key key-digit" data-digit="6">6</button>
          <button class="key key-operator" data-action="operator" data-operator="-">−</button>
          
          <button class="key key-digit" data-digit="1">1</button>
          <button class="key key-digit" data-digit="2">2</button>
          <button class="key key-digit" data-digit="3">3</button>
          <button class="key key-operator" data-action="operator" data-operator="+">+</button>
          
          <button class="key key-digit" data-digit="0">0</button>
          <button class="key key-decimal" data-action="decimal">.</button>
          <button class="key key-equals" data-action="equals">=</button>
        </div>
      </div>
    `;
    
    // Add styles
    const style = document.createElement('style');
    style.textContent = `
      .calculator {
        display: flex;
        flex-direction: column;
        height: 100%;
        width: 100%;
        max-width: 320px;
        margin: 0 auto;
        font-family: Arial, sans-serif;
        overflow: hidden;
        border-radius: 8px;
        box-shadow: 0 4px 15px rgba(0, 0, 0, 0.1);
        background-color: #f8f9fa;
      }
      
      .calculator-header {
        display: flex;
        justify-content: flex-end;
        padding: 10px;
      }
      
      .calculator-display {
        background-color: #f0f0f0;
        text-align: right;
        padding: 20px;
        border-bottom: 1px solid #ddd;
      }
      
      .display {
        font-size: 36px;
        font-weight: bold;
        min-height: 44px;
        overflow: hidden;
        text-overflow: ellipsis;
      }
      
      .calculator-keys {
        display: grid;
        grid-template-columns: repeat(4, 1fr);
        gap: 1px;
        background-color: #ddd;
        flex: 1;
      }
      
      .key {
        border: none;
        background-color: #fff;
        font-size: 20px;
        padding: 15px;
        cursor: pointer;
        transition: background-color 0.2s;
      }
      
      .key:hover {
        background-color: #f5f5f5;
      }
      
      .key:active {
        background-color: #e0e0e0;
      }
      
      .key-operator {
        background-color: #f8f9fa;
      }
      
      .key-equals {
        background-color: #007bff;
        color: white;
      }
      
      .key-equals:hover {
        background-color: #0069d9;
      }
      
      .key-clear, .key-backspace {
        background-color: #f8d7da;
      }
      
      /* Dark theme */
      .calculator.theme-dark {
        background-color: #343a40;
        color: #f8f9fa;
        box-shadow: 0 4px 15px rgba(0, 0, 0, 0.3);
      }
      
      .calculator.theme-dark .calculator-display {
        background-color: #212529;
        color: #fff;
        border-bottom: 1px solid #495057;
      }
      
      .calculator.theme-dark .calculator-keys {
        background-color: #495057;
      }
      
      .calculator.theme-dark .key {
        background-color: #343a40;
        color: #f8f9fa;
      }
      
      .calculator.theme-dark .key:hover {
        background-color: #4b545c;
      }
      
      .calculator.theme-dark .key:active {
        background-color: #6c757d;
      }
      
      .calculator.theme-dark .key-operator {
        background-color: #2b3035;
      }
      
      .calculator.theme-dark .key-equals {
        background-color: #0d6efd;
      }
      
      .calculator.theme-dark .key-equals:hover {
        background-color: #0a58ca;
      }
      
      .calculator.theme-dark .key-clear, 
      .calculator.theme-dark .key-backspace {
        background-color: #721c24;
        color: #f8d7da;
      }
    `;
    
    this.container.appendChild(style);
  }
  
  /**
   * Initialize event handlers
   */
  initEventHandlers() {
    // Digit keys
    const digitKeys = this.container.querySelectorAll('.key-digit');
    digitKeys.forEach(key => {
      key.addEventListener('click', () => {
        const digit = key.getAttribute('data-digit');
        this.handleDigit(digit);
      });
    });
    
    // Operator keys
    const operatorKeys = this.container.querySelectorAll('.key-operator');
    operatorKeys.forEach(key => {
      key.addEventListener('click', () => {
        const operator = key.getAttribute('data-operator');
        this.handleOperator(operator);
      });
    });
    
    // Equals key
    const equalsKey = this.container.querySelector('.key-equals');
    equalsKey.addEventListener('click', this.handleEquals);
    
    // Decimal key
    const decimalKey = this.container.querySelector('.key-decimal');
    decimalKey.addEventListener('click', this.handleDecimal);
    
    // Clear key
    const clearKey = this.container.querySelector('.key-clear');
    clearKey.addEventListener('click', this.handleClear);
    
    // Backspace key
    const backspaceKey = this.container.querySelector('.key-backspace');
    backspaceKey.addEventListener('click', this.handleBackspace);
    
    // Theme toggle
    const themeToggle = this.container.querySelector('#toggle-theme');
    themeToggle.addEventListener('click', () => {
      const calculator = this.container.querySelector('.calculator');
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
    });
    
    // Keyboard support
    document.addEventListener('keydown', (e) => {
      if (!this.api.state.isActive) return;
      
      // Digits
      if (/^[0-9]$/.test(e.key)) {
        this.handleDigit(e.key);
      }
      
      // Operators
      if (['+', '-', '*', '/', '%'].includes(e.key)) {
        this.handleOperator(e.key);
      }
      
      // Equals
      if (e.key === '=' || e.key === 'Enter') {
        this.handleEquals();
      }
      
      // Decimal
      if (e.key === '.') {
        this.handleDecimal();
      }
      
      // Clear
      if (e.key === 'Escape' || e.key === 'Delete') {
        this.handleClear();
      }
      
      // Backspace
      if (e.key === 'Backspace') {
        this.handleBackspace();
      }
    });
    
    // Lifecycle hooks
    this.api.onFocus = () => {
      // Ensure the calculator handles keyboard input when focused
      console.log('Calculator focused');
    };
  }
  
  /**
   * Apply theme to calculator
   * @param {string} theme - Theme name (light or dark)
   */
  applyTheme(theme) {
    const calculator = this.container.querySelector('.calculator');
    const themeToggle = this.container.querySelector('#toggle-theme');
    
    if (theme === 'dark') {
      calculator.classList.add('theme-dark');
      themeToggle.textContent = '☀️';
    } else {
      calculator.classList.remove('theme-dark');
      themeToggle.textContent = '🌙';
    }
  }
  
  /**
   * Handle digit button click
   * @param {string} digit - The digit pressed
   */
  handleDigit(digit) {
    const { display, waitingForSecondOperand } = this.state;
    
    if (waitingForSecondOperand) {
      this.state.display = digit;
      this.state.waitingForSecondOperand = false;
    } else {
      this.state.display = display === '0' ? digit : display + digit;
    }
    
    this.updateDisplay();
  }
  
  /**
   * Handle operator button click
   * @param {string} nextOperator - The operator pressed
   */
  handleOperator(nextOperator) {
    const { firstOperand, display, operator } = this.state;
    const inputValue = parseFloat(display);
    
    if (firstOperand === null) {
      this.state.firstOperand = inputValue;
    } else if (operator) {
      const result = this.calculate(firstOperand, inputValue, operator);
      
      this.state.display = String(result);
      this.state.firstOperand = result;
    }
    
    this.state.waitingForSecondOperand = true;
    this.state.operator = nextOperator;
    
    this.updateDisplay();
  }
  
  /**
   * Handle equals button click
   */
  handleEquals() {
    const { firstOperand, display, operator } = this.state;
    const inputValue = parseFloat(display);
    
    if (firstOperand === null || !operator) {
      return;
    }
    
    const result = this.calculate(firstOperand, inputValue, operator);
    this.state.display = String(result);
    
    // Reset for next calculation
    this.state.firstOperand = result;
    this.state.waitingForSecondOperand = true;
    this.state.operator = null;
    
    this.updateDisplay();
  }
  
  /**
   * Handle decimal point button click
   */
  handleDecimal() {
    const { display, waitingForSecondOperand } = this.state;
    
    if (waitingForSecondOperand) {
      this.state.display = '0.';
      this.state.waitingForSecondOperand = false;
    } else if (display.indexOf('.') === -1) {
      this.state.display = display + '.';
    }
    
    this.updateDisplay();
  }
  
  /**
   * Handle clear button click
   */
  handleClear() {
    this.state.display = '0';
    this.state.firstOperand = null;
    this.state.secondOperand = null;
    this.state.operator = null;
    this.state.waitingForSecondOperand = false;
    
    this.updateDisplay();
  }
  
  /**
   * Handle backspace button click
   */
  handleBackspace() {
    const { display } = this.state;
    
    if (display === '0' || display.length === 1) {
      this.state.display = '0';
    } else {
      this.state.display = display.substring(0, display.length - 1);
    }
    
    this.updateDisplay();
  }
  
  /**
   * Perform calculation
   * @param {number} firstOperand - First operand
   * @param {number} secondOperand - Second operand
   * @param {string} operator - Operator to use
   * @returns {number} Result of calculation
   */
  calculate(firstOperand, secondOperand, operator) {
    switch (operator) {
      case '+':
        return firstOperand + secondOperand;
      case '-':
        return firstOperand - secondOperand;
      case '*':
        return firstOperand * secondOperand;
      case '/':
        return secondOperand !== 0 ? firstOperand / secondOperand : 'Error';
      case '%':
        return firstOperand % secondOperand;
      default:
        return secondOperand;
    }
  }
  
  /**
   * Update the display
   */
  updateDisplay() {
    const displayElement = this.container.querySelector('#display');
    displayElement.textContent = this.state.display;
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { default: Calculator };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.Calculator = Calculator;
}