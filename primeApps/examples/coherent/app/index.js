/**
 * Coherent Example PrimeApp
 * Demonstrates coherence boundaries and enforcement
 */

const { PrimeApplication } = require('../../../../src/veneer/application');
const { 
  BoundaryType, 
  DomainType 
} = require('../../../../src/veneer/coherence-boundaries');

/**
 * Example app that implements coherence boundaries
 */
class CoherentExampleApp extends PrimeApplication {
  /**
   * Initialize the application
   */
  async init() {
    console.log('Initializing Coherent Example App');
    
    // Initialize application internal state
    this.appState = {
      started: false,
      counter: 0,
      data: {},
      numericalResults: [],
      coherenceViolations: []
    };
    
    // Call parent initialization
    await super.init();
    
    // Request resources
    this.storage = await this.getResource('storage', {
      persistent: true
    });
    
    this.compute = await this.getResource('compute', {
      concurrency: 3,
      priority: 'high'
    });
    
    this.memory = await this.getResource('memory', {
      max: '20MB'
    });
    
    // Load any saved state
    try {
      const savedState = await this.storage.load('appState');
      if (savedState) {
        this.appState = { ...this.appState, ...savedState };
        console.log('Loaded saved state:', this.appState);
      }
    } catch (error) {
      console.warn('No saved state found:', error.message);
    }
    
    // Register coherence boundaries
    this._registerCoherenceBoundaries();
  }
  
  /**
   * Start the application
   */
  async start() {
    console.log('Starting Coherent Example App');
    
    // Call parent start
    await super.start();
    
    // Set up interval for demo purposes
    this._intervalId = setInterval(() => {
      this.appState.counter++;
      console.log('App counter:', this.appState.counter);
      
      // Simulate numerical computations
      this._simulateNumericalWork();
      
    }, 5000);
    
    this.appState.started = true;
  }
  
  /**
   * Pause application activities
   */
  async pause() {
    console.log('Pausing Coherent Example App');
    
    // Call parent pause
    await super.pause();
    
    // Clear interval
    if (this._intervalId) {
      clearInterval(this._intervalId);
      this._intervalId = null;
    }
    
    // Save state
    await this._saveState();
  }
  
  /**
   * Resume application activities
   */
  async resume() {
    console.log('Resuming Coherent Example App');
    
    // Call parent resume
    await super.resume();
    
    // Restart interval
    this._intervalId = setInterval(() => {
      this.appState.counter++;
      console.log('App counter:', this.appState.counter);
      
      // Simulate numerical computations
      this._simulateNumericalWork();
      
    }, 5000);
  }
  
  /**
   * Stop and clean up resources
   */
  async stop() {
    console.log('Stopping Coherent Example App');
    
    // Clear interval
    if (this._intervalId) {
      clearInterval(this._intervalId);
      this._intervalId = null;
    }
    
    // Save state
    await this._saveState();
    
    // Call parent stop
    await super.stop();
  }
  
  /**
   * Calculate coherence score for this application
   * @returns {number} - Coherence score between 0 and 1
   */
  calculateCoherence() {
    // For this example, we'll calculate coherence based on:
    // - Numerical stability: proportion of finite values in results
    // - Memory usage: inverse proportion of memory used
    // - Logical consistency: based on state consistency
    
    let numericalCoherence = 1.0;
    let memoryCoherence = 1.0;
    let logicalCoherence = 1.0;
    
    // Numerical coherence
    if (this.appState.numericalResults.length > 0) {
      const validResults = this.appState.numericalResults.filter(val => 
        typeof val === 'number' && Number.isFinite(val)
      );
      
      numericalCoherence = validResults.length / this.appState.numericalResults.length;
    }
    
    // Memory coherence
    if (this.memory && typeof this.memory._estimateSize === 'function') {
      try {
        const stateSize = this.memory._estimateSize(this.appState);
        const maxSize = 20 * 1024 * 1024; // 20MB
        memoryCoherence = Math.max(0, Math.min(1, 1 - (stateSize / maxSize)));
      } catch (e) {
        // Ignore estimation errors
      }
    }
    
    // Logical coherence
    logicalCoherence = this.appState.started === (this.state === 'running') ? 1.0 : 0.5;
    
    // Weighted average with more weight on numerical stability
    const weightedCoherence = 
      (numericalCoherence * 0.5) + 
      (memoryCoherence * 0.3) + 
      (logicalCoherence * 0.2);
    
    return weightedCoherence;
  }
  
  /**
   * Process a numerical computation with coherence awareness
   * @param {number[]} values - Input values
   * @param {Object} options - Processing options
   * @returns {Object} - Processing results with coherence metrics
   */
  processNumericalComputation(values, options = {}) {
    console.log('Processing numerical computation:', { values, options });
    
    const results = {
      input: values,
      output: [],
      coherence: 1.0,
      violations: []
    };
    
    try {
      // Check input validity
      if (!Array.isArray(values)) {
        throw new Error('Input must be an array');
      }
      
      // Process each value
      for (const value of values) {
        let result;
        
        // Different operations based on options
        if (options.operation === 'square') {
          result = value * value;
        } else if (options.operation === 'sqrt') {
          result = Math.sqrt(value);
        } else if (options.operation === 'exp') {
          result = Math.exp(value);
        } else if (options.operation === 'log') {
          result = Math.log(value);
        } else {
          // Default to identity
          result = value;
        }
        
        results.output.push(result);
        
        // Add to numerical results history
        this.appState.numericalResults.push(result);
        
        // Track non-finite results
        if (!Number.isFinite(result)) {
          results.violations.push({
            type: 'finiteness',
            input: value,
            output: result,
            operation: options.operation || 'identity'
          });
        }
      }
      
      // Trim numerical results to avoid excessive memory growth
      if (this.appState.numericalResults.length > 1000) {
        this.appState.numericalResults = this.appState.numericalResults.slice(-1000);
      }
      
      // Calculate coherence based on output validity
      const validOutputs = results.output.filter(val => Number.isFinite(val));
      results.coherence = results.output.length > 0 
        ? validOutputs.length / results.output.length 
        : 1.0;
      
      // Track violations if coherence is low
      if (results.coherence < 0.9) {
        this.appState.coherenceViolations.push({
          type: 'numerical',
          timestamp: Date.now(),
          details: {
            operation: options.operation || 'identity',
            coherence: results.coherence,
            violations: results.violations.length
          }
        });
        
        // Trim violations list
        if (this.appState.coherenceViolations.length > 100) {
          this.appState.coherenceViolations = this.appState.coherenceViolations.slice(-100);
        }
      }
      
      return results;
    } catch (error) {
      // Log and return error result
      console.error('Error processing numerical computation:', error);
      
      return {
        input: values,
        output: [],
        coherence: 0,
        violations: [{
          type: 'error',
          message: error.message
        }]
      };
    }
  }
  
  /**
   * Save application state
   * @private
   */
  async _saveState() {
    if (this.storage) {
      await this.storage.store(this.appState, 'appState');
      console.log('Saved application state');
    }
  }
  
  /**
   * Register coherence boundaries for this application
   * @private
   */
  _registerCoherenceBoundaries() {
    // Register boundaries from manifest
    const boundaries = this.manifest.coherence && this.manifest.coherence.boundaries;
    
    if (!boundaries) {
      return;
    }
    
    // In a real implementation, this would register the boundaries with
    // the coherence manager. For this example, we'll just log them.
    console.log('Registering coherence boundaries:', boundaries);
    
    // Store boundaries for reference
    this.coherenceBoundaries = boundaries;
  }
  
  /**
   * Simulate numerical work to demonstrate coherence
   * @private
   */
  _simulateNumericalWork() {
    // Generate random values
    const values = Array(10).fill(0).map(() => (Math.random() - 0.5) * 10);
    
    // Different operations with different coherence implications
    const operations = ['square', 'sqrt', 'exp', 'log'];
    const operation = operations[Math.floor(Math.random() * operations.length)];
    
    // Process computation
    const results = this.processNumericalComputation(values, { 
      operation 
    });
    
    // Log results if violation occurred
    if (results.violations.length > 0) {
      console.log('Numerical computation violations:', {
        operation,
        coherence: results.coherence,
        violations: results.violations.length
      });
    }
  }
}

module.exports = CoherentExampleApp;