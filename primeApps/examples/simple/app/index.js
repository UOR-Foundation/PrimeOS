/**
 * Simple Example PrimeApp
 * Demonstrates basic PrimeApp functionality
 */

const { PrimeApplication } = require('../../../../src/veneer/application');

class SimpleExampleApp extends PrimeApplication {
  /**
   * Initialize the application
   */
  async init() {
    console.log('Initializing Simple Example App');
    
    // Call parent initialization
    await super.init();
    
    // Initialize application internal state
    this.appState = {
      started: false,
      counter: 0,
      data: {}
    };
    
    // Request storage resource
    this.storage = await this.getResource('storage', {
      persistent: true
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
  }
  
  /**
   * Start the application
   */
  async start() {
    console.log('Starting Simple Example App');
    
    // Call parent start
    await super.start();
    
    // Set up interval for demo purposes
    this._intervalId = setInterval(() => {
      this.appState.counter++;
      console.log('App counter:', this.appState.counter);
    }, 5000);
    
    this.appState.started = true;
  }
  
  /**
   * Pause application activities
   */
  async pause() {
    console.log('Pausing Simple Example App');
    
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
    console.log('Resuming Simple Example App');
    
    // Call parent resume
    await super.resume();
    
    // Restart interval
    this._intervalId = setInterval(() => {
      this.appState.counter++;
      console.log('App counter:', this.appState.counter);
    }, 5000);
  }
  
  /**
   * Stop and clean up resources
   */
  async stop() {
    console.log('Stopping Simple Example App');
    
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
   * Example method provided by this application
   * @param {string} message - Message to process
   * @returns {Object} - Processed result
   */
  processMessage(message) {
    const result = {
      original: message,
      processed: message.toUpperCase(),
      timestamp: Date.now(),
      counter: this.appState.counter
    };
    
    this.appState.data[result.timestamp] = result;
    
    return result;
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
   * Calculate the application coherence score
   * @returns {number} - Coherence score between 0 and 1
   */
  calculateCoherence() {
    // For this example, we'll return a simple coherence score
    // In a real application, this would be based on actual coherence calculations
    return 0.9;
  }
}

module.exports = SimpleExampleApp;