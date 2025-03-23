/**
 * PrimeOS JavaScript Library - Distributed Event Bus
 * Local implementation for distributed modules
 */

/**
 * Simple EventBus implementation for distributed modules
 */
class EventBus {
  /**
   * Create a new EventBus instance
   */
  constructor() {
    // Map of event name -> array of listeners
    this.events = new Map();
    // Counter for generating listener IDs
    this.nextId = 1;
  }

  /**
   * Register an event listener
   * @param {string} event - Event name to listen for
   * @param {Function} callback - Function to call when event is emitted
   * @returns {Function} Function to remove this listener
   */
  on(event, callback) {
    if (typeof callback !== 'function') {
      throw new Error('Callback must be a function');
    }

    if (!this.events.has(event)) {
      this.events.set(event, []);
    }

    const id = this.nextId++;
    const listeners = this.events.get(event);

    listeners.push({
      id,
      callback,
    });

    // Return an unsubscribe function
    return () => {
      this.off(event, callback);
    };
  }

  /**
   * Remove an event listener
   * @param {string} event - Event name
   * @param {Function} callback - Callback to remove
   * @returns {boolean} True if listener was removed
   */
  off(event, callback) {
    if (!this.events.has(event)) {
      return false;
    }

    const listeners = this.events.get(event);
    const initialLength = listeners.length;

    const filtered = listeners.filter(
      (listener) => listener.callback !== callback,
    );

    if (filtered.length === initialLength) {
      return false;
    }

    if (filtered.length === 0) {
      this.events.delete(event);
    } else {
      this.events.set(event, filtered);
    }

    return true;
  }

  /**
   * Emit an event with data
   * @param {string} event - Event name to emit
   * @param {*} data - Data to pass to listeners
   * @returns {boolean} True if event had listeners
   */
  emit(event, data) {
    if (!this.events.has(event)) {
      return false;
    }

    const listeners = this.events.get(event);

    if (listeners.length === 0) {
      return false;
    }

    // Create a copy to avoid modification issues during iteration
    [...listeners].forEach((listener) => {
      try {
        listener.callback(data);
      } catch (error) {
        console.error(`Error in event listener for ${event}:`, error);
      }
    });

    return true;
  }

  /**
   * Remove all listeners for an event
   * @param {string} event - Event name to clear
   * @returns {boolean} True if event existed and was cleared
   */
  removeAllListeners(event) {
    if (event) {
      // Remove specific event
      return this.events.delete(event);
    } else {
      // Remove all events
      this.events.clear();
      return true;
    }
  }

  /**
   * Get the number of listeners for an event
   * @param {string} event - Event name
   * @returns {number} Number of listeners
   */
  listenerCount(event) {
    if (!this.events.has(event)) {
      return 0;
    }

    return this.events.get(event).length;
  }

  /**
   * Get all event names
   * @returns {Array<string>} Array of event names
   */
  eventNames() {
    return Array.from(this.events.keys());
  }
}

// Export the EventBus class
module.exports = EventBus;
