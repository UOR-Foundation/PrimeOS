/**
 * PrimeOS JavaScript Library - Event Bus
 * Publish/Subscribe event system for component communication
 * Version 1.0.0
 */

// Import Prime object from prime.js
const Prime = require('./prime.js');

(function (Prime) {
  /**
   * EventBus implementation
   * Central pub/sub mechanism for component communication
   */

  // Legacy singleton EventBus for backward compatibility
  const LegacyEventBus = (function () {
    // Map of topic -> array of callbacks
    const topics = {};
    // Counter for generating subscription tokens
    let subUid = -1;

    return {
      /**
       * Publishes data to a topic
       * @param {string} topic - Topic to publish to
       * @param {*} data - Data to publish
       * @returns {boolean} True if data was published
       */
      publish: function (topic, data) {
        if (!topic) {
          return false;
        }

        const listeners = topics[topic];
        if (!listeners || listeners.length === 0) {
          return false;
        }

        // Create a copy to avoid modification issues during iteration
        const currentListeners = [...listeners];

        // Publish to each subscriber
        currentListeners.forEach((listener) => {
          try {
            listener.callback(data, {
              topic,
              timestamp: Date.now(),
              token: listener.token,
            });
          } catch (e) {
            console.error(
              `Error in eventbus subscriber for topic ${topic}:`,
              e,
            );
          }
        });

        return true;
      },

      /**
       * Subscribes to a topic
       * @param {string} topic - Topic to subscribe to
       * @param {Function} callback - Function to call when topic is published to
       * @returns {string} Subscription token
       */
      subscribe: function (topic, callback) {
        if (!topic || typeof callback !== 'function') {
          return null;
        }

        // Create topic array if it doesn't exist
        if (!topics[topic]) {
          topics[topic] = [];
        }

        // Generate token and add subscription
        const token = (++subUid).toString();
        topics[topic].push({
          token,
          callback,
        });

        return token;
      },

      /**
       * Unsubscribes from a topic using the token
       * @param {string} token - Subscription token
       * @returns {boolean} True if unsubscribed successfully
       */
      unsubscribe: function (token) {
        if (!token) {
          return false;
        }

        let found = false;

        // Look through all topics for the token
        Object.keys(topics).forEach((topic) => {
          if (topics[topic]) {
            const initialLength = topics[topic].length;
            topics[topic] = topics[topic].filter(
              (item) => item.token !== token,
            );

            if (topics[topic].length < initialLength) {
              found = true;
            }

            // Clean up empty topic arrays
            if (topics[topic].length === 0) {
              delete topics[topic];
            }
          }
        });

        return found;
      },

      /**
       * Clears all subscriptions for a topic
       * @param {string} topic - Topic to clear
       * @returns {boolean} True if topic existed and was cleared
       */
      clearTopic: function (topic) {
        if (!topic || !topics[topic]) {
          return false;
        }

        delete topics[topic];
        return true;
      },

      /**
       * Gets the number of subscribers for a topic
       * @param {string} topic - Topic to check
       * @returns {number} Number of subscribers
       */
      getSubscriberCount: function (topic) {
        if (!topic || !topics[topic]) {
          return 0;
        }
        return topics[topic].length;
      },

      /**
       * Gets all active topics
       * @returns {string[]} Array of active topics
       */
      getTopics: function () {
        return Object.keys(topics);
      },
    };
  })();

  /**
   * Modern EventBus class for instance-based event handling
   * Used by advanced modules like Distributed Computing
   */
  class EventBusClass {
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

  // Attach EventBus to Prime (both legacy and class versions)
  Prime.EventBus = LegacyEventBus;
  Prime.EventBusClass = EventBusClass;
})(Prime);

// CommonJS export
if (typeof module !== 'undefined' && module.exports) {
  module.exports = Prime;
}
