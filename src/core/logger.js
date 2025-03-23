/**
 * PrimeOS JavaScript Library - Core Logger
 * Logging system with configurable levels
 */

// Import the Prime object from prime.js
const Prime = require("./prime");

// Create the Logger module using IIFE
(function () {
  /**
   * Internal logger with configurable levels
   */
  const Logger = {
    levels: {
      DEBUG: 0,
      INFO: 1,
      WARN: 2,
      ERROR: 3,
      NONE: 4,
    },

    currentLevel: 1, // Default to INFO

    /**
     * Set the logging level
     * @param {string|number} level - Log level as string name or number
     * @throws {ValidationError} If level is invalid
     */
    setLevel: function (level) {
      if (Prime.Utils.isString(level)) {
        if (this.levels[level.toUpperCase()] !== undefined) {
          this.currentLevel = this.levels[level.toUpperCase()];
        } else {
          throw new Prime.ValidationError(`Invalid log level: ${level}`);
        }
      } else if (Prime.Utils.isNumber(level) && level >= 0 && level <= 4) {
        this.currentLevel = level;
      } else {
        throw new Prime.ValidationError(
          "Log level must be a valid string or number",
        );
      }
    },

    /**
     * Check if a message at the given level should be logged
     * @private
     * @param {string} level - Log level to check
     * @returns {boolean} Whether the message should be logged
     */
    shouldLog: function (level) {
      return this.levels[level] >= this.currentLevel;
    },

    /**
     * Format a log message
     * @private
     * @param {string} level - Log level
     * @param {string} message - The message to format
     * @param {Object} [context] - Optional context object for structured logging
     * @returns {string} Formatted log message
     */
    format: function (level, message, context) {
      // Format message with optional context
      let formattedMessage = `[Prime] [${level}] ${message}`;

      // Add context if available
      if (context && typeof context === "object") {
        formattedMessage += `\nContext: ${JSON.stringify(context)}`;
      }

      return formattedMessage;
    },

    /**
     * Log a debug message
     * @param {...any} args - Log arguments
     */
    debug: function (...args) {
      if (this.shouldLog("DEBUG")) {
        console.debug(
          this.format("DEBUG", args[0]),
          ...(args.length > 1 ? args.slice(1) : []),
        );
      }
    },

    /**
     * Log an info message
     * @param {...any} args - Log arguments
     */
    info: function (...args) {
      if (this.shouldLog("INFO")) {
        console.info(
          this.format("INFO", args[0]),
          ...(args.length > 1 ? args.slice(1) : []),
        );
      }
    },

    /**
     * Log a warning message
     * @param {...any} args - Log arguments
     */
    warn: function (...args) {
      if (this.shouldLog("WARN")) {
        console.warn(
          this.format("WARN", args[0]),
          ...(args.length > 1 ? args.slice(1) : []),
        );
      }
    },

    /**
     * Log an error message
     * @param {...any} args - Log arguments
     */
    error: function (...args) {
      if (this.shouldLog("ERROR")) {
        console.error(
          this.format("ERROR", args[0]),
          ...(args.length > 1 ? args.slice(1) : []),
        );
      }
    },
  };

  // Add Logger to the Prime object
  Prime.Logger = Logger;
})();

// Export the enhanced Prime object
module.exports = Prime;
