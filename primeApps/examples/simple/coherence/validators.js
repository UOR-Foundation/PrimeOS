/**
 * Simple Example PrimeApp Validators
 */

const { PrimeError } = require('../../../../src/core/error');

class MessageValidator {
  /**
   * Validate a message
   * @param {string} message - Message to validate
   * @returns {Object} - Validation result
   */
  validate(message) {
    const isValid = typeof message === 'string' && message.length > 0;
    const coherenceScore = isValid ? 0.9 : 0;
    
    return {
      valid: isValid,
      score: coherenceScore,
      details: isValid ? null : "Invalid message format"
    };
  }
}

module.exports = {
  MessageValidator
};