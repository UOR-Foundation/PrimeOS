/**
 * PrimeOS Settings Models
 * 
 * Exports all model classes for the Settings application
 */

// Import models
const { SettingsStore } = require('./settings-store');

// Export all models
module.exports = {
  SettingsStore
};

// For browser environment
if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  
  if (!window.PrimeOS.Settings) {
    window.PrimeOS.Settings = {};
  }
  
  window.PrimeOS.Settings.Models = {
    SettingsStore
  };
}