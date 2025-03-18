/**
 * PrimeOS Settings Components
 * 
 * Exports all UI components for the Settings application
 */

// Import components
const { SettingsPanel } = require('./settings-panel');
const { SecretsManager } = require('./secrets-manager');

// Export all components
module.exports = {
  SettingsPanel,
  SecretsManager
};

// For browser environment
if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  
  if (!window.PrimeOS.Settings) {
    window.PrimeOS.Settings = {};
  }
  
  window.PrimeOS.Settings.Components = {
    SettingsPanel,
    SecretsManager
  };
}