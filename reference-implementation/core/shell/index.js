/**
 * PrimeOS Shell Environment - Main Entry Point
 * 
 * This file initializes the Shell environment and exports the public API
 */

const { Shell } = require('./shell');

// Create global stylesheet link
function loadShellStyles() {
  // Don't add another stylesheet if it already exists
  if (document.querySelector('link[href*="shell.css"]')) return;
  
  const linkElement = document.createElement('link');
  linkElement.rel = 'stylesheet';
  linkElement.href = '/reference-implementation/core/shell/shell.css';
  document.head.appendChild(linkElement);
  
  // Also add Google Fonts for Roboto
  const fontLink = document.createElement('link');
  fontLink.rel = 'stylesheet';
  fontLink.href = 'https://fonts.googleapis.com/css2?family=Roboto:wght@300;400;500;700&display=swap';
  document.head.appendChild(fontLink);
}

// Initialize shell instance
let shellInstance = null;

/**
 * Get the shell instance, creating it if it doesn't exist
 * @returns {Shell} The shell instance
 */
function getShell() {
  if (!shellInstance) {
    // Load shell styles
    loadShellStyles();
    
    // Create new Shell instance
    shellInstance = new Shell();
  }
  
  return shellInstance;
}

/**
 * Initialize the shell environment
 * @returns {Promise<Shell>} The initialized shell instance
 */
async function initializeShell() {
  const shell = getShell();
  await shell.initialize();
  return shell;
}

module.exports = {
  getShell,
  initializeShell
};