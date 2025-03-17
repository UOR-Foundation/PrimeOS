/**
 * PrimeOS Shell Environment - Main Entry Point
 * 
 * This file initializes the Shell environment and exports the public API
 */

import { Shell } from './shell.js';

// Create global stylesheet link
function loadShellStyles() {
  // Don't add another stylesheet if it already exists
  if (document.querySelector('link[href*="shell.css"]')) return;
  
  // Wait for document.head to be available
  if (!document.head) {
    console.warn('Document head not available, deferring style loading');
    setTimeout(loadShellStyles, 10);
    return;
  }
  
  // Try to load CSS using dynamic import.meta.url (for ESM modules)
  try {
    const linkElement = document.createElement('link');
    linkElement.rel = 'stylesheet';
    
    // Use relative path instead of absolute to fix GitHub Pages deployment
    // This will look for shell.css in the same directory as index.js
    linkElement.href = new URL('./shell.css', import.meta.url).href;
    
    // Add load error handler with fallbacks
    linkElement.onerror = () => {
      console.warn('Failed to load shell.css using import.meta.url, trying fallback paths');
      
      // Try relative path as first fallback
      linkElement.href = './core/shell/shell.css';
      
      // Add another error handler for the second fallback
      linkElement.onerror = () => {
        console.warn('Failed to load shell.css with first fallback, trying second fallback');
        linkElement.href = 'core/shell/shell.css';
        
        // Final fallback error handler
        linkElement.onerror = () => {
          console.error('All attempts to load shell.css failed');
        };
      };
    };
    
    document.head.appendChild(linkElement);
  } catch (error) {
    console.error('Error loading shell styles with import.meta.url:', error);
    
    // Fallback to relative path if import.meta.url fails
    const fallbackLink = document.createElement('link');
    fallbackLink.rel = 'stylesheet';
    fallbackLink.href = './core/shell/shell.css';
    document.head.appendChild(fallbackLink);
  }
  
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
export function getShell() {
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
export async function initializeShell() {
  // Ensure styles are loaded first
  loadShellStyles();
  
  // Wait for document to be ready
  if (document.readyState !== 'complete' && document.readyState !== 'interactive') {
    await new Promise(resolve => {
      document.addEventListener('DOMContentLoaded', resolve, { once: true });
    });
  }
  
  // Create and initialize shell
  const shell = getShell();
  await shell.initialize();
  return shell;
}

// Make functions available to window for browser usage
if (typeof window !== 'undefined') {
  window.getShell = getShell;
  window.initializeShell = initializeShell;
}