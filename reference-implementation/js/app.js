/**
 * PrimeOS Reference Implementation - Main Application
 * 
 * This file initializes the PrimeOS Shell environment and serves as the entry point for the application.
 */

// Event Bus from framework.js
const { EventBus } = window.Prime || {};

// Loading states
const LOADING_STATES = [
  'Initializing core systems...',
  'Loading components...',
  'Establishing coherence...',
  'Optimizing calculations...',
  'Preparing user interface...',
  'Starting services...',
  'Validating system integrity...'
];

/**
 * Update the loading message
 * @param {string} message - The message to display
 */
function updateLoadingMessage(message) {
  const loadingText = document.querySelector('.loading-text');
  if (loadingText) {
    loadingText.textContent = message;
  }
}

/**
 * Animate the loading sequence
 */
async function animateLoading() {
  const loader = document.querySelector('.loader-bar');
  if (!loader) return;
  
  // Start with 0% width
  loader.style.width = '0%';
  
  // Animate to 100% width
  for (let i = 0; i < LOADING_STATES.length; i++) {
    const progress = (i / LOADING_STATES.length) * 100;
    loader.style.width = `${progress}%`;
    updateLoadingMessage(LOADING_STATES[i]);
    
    // Wait for a random time between 400-800ms
    await new Promise(resolve => setTimeout(resolve, 400 + Math.random() * 400));
  }
  
  // Final state
  loader.style.width = '100%';
  updateLoadingMessage('Ready to launch...');
  
  // Wait a moment before hiding
  await new Promise(resolve => setTimeout(resolve, 500));
}

/**
 * Initialize the application
 */
async function initializeApp() {
  try {
    console.log('%cPrimeOS Reference Implementation', 'font-size: 16px; font-weight: bold; color: #3498db;');
    
    // Check if Prime library is loaded, or create a mock for development
    if (!window.Prime) {
      console.warn('PrimeOS library not loaded. Creating a mock version for demonstration.');
      window.Prime = {
        version: '1.0.0 (Mock)',
        Utils: {
          uuid: function() {
            return 'xxxx-xxxx-xxxx-xxxx'.replace(/x/g, () => 
                Math.floor(Math.random() * 16).toString(16));
          },
          isObject: (obj) => obj !== null && typeof obj === 'object' && !Array.isArray(obj),
          isFunction: (fn) => typeof fn === 'function',
          isArray: Array.isArray,
          deepClone: (obj) => JSON.parse(JSON.stringify(obj))
        },
        Logger: {
          setLevel: function(level) {
            console.log(`Log level set to: ${level}`);
          }
        }
      };
    }
    
    // Set log level based on URL parameter
    if (window.Prime && Prime.Logger) {
      const urlParams = new URLSearchParams(window.location.search);
      const logLevel = urlParams.get('log') || 'info';
      Prime.Logger.setLevel(logLevel.toUpperCase());
    }
    
    // Animate loading sequence
    await animateLoading();
    
    // Initialize the shell
    if (typeof window.initializeShell !== 'function') {
      throw new Error('Shell initialization function not found. Make sure core/shell/index.js is properly loaded.');
    }
    
    const shell = await window.initializeShell();
    
    // Hide loading screen
    const loadingScreen = document.getElementById('loading');
    if (loadingScreen) {
      loadingScreen.style.opacity = '0';
      setTimeout(() => {
        loadingScreen.style.display = 'none';
      }, 300);
    }
    
    console.log('PrimeOS Reference Implementation initialized successfully');
    
    // Listen for shell events
    if (EventBus) {
      EventBus.subscribe('shell:ready', (data) => {
        console.log('Shell ready event received', data);
      });
    }
  } catch (error) {
    console.error('Failed to initialize PrimeOS:', error);
    updateLoadingMessage(`Error: ${error.message}`);
    showError(error.message);
  }
}

/**
 * Display error message to user
 * @param {string} message - Error message to display
 */
function showError(message) {
  console.error(message);
  
  // Create error toast
  const errorToast = document.createElement('div');
  errorToast.className = 'error-toast';
  errorToast.innerHTML = `
    <div class="error-toast-header">
      <strong>Error</strong>
      <button class="close-error">×</button>
    </div>
    <div class="error-toast-body">
      <p>${message}</p>
    </div>
  `;
  
  // Add to the document
  document.body.appendChild(errorToast);
  
  // Add close button handler
  const closeBtn = errorToast.querySelector('.close-error');
  if (closeBtn) {
    closeBtn.addEventListener('click', () => {
      errorToast.remove();
    });
  }
  
  // Auto-remove after 10 seconds
  setTimeout(() => {
    if (document.body.contains(errorToast)) {
      errorToast.remove();
    }
  }, 10000);
}

// Initialize the application when the document is ready
document.addEventListener('DOMContentLoaded', initializeApp);