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
  
  // Create inline styles instead of loading external CSS to ensure it works everywhere
  try {
    // Create a style element for shell styles
    const styleElement = document.createElement('style');
    styleElement.setAttribute('data-shell-styles', 'true');
    
    // Add the shell CSS inline
    styleElement.textContent = `
      /* Shell container */
      #prime-shell {
        position: fixed;
        top: 0;
        left: 0;
        width: 100%;
        height: 100%;
        overflow: hidden;
        font-family: 'Roboto', 'Segoe UI', Arial, sans-serif;
        font-size: var(--font-size-base, 14px);
        color: var(--text-color, #333);
        background-color: var(--bg-color, #f5f5f5);
        display: flex;
        flex-direction: column;
        z-index: 1000;
      }
      
      /* Desktop */
      .desktop {
        flex: 1;
        position: relative;
        overflow: hidden;
        background-size: cover;
        background-position: center;
        background-repeat: no-repeat;
        background-image: var(--desktop-bg, linear-gradient(45deg, #1a237e, #283593, #3949ab, #5c6bc0));
      }
      
      .windows-container {
        position: absolute;
        top: 0;
        left: 0;
        width: 100%;
        height: 100%;
        z-index: 10;
        pointer-events: none;
      }
      
      .windows-container .window {
        pointer-events: auto;
      }
      
      /* Taskbar */
      .taskbar {
        height: 48px;
        background-color: var(--taskbar-bg, rgba(20, 20, 30, 0.85));
        backdrop-filter: blur(5px);
        display: flex;
        align-items: center;
        padding: 0 12px;
        z-index: 1000;
        box-shadow: 0 -1px 3px rgba(0, 0, 0, 0.1);
      }
      
      .taskbar[data-position="top"] {
        order: -1;
        box-shadow: 0 1px 3px rgba(0, 0, 0, 0.1);
      }
      
      .start-button {
        width: 40px;
        height: 40px;
        border-radius: 8px;
        background-color: var(--accent-color, #5c6bc0);
        display: flex;
        align-items: center;
        justify-content: center;
        margin-right: 12px;
        cursor: pointer;
        transition: background-color 0.2s;
      }
      
      .start-button:hover {
        background-color: var(--accent-hover, #3949ab);
      }
      
      .start-button .icon {
        font-size: 22px;
        font-weight: bold;
        color: white;
      }
      
      .taskbar-items {
        display: flex;
        flex: 1;
        height: 100%;
        overflow-x: auto;
        overflow-y: hidden;
      }
      
      .taskbar-item {
        height: 40px;
        min-width: 160px;
        max-width: 200px;
        margin: 0 4px;
        padding: 0 12px;
        border-radius: 6px;
        background-color: var(--taskbar-item-bg, rgba(255, 255, 255, 0.1));
        display: flex;
        align-items: center;
        cursor: pointer;
        transition: background-color 0.2s;
        color: var(--taskbar-text, #fff);
        white-space: nowrap;
      }
      
      .taskbar-item.active {
        background-color: var(--taskbar-item-active, rgba(255, 255, 255, 0.25));
      }
      
      .taskbar-item.minimized-window {
        background-color: var(--taskbar-item-minimized, rgba(255, 255, 255, 0.1));
        box-shadow: inset 0 -2px 0 rgba(255, 255, 255, 0.3);
      }
      
      .taskbar-item:hover {
        background-color: var(--taskbar-item-hover, rgba(255, 255, 255, 0.2));
      }
      
      .taskbar-item .icon {
        margin-right: 8px;
        font-size: 18px;
      }
      
      .taskbar-item .title {
        overflow: hidden;
        text-overflow: ellipsis;
        white-space: nowrap;
      }
      
      .system-tray {
        display: flex;
        align-items: center;
        margin-left: auto;
      }
      
      .clock {
        padding: 0 12px;
        color: var(--taskbar-text, #fff);
        font-weight: 500;
      }
      
      .notification-icon {
        width: 32px;
        height: 32px;
        margin-left: 12px;
        border-radius: 6px;
        display: flex;
        align-items: center;
        justify-content: center;
        cursor: pointer;
        position: relative;
        color: var(--taskbar-text, #fff);
      }
      
      .notification-icon:hover {
        background-color: var(--taskbar-item-hover, rgba(255, 255, 255, 0.2));
      }
      
      .badge {
        position: absolute;
        top: -4px;
        right: -4px;
        background-color: var(--notification-badge, #e53935);
        color: white;
        border-radius: 10px;
        padding: 0 6px;
        font-size: 10px;
        min-width: 16px;
        height: 16px;
        display: flex;
        align-items: center;
        justify-content: center;
      }
      
      /* App Launcher */
      .app-launcher {
        position: absolute;
        left: 0;
        bottom: 48px;
        width: 600px;
        height: 440px;
        background-color: var(--app-launcher-bg, rgba(30, 30, 40, 0.95));
        backdrop-filter: blur(10px);
        border-radius: 12px;
        box-shadow: 0 5px 20px rgba(0, 0, 0, 0.3);
        z-index: 1100;
        display: flex;
        flex-direction: column;
        overflow: hidden;
        margin: 0 12px;
        border: 1px solid var(--border-color, rgba(255, 255, 255, 0.1));
        color: var(--app-launcher-text, #fff);
        transition: transform 0.3s, opacity 0.3s;
      }
      
      .app-launcher.hidden {
        transform: translateY(20px);
        opacity: 0;
        pointer-events: none;
      }
      
      .app-launcher-search {
        padding: 16px;
        border-bottom: 1px solid var(--border-color, rgba(255, 255, 255, 0.1));
      }
      
      .app-launcher-search input {
        width: 100%;
        padding: 10px 16px;
        border-radius: 8px;
        border: none;
        background-color: var(--input-bg, rgba(255, 255, 255, 0.1));
        color: var(--input-text, #fff);
        font-size: 14px;
        outline: none;
      }
      
      .app-launcher-search input::placeholder {
        color: var(--input-placeholder, rgba(255, 255, 255, 0.5));
      }
      
      .app-grid {
        flex: 1;
        display: grid;
        grid-template-columns: repeat(4, 1fr);
        grid-gap: 8px;
        padding: 16px;
        overflow-y: auto;
      }
      
      .app-item {
        display: flex;
        flex-direction: column;
        align-items: center;
        justify-content: center;
        padding: 16px;
        border-radius: 12px;
        cursor: pointer;
        transition: all 0.2s ease-in-out;
        background-color: rgba(255, 255, 255, 0.05);
        box-shadow: 0 2px 8px rgba(0, 0, 0, 0.1);
        margin: 4px;
        border: 1px solid rgba(255, 255, 255, 0.1);
      }
      
      .app-item:hover {
        background-color: var(--app-item-hover, rgba(255, 255, 255, 0.15));
        transform: translateY(-3px);
        box-shadow: 0 5px 15px rgba(0, 0, 0, 0.2);
        border-color: rgba(255, 255, 255, 0.3);
      }
      
      .app-icon {
        width: 60px;
        height: 60px;
        display: flex;
        align-items: center;
        justify-content: center;
        font-size: 28px;
        margin-bottom: 12px;
        background-color: var(--app-icon-bg, rgba(255, 255, 255, 0.15));
        border-radius: 16px;
        box-shadow: 0 3px 10px rgba(0, 0, 0, 0.1);
        transition: all 0.2s ease;
      }
      
      .app-item:hover .app-icon {
        transform: scale(1.1);
        background-color: rgba(255, 255, 255, 0.25);
      }
      
      .app-name {
        font-size: 14px;
        font-weight: 500;
        text-align: center;
        white-space: nowrap;
        overflow: hidden;
        text-overflow: ellipsis;
        max-width: 100%;
        color: rgba(255, 255, 255, 0.9);
        text-shadow: 0 1px 2px rgba(0, 0, 0, 0.2);
        transition: color 0.2s ease;
      }
      
      .app-item:hover .app-name {
        color: #ffffff;
      }
      
      /* Notification Center */
      .notification-center {
        position: absolute;
        right: 0;
        bottom: 48px;
        width: 320px;
        max-height: 560px;
        background-color: var(--notification-center-bg, rgba(30, 30, 40, 0.95));
        backdrop-filter: blur(10px);
        border-radius: 12px;
        box-shadow: 0 5px 20px rgba(0, 0, 0, 0.3);
        z-index: 1100;
        display: flex;
        flex-direction: column;
        overflow: hidden;
        margin: 0 12px;
        border: 1px solid var(--border-color, rgba(255, 255, 255, 0.1));
        color: var(--notification-center-text, #fff);
        transition: transform 0.3s, opacity 0.3s;
      }
      
      .notification-center.hidden {
        transform: translateY(20px);
        opacity: 0;
        pointer-events: none;
      }
      
      .notification-header {
        padding: 16px;
        border-bottom: 1px solid var(--border-color, rgba(255, 255, 255, 0.1));
        display: flex;
        justify-content: space-between;
        align-items: center;
      }
      
      .notification-header h3 {
        margin: 0;
        font-size: 16px;
        font-weight: 500;
      }
      
      .notification-header button {
        background: none;
        border: none;
        color: var(--notification-center-text, #fff);
        opacity: 0.7;
        cursor: pointer;
        padding: 4px 8px;
        border-radius: 4px;
      }
      
      .notification-header button:hover {
        opacity: 1;
        background-color: var(--button-hover, rgba(255, 255, 255, 0.1));
      }
      
      .notifications-list {
        flex: 1;
        overflow-y: auto;
        padding: 8px;
      }
      
      .notification {
        background-color: var(--notification-bg, rgba(255, 255, 255, 0.1));
        border-radius: 8px;
        margin-bottom: 8px;
        overflow: hidden;
      }
      
      .empty-notifications {
        display: flex;
        align-items: center;
        justify-content: center;
        height: 120px;
        opacity: 0.5;
      }
      
      /* Windows */
      .window {
        position: absolute;
        background-color: var(--window-bg, #fff);
        border-radius: 8px;
        box-shadow: 0 8px 24px rgba(0, 0, 0, 0.15);
        display: flex;
        flex-direction: column;
        overflow: hidden;
        transition: box-shadow 0.2s, transform 0.2s;
        min-width: 320px;
        min-height: 240px;
        z-index: 10;
      }
      
      .window.active {
        box-shadow: 0 12px 32px rgba(0, 0, 0, 0.25);
        transform: translateY(-2px);
        z-index: 1000;
      }
      
      .window.minimized {
        /* Hide but keep in DOM for event handlers */
        visibility: hidden;
        opacity: 0;
        transform: scale(0.8);
        pointer-events: none;
        position: absolute;
        z-index: -1;
      }
      
      .window.maximized {
        top: 0 !important;
        left: 0 !important;
        width: 100% !important;
        height: 100% !important;
        border-radius: 0;
      }
      
      .window-titlebar {
        height: 36px;
        background-color: var(--titlebar-bg, #f5f5f5);
        display: flex;
        align-items: center;
        padding: 0 12px;
        justify-content: space-between;
        cursor: default;
        user-select: none;
      }
      
      .window-title {
        font-size: 14px;
        font-weight: 500;
        overflow: hidden;
        text-overflow: ellipsis;
        white-space: nowrap;
        color: var(--window-title, #333);
      }
      
      .window-controls {
        display: flex;
        gap: 8px;
      }
      
      .window-control {
        width: 20px;
        height: 20px;
        border: none;
        background: none;
        border-radius: 50%;
        display: flex;
        align-items: center;
        justify-content: center;
        cursor: pointer;
        font-size: 14px;
        padding: 0;
        color: var(--control-icon, #555);
      }
      
      .window-minimize {
        background-color: var(--minimize-bg, #ffbd2e);
      }
      
      .window-maximize {
        background-color: var(--maximize-bg, #28c941);
      }
      
      .window-close {
        background-color: var(--close-bg, #ff5f57);
      }
      
      .window-content {
        flex: 1;
        overflow: auto;
        position: relative;
        background-color: var(--content-bg, #fff);
      }
      
      .window-resize-handle {
        position: absolute;
        bottom: 0;
        right: 0;
        width: 16px;
        height: 16px;
        cursor: nwse-resize;
        background: linear-gradient(135deg, transparent 50%, rgba(0, 0, 0, 0.1) 50%);
      }
      
      /* Login screen */
      .login-screen {
        position: fixed;
        top: 0;
        left: 0;
        width: 100%;
        height: 100%;
        background: linear-gradient(45deg, #1a237e, #283593, #3949ab, #5c6bc0);
        display: flex;
        align-items: center;
        justify-content: center;
        z-index: 9999;
      }
      
      .login-card {
        width: 360px;
        background-color: rgba(255, 255, 255, 0.95);
        border-radius: 12px;
        box-shadow: 0 8px 32px rgba(0, 0, 0, 0.2);
        overflow: hidden;
      }
      
      .login-header {
        padding: 24px;
        text-align: center;
        background-color: rgba(0, 0, 0, 0.02);
        border-bottom: 1px solid rgba(0, 0, 0, 0.05);
      }
      
      .login-header h2 {
        margin: 0 0 8px;
        font-size: 24px;
        font-weight: 500;
        color: #333;
      }
      
      .login-header p {
        margin: 0;
        opacity: 0.7;
        font-size: 14px;
      }
      
      .login-form {
        padding: 24px;
      }
      
      .form-group {
        margin-bottom: 16px;
      }
      
      .form-group label {
        display: block;
        margin-bottom: 8px;
        font-size: 14px;
        font-weight: 500;
        color: #555;
      }
      
      .form-group input {
        width: 100%;
        padding: 10px 12px;
        font-size: 14px;
        border: 1px solid rgba(0, 0, 0, 0.1);
        border-radius: 6px;
        background-color: white;
        transition: border-color 0.2s;
      }
      
      .form-group input:focus {
        outline: none;
        border-color: var(--accent-color, #5c6bc0);
      }
      
      .form-actions {
        display: flex;
        justify-content: space-between;
        margin-top: 24px;
      }
      
      .btn-primary, .btn-secondary {
        padding: 10px 16px;
        border: none;
        border-radius: 6px;
        font-size: 14px;
        font-weight: 500;
        cursor: pointer;
        transition: background-color 0.2s;
      }
      
      .btn-primary {
        background-color: var(--accent-color, #5c6bc0);
        color: white;
      }
      
      .btn-primary:hover {
        background-color: var(--accent-hover, #3949ab);
      }
      
      .btn-secondary {
        background-color: rgba(0, 0, 0, 0.15);
        color: #333;
      }
      
      .btn-secondary:hover {
        background-color: rgba(0, 0, 0, 0.25);
      }
      
      .login-footer {
        padding: 16px;
        text-align: center;
        background-color: rgba(0, 0, 0, 0.02);
        border-top: 1px solid rgba(0, 0, 0, 0.05);
      }
      
      .login-footer p {
        margin: 0;
        font-size: 12px;
        opacity: 0.7;
      }
    `;
    
    // Add the style element to the document head
    document.head.appendChild(styleElement);
    console.log('Embedded shell styles directly in the page');
  } catch (error) {
    console.error('Error loading shell styles:', error);
    
    // Final fallback - try to load the CSS from multiple possible locations
    const possiblePaths = [
      './shell.css',                            // Same directory
      '../core/shell/shell.css',                // Relative to JS directory 
      './core/shell/shell.css',                 // Relative to base
      'core/shell/shell.css',                   // No leading slash
      '/core/shell/shell.css',                  // Absolute from root
      '/reference-implementation/core/shell/shell.css',  // GitHub Pages path
      '/PrimeOS/reference-implementation/core/shell/shell.css'  // Full repo path
    ];
    
    // Try each path with proper error handling
    tryNextCssPath(possiblePaths, 0);
  }
  
  // Helper function to try loading CSS from different paths
  function tryNextCssPath(paths, index) {
    if (index >= paths.length) {
      console.error('All CSS loading attempts failed');
      return;
    }
    
    const link = document.createElement('link');
    link.rel = 'stylesheet';
    link.href = paths[index];
    
    link.onerror = () => {
      console.warn(`Failed to load CSS from ${paths[index]}, trying next path`);
      tryNextCssPath(paths, index + 1);
    };
    
    link.onload = () => {
      console.log(`Successfully loaded CSS from ${paths[index]}`);
    };
    
    document.head.appendChild(link);
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