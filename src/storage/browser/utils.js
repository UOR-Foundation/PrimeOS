/**
 * PrimeOS JavaScript Library - Browser Storage Utilities
 * Utility functions for browser storage providers
 */

const Prime = require('../../core');
const { PrimeStorageError } = require('../core/provider');

/**
 * Utility functions for browser storage
 */
const BrowserStorageUtils = {
  /**
   * Checks if the browser supports IndexedDB
   * @returns {boolean} True if IndexedDB is supported
   */
  isIndexedDBSupported() {
    if (typeof window === 'undefined') {
      return false;
    }
    
    return Boolean(window.indexedDB);
  },

  /**
   * Checks if the browser supports localStorage
   * @returns {boolean} True if localStorage is supported
   */
  isLocalStorageSupported() {
    if (typeof window === 'undefined' || typeof localStorage === 'undefined') {
      return false;
    }
    
    try {
      const testKey = '__primeos_test__';
      localStorage.setItem(testKey, 'test');
      localStorage.removeItem(testKey);
      return true;
    } catch (e) {
      return false;
    }
  },

  /**
   * Checks if the browser supports the File System Access API
   * @returns {boolean} True if File System Access API is supported
   */
  isFileSystemAccessSupported() {
    if (typeof window === 'undefined') {
      return false;
    }
    
    return Boolean(window.showDirectoryPicker && window.showOpenFilePicker);
  },

  /**
   * Gets the available browser storage options
   * @returns {Object} Available storage options
   */
  getAvailableStorageOptions() {
    return {
      indexedDB: this.isIndexedDBSupported(),
      localStorage: this.isLocalStorageSupported(),
      fileSystemAccess: this.isFileSystemAccessSupported()
    };
  },

  /**
   * Gets the best available storage method
   * @returns {string} Name of the best available storage method
   */
  getBestAvailableStorage() {
    const options = this.getAvailableStorageOptions();
    
    if (options.indexedDB) {
      return 'indexeddb';
    } else if (options.localStorage) {
      return 'localstorage';
    } else {
      return 'memory';
    }
  },

  /**
   * Estimates available storage space
   * @returns {Promise<Object>} Storage space information
   */
  async estimateStorageSpace() {
    if (typeof navigator !== 'undefined' && navigator.storage && navigator.storage.estimate) {
      try {
        const estimate = await navigator.storage.estimate();
        
        return {
          quota: estimate.quota || 0,
          usage: estimate.usage || 0,
          available: (estimate.quota || 0) - (estimate.usage || 0),
          persistent: false
        };
      } catch (error) {
        Prime.Logger.warn('Failed to estimate storage space', { error: error.message });
      }
    }
    
    // Fallback values if Storage API isn't available
    return {
      quota: 50 * 1024 * 1024, // 50MB
      usage: 0,
      available: 50 * 1024 * 1024,
      persistent: false
    };
  },

  /**
   * Requests persistent storage permission
   * @returns {Promise<boolean>} True if permission was granted
   */
  async requestPersistentStorage() {
    if (typeof navigator !== 'undefined' && navigator.storage && navigator.storage.persist) {
      try {
        return await navigator.storage.persist();
      } catch (error) {
        Prime.Logger.warn('Failed to request persistent storage', { error: error.message });
        return false;
      }
    }
    
    return false;
  },

  /**
   * Checks if storage is persistent
   * @returns {Promise<boolean>} True if storage is persistent
   */
  async isStoragePersistent() {
    if (typeof navigator !== 'undefined' && navigator.storage && navigator.storage.persisted) {
      try {
        return await navigator.storage.persisted();
      } catch (error) {
        Prime.Logger.warn('Failed to check storage persistence', { error: error.message });
        return false;
      }
    }
    
    return false;
  },

  /**
   * Creates a download link for data
   * @param {*} data - Data to download
   * @param {string} filename - Filename for the download
   * @param {string} [mimeType='application/octet-stream'] - MIME type of the data
   * @returns {string} URL for downloading the data
   */
  createDownloadLink(data, filename, mimeType = 'application/octet-stream') {
    if (typeof window === 'undefined' || typeof URL === 'undefined') {
      throw new PrimeStorageError(
        'Download functionality is only available in browser environments',
        {},
        'STORAGE_BROWSER_ONLY'
      );
    }
    
    let blob;
    
    if (data instanceof Blob) {
      blob = data;
    } else if (typeof Buffer !== 'undefined' && Buffer.isBuffer(data)) {
      blob = new Blob([data], { type: mimeType });
    } else if (ArrayBuffer.isView(data) || data instanceof ArrayBuffer) {
      blob = new Blob([data], { type: mimeType });
    } else if (typeof data === 'string') {
      blob = new Blob([data], { type: mimeType });
    } else {
      // For other types, try to JSON stringify
      try {
        const jsonStr = JSON.stringify(data);
        blob = new Blob([jsonStr], { type: 'application/json' });
      } catch (e) {
        throw new PrimeStorageError(
          'Unable to convert data to blob',
          { type: typeof data },
          'STORAGE_INVALID_DATA'
        );
      }
    }
    
    return URL.createObjectURL(blob);
  },

  /**
   * Initiates a download of data
   * @param {*} data - Data to download
   * @param {string} filename - Filename for the download
   * @param {string} [mimeType='application/octet-stream'] - MIME type of the data
   */
  downloadData(data, filename, mimeType = 'application/octet-stream') {
    const url = this.createDownloadLink(data, filename, mimeType);
    
    const a = document.createElement('a');
    a.href = url;
    a.download = filename;
    a.style.display = 'none';
    
    document.body.appendChild(a);
    a.click();
    
    // Clean up
    setTimeout(() => {
      document.body.removeChild(a);
      URL.revokeObjectURL(url);
    }, 100);
  }
};

module.exports = BrowserStorageUtils;