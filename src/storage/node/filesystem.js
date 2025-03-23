/**
 * PrimeOS JavaScript Library - Filesystem Storage Provider
 * Node.js-based storage provider using the filesystem
 */

const Prime = require('../../core');
const { StorageProvider, PrimeStorageError } = require('../core/provider');
const { EventEmitter } = require('events');
const path = require('path');
const fs = require('fs');
const os = require('os');

/**
 * Filesystem-based storage provider for Node.js
 */
class FilesystemProvider extends StorageProvider {
  /**
   * Creates a new filesystem provider
   * @param {StorageOptions} options - Storage options
   */
  constructor(options = {}) {
    super(options);
    
    // Set storage path
    this.options.storagePath = this.options.storagePath || 
      path.join(os.tmpdir(), 'primeos-storage');
    
    this.isInitialized = false;
  }

  /**
   * Initializes the filesystem provider
   * @returns {Promise<void>}
   */
  async init() {
    // Check environment
    if (typeof process === 'undefined' || typeof fs === 'undefined') {
      throw new PrimeStorageError(
        'Filesystem provider is only available in Node.js',
        {},
        'STORAGE_FS_UNAVAILABLE'
      );
    }
    
    try {
      // Ensure storage directory exists
      await this.ensureDirectory(this.options.storagePath);
      
      // Test write permissions
      await this.testWritePermissions();
      
      this.isInitialized = true;
    } catch (error) {
      throw new PrimeStorageError(
        `Failed to initialize filesystem provider: ${error.message}`,
        { path: this.options.storagePath, originalError: error },
        'STORAGE_FS_INIT_FAILED',
        error
      );
    }
  }

  /**
   * Ensures a directory exists
   * @private
   * @param {string} dir - Directory path
   * @returns {Promise<void>}
   */
  async ensureDirectory(dir) {
    return new Promise((resolve, reject) => {
      fs.mkdir(dir, { recursive: true }, (err) => {
        if (err) {
          reject(new Error(`Failed to create directory ${dir}: ${err.message}`));
        } else {
          resolve();
        }
      });
    });
  }

  /**
   * Tests write permissions
   * @private
   * @returns {Promise<void>}
   */
  async testWritePermissions() {
    const testFile = path.join(this.options.storagePath, '.permission_test');
    
    return new Promise((resolve, reject) => {
      fs.writeFile(testFile, 'test', (err) => {
        if (err) {
          reject(new PrimeStorageError(
            `No write permission for storage path: ${err.message}`,
            { path: this.options.storagePath },
            'STORAGE_PERMISSION_DENIED',
            err
          ));
          return;
        }
        
        fs.unlink(testFile, (unlinkErr) => {
          // Ignore unlink errors
          resolve();
        });
      });
    });
  }

  /**
   * Gets the file path for an ID
   * @private
   * @param {string} id - Data ID
   * @returns {string} File path
   */
  getFilePath(id) {
    return path.join(this.options.storagePath, `${id}.data`);
  }

  /**
   * Gets the metadata file path for an ID
   * @private
   * @param {string} id - Data ID
   * @returns {string} Metadata file path
   */
  getMetadataPath(id) {
    return path.join(this.options.storagePath, `${id}.meta`);
  }

  /**
   * Stores data with the given ID
   * @param {*} data - Data to store
   * @param {string} [id] - Optional ID (if not provided, a UUID will be generated)
   * @returns {Promise<string>} The ID of the stored data
   */
  async store(data, id) {
    const dataId = id || Prime.Utils.uuid();
    const filePath = this.getFilePath(dataId);
    const metadataPath = this.getMetadataPath(dataId);
    
    // Prepare data for storage
    let dataToWrite;
    let metadata = {
      id: dataId,
      contentType: 'application/json',
      timestamp: Date.now()
    };
    
    // Handle different data types
    if (typeof data === 'string') {
      dataToWrite = data;
      metadata.contentType = 'text/plain';
    } else if (typeof Buffer !== 'undefined' && Buffer.isBuffer(data)) {
      dataToWrite = data;
      metadata.contentType = 'application/octet-stream';
    } else if (ArrayBuffer.isView(data) || data instanceof ArrayBuffer) {
      dataToWrite = Buffer.from(data);
      metadata.contentType = 'application/octet-stream';
    } else {
      // For other types, serialize to JSON
      try {
        dataToWrite = JSON.stringify(data);
        metadata.contentType = 'application/json';
      } catch (error) {
        throw new PrimeStorageError(
          `Failed to serialize data: ${error.message}`,
          { originalError: error },
          'STORAGE_SERIALIZATION_FAILED',
          error
        );
      }
    }
    
    // Write data and metadata
    await Promise.all([
      this.writeFile(filePath, dataToWrite),
      this.writeFile(metadataPath, JSON.stringify(metadata))
    ]);
    
    return dataId;
  }

  /**
   * Writes data to a file
   * @private
   * @param {string} filePath - Path to write to
   * @param {*} data - Data to write
   * @returns {Promise<void>}
   */
  async writeFile(filePath, data) {
    return new Promise((resolve, reject) => {
      fs.writeFile(filePath, data, (err) => {
        if (err) {
          reject(new PrimeStorageError(
            `Failed to write file: ${err.message}`,
            { path: filePath },
            'STORAGE_WRITE_FAILED',
            err
          ));
        } else {
          resolve();
        }
      });
    });
  }

  /**
   * Loads data with the given ID
   * @param {string} id - ID of the data to load
   * @returns {Promise<*>} The loaded data
   */
  async load(id) {
    const filePath = this.getFilePath(id);
    const metadataPath = this.getMetadataPath(id);
    
    // Check if file exists
    if (!await this.fileExists(filePath)) {
      throw new PrimeStorageError(
        `Data not found for ID: ${id}`,
        { id, path: filePath },
        'STORAGE_NOT_FOUND'
      );
    }
    
    try {
      // Load metadata if available
      let metadata = { contentType: 'application/json' };
      if (await this.fileExists(metadataPath)) {
        const metadataContent = await this.readFile(metadataPath, 'utf8');
        metadata = JSON.parse(metadataContent);
      }
      
      // Read data based on content type
      if (metadata.contentType === 'application/json') {
        const content = await this.readFile(filePath, 'utf8');
        return JSON.parse(content);
      } else if (metadata.contentType === 'text/plain') {
        return this.readFile(filePath, 'utf8');
      } else {
        // Binary data
        return this.readFile(filePath);
      }
    } catch (error) {
      throw new PrimeStorageError(
        `Failed to load data: ${error.message}`,
        { id, path: filePath, originalError: error },
        'STORAGE_LOAD_FAILED',
        error
      );
    }
  }

  /**
   * Reads a file
   * @private
   * @param {string} filePath - Path to read from
   * @param {string} [encoding] - Optional encoding
   * @returns {Promise<*>} File contents
   */
  async readFile(filePath, encoding) {
    return new Promise((resolve, reject) => {
      fs.readFile(filePath, encoding, (err, data) => {
        if (err) {
          reject(new PrimeStorageError(
            `Failed to read file: ${err.message}`,
            { path: filePath },
            'STORAGE_READ_FAILED',
            err
          ));
        } else {
          resolve(data);
        }
      });
    });
  }

  /**
   * Checks if a file exists
   * @private
   * @param {string} filePath - Path to check
   * @returns {Promise<boolean>} True if file exists
   */
  async fileExists(filePath) {
    return new Promise((resolve) => {
      fs.access(filePath, fs.constants.F_OK, (err) => {
        resolve(!err);
      });
    });
  }

  /**
   * Deletes data with the given ID
   * @param {string} id - ID of the data to delete
   * @returns {Promise<boolean>} True if successful
   */
  async delete(id) {
    const filePath = this.getFilePath(id);
    const metadataPath = this.getMetadataPath(id);
    
    const fileExists = await this.fileExists(filePath);
    
    if (!fileExists) {
      return false;
    }
    
    try {
      // Delete data file
      await this.deleteFile(filePath);
      
      // Delete metadata file if it exists
      if (await this.fileExists(metadataPath)) {
        await this.deleteFile(metadataPath);
      }
      
      return true;
    } catch (error) {
      throw new PrimeStorageError(
        `Failed to delete data: ${error.message}`,
        { id, path: filePath, originalError: error },
        'STORAGE_DELETE_FAILED',
        error
      );
    }
  }

  /**
   * Deletes a file
   * @private
   * @param {string} filePath - Path to delete
   * @returns {Promise<void>}
   */
  async deleteFile(filePath) {
    return new Promise((resolve, reject) => {
      fs.unlink(filePath, (err) => {
        if (err) {
          reject(new PrimeStorageError(
            `Failed to delete file: ${err.message}`,
            { path: filePath },
            'STORAGE_DELETE_FAILED',
            err
          ));
        } else {
          resolve();
        }
      });
    });
  }

  /**
   * Checks if data with the given ID exists
   * @param {string} id - ID to check
   * @returns {Promise<boolean>} True if data exists
   */
  async exists(id) {
    const filePath = this.getFilePath(id);
    return this.fileExists(filePath);
  }

  /**
   * Lists all stored data IDs
   * @returns {Promise<string[]>} Array of stored data IDs
   */
  async getAllKeys() {
    return new Promise((resolve, reject) => {
      fs.readdir(this.options.storagePath, (err, files) => {
        if (err) {
          reject(new PrimeStorageError(
            `Failed to list files: ${err.message}`,
            { path: this.options.storagePath },
            'STORAGE_LIST_FAILED',
            err
          ));
          return;
        }
        
        // Filter data files and extract IDs
        const dataFiles = files.filter(file => file.endsWith('.data'));
        const keys = dataFiles.map(file => file.slice(0, -5)); // Remove ".data"
        
        resolve(keys);
      });
    });
  }

  /**
   * Clears all stored data
   * @returns {Promise<void>}
   */
  async clear() {
    try {
      const files = await this.readDir(this.options.storagePath);
      
      // Delete all files in the storage directory
      const deletePromises = files.map(file => {
        const filePath = path.join(this.options.storagePath, file);
        return this.deleteFile(filePath).catch(err => {
          // Log error but continue with other files
          Prime.Logger.warn(`Failed to delete file during clear: ${err.message}`, {
            path: filePath
          });
        });
      });
      
      await Promise.all(deletePromises);
    } catch (error) {
      throw new PrimeStorageError(
        `Failed to clear storage: ${error.message}`,
        { path: this.options.storagePath, originalError: error },
        'STORAGE_CLEAR_FAILED',
        error
      );
    }
  }

  /**
   * Reads a directory
   * @private
   * @param {string} dirPath - Path to read
   * @returns {Promise<string[]>} Files in the directory
   */
  async readDir(dirPath) {
    return new Promise((resolve, reject) => {
      fs.readdir(dirPath, (err, files) => {
        if (err) {
          reject(new PrimeStorageError(
            `Failed to read directory: ${err.message}`,
            { path: dirPath },
            'STORAGE_READ_DIR_FAILED',
            err
          ));
        } else {
          resolve(files);
        }
      });
    });
  }

  /**
   * Gets information about the storage
   * @returns {Promise<StorageInfo>} Storage information
   */
  async getStorageInfo() {
    try {
      const stats = await this.getDiskSpace();
      const usedSpace = await this.getStorageSize();
      
      return {
        available: stats.available,
        used: usedSpace,
        total: stats.total,
        provider: 'filesystem'
      };
    } catch (error) {
      Prime.Logger.warn('Failed to get storage info', { error: error.message });
      
      // Return default values on error
      return {
        available: 1024 * 1024 * 1024, // 1GB
        used: 0,
        total: 1024 * 1024 * 1024,
        provider: 'filesystem'
      };
    }
  }

  /**
   * Gets disk space information
   * @private
   * @returns {Promise<Object>} Disk space information
   */
  async getDiskSpace() {
    return new Promise((resolve, reject) => {
      // Use fs.statfs if available, otherwise fallback to a simple estimation
      if (typeof fs.statfs === 'function') {
        fs.statfs(this.options.storagePath, (err, stats) => {
          if (err) {
            reject(err);
            return;
          }
          
          resolve({
            available: stats.bavail * stats.bsize,
            total: stats.blocks * stats.bsize
          });
        });
      } else {
        // Simple fallback
        resolve({
          available: 1024 * 1024 * 1024, // 1GB
          total: 1024 * 1024 * 1024
        });
      }
    });
  }

  /**
   * Gets the total size of stored data
   * @private
   * @returns {Promise<number>} Size in bytes
   */
  async getStorageSize() {
    try {
      const files = await this.readDir(this.options.storagePath);
      
      const sizePromises = files.map(async (file) => {
        const filePath = path.join(this.options.storagePath, file);
        try {
          const stats = await this.getFileStats(filePath);
          return stats.size;
        } catch (error) {
          return 0;
        }
      });
      
      const sizes = await Promise.all(sizePromises);
      return sizes.reduce((total, size) => total + size, 0);
    } catch (error) {
      return 0;
    }
  }

  /**
   * Gets file stats
   * @private
   * @param {string} filePath - Path to get stats for
   * @returns {Promise<fs.Stats>} File stats
   */
  async getFileStats(filePath) {
    return new Promise((resolve, reject) => {
      fs.stat(filePath, (err, stats) => {
        if (err) {
          reject(err);
        } else {
          resolve(stats);
        }
      });
    });
  }

  /**
   * Creates a read stream for the data with the given ID
   * @param {string} id - ID of the data to stream
   * @param {StreamOptions} [options] - Stream options
   * @returns {ReadableStream} A readable stream of the data
   */
  createReadStream(id, options = {}) {
    const filePath = this.getFilePath(id);
    
    // Check if file exists
    if (!fs.existsSync(filePath)) {
      throw new PrimeStorageError(
        `Data not found for ID: ${id}`,
        { id, path: filePath },
        'STORAGE_NOT_FOUND'
      );
    }
    
    // Create a readable stream
    return fs.createReadStream(filePath, {
      highWaterMark: options.highWaterMark || 16384,
      encoding: options.encoding
    });
  }

  /**
   * Creates a write stream for storing data
   * @param {string} [id] - Optional ID (if not provided, a UUID will be generated)
   * @param {StreamOptions} [options] - Stream options
   * @returns {WritableStream} A writable stream to store data
   */
  createWriteStream(id, options = {}) {
    const dataId = id || Prime.Utils.uuid();
    const filePath = this.getFilePath(dataId);
    const metadataPath = this.getMetadataPath(dataId);
    
    // Create metadata
    const metadata = {
      id: dataId,
      contentType: options.contentType || 'application/octet-stream',
      timestamp: Date.now()
    };
    
    // Write metadata
    fs.writeFileSync(metadataPath, JSON.stringify(metadata));
    
    // Create a writable stream
    const stream = fs.createWriteStream(filePath, {
      highWaterMark: options.highWaterMark || 16384,
      encoding: options.encoding
    });
    
    // Add the ID to the stream for reference
    stream.id = dataId;
    
    return stream;
  }

  /**
   * Gets the provider type
   * @returns {string} The provider type
   */
  getProviderType() {
    return 'filesystem';
  }
}

module.exports = FilesystemProvider;