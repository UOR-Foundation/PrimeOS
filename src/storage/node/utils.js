/**
 * PrimeOS JavaScript Library - Node.js Storage Utilities
 * Utility functions for Node.js storage providers
 */

const Prime = require("../../core");
const { PrimeStorageError } = require("../core/provider");
const fs = require("fs");
const path = require("path");
const os = require("os");
const crypto = require("crypto");

/**
 * Utility functions for Node.js storage
 */
const NodeStorageUtils = {
  /**
   * Gets the default storage directory
   * @returns {string} Default storage path
   */
  getDefaultStoragePath() {
    return path.join(os.tmpdir(), "primeos-storage");
  },

  /**
   * Gets the user's home directory
   * @returns {string} Home directory path
   */
  getUserHomeDir() {
    return os.homedir();
  },

  /**
   * Gets the application data directory
   * @param {string} [appName='primeos'] - Application name
   * @returns {string} Application data directory path
   */
  getAppDataDir(appName = "primeos") {
    if (process.platform === "win32") {
      return path.join(process.env.APPDATA || "", appName);
    } else if (process.platform === "darwin") {
      return path.join(os.homedir(), "Library", "Application Support", appName);
    } else {
      return path.join(os.homedir(), ".config", appName);
    }
  },

  /**
   * Calculates the hash of a file
   * @param {string} filePath - Path to the file
   * @param {string} [algorithm='sha256'] - Hash algorithm
   * @returns {Promise<string>} File hash
   */
  async calculateFileHash(filePath, algorithm = "sha256") {
    return new Promise((resolve, reject) => {
      const hash = crypto.createHash(algorithm);
      const stream = fs.createReadStream(filePath);

      stream.on("error", (err) => {
        reject(
          new PrimeStorageError(
            `Failed to calculate file hash: ${err.message}`,
            { path: filePath },
            "STORAGE_HASH_FAILED",
            err,
          ),
        );
      });

      stream.on("data", (chunk) => {
        hash.update(chunk);
      });

      stream.on("end", () => {
        resolve(hash.digest("hex"));
      });
    });
  },

  /**
   * Gets the size of a directory
   * @param {string} dirPath - Path to the directory
   * @returns {Promise<number>} Size in bytes
   */
  async getDirectorySize(dirPath) {
    let totalSize = 0;

    try {
      const files = await this.readDirRecursive(dirPath);

      const sizePromises = files.map(async (file) => {
        try {
          const stats = await this.getFileStats(file);
          return stats.isFile() ? stats.size : 0;
        } catch (error) {
          return 0;
        }
      });

      const sizes = await Promise.all(sizePromises);
      totalSize = sizes.reduce((total, size) => total + size, 0);
    } catch (error) {
      Prime.Logger.warn(
        `Failed to calculate directory size: ${error.message}`,
        {
          path: dirPath,
        },
      );
    }

    return totalSize;
  },

  /**
   * Reads a directory recursively
   * @private
   * @param {string} dir - Directory path
   * @returns {Promise<string[]>} Array of file paths
   */
  async readDirRecursive(dir) {
    let results = [];

    try {
      const list = await this.readDir(dir);

      for (const file of list) {
        const filePath = path.join(dir, file);
        const stats = await this.getFileStats(filePath);

        if (stats.isDirectory()) {
          const subFiles = await this.readDirRecursive(filePath);
          results = results.concat(subFiles);
        } else {
          results.push(filePath);
        }
      }
    } catch (error) {
      Prime.Logger.warn(
        `Failed to read directory recursively: ${error.message}`,
        {
          path: dir,
        },
      );
    }

    return results;
  },

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
          reject(err);
        } else {
          resolve(files);
        }
      });
    });
  },

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
  },

  /**
   * Gets disk space information
   * @param {string} [dirPath=os.tmpdir()] - Directory to check
   * @returns {Promise<Object>} Disk space information
   */
  async getDiskSpace(dirPath = os.tmpdir()) {
    return new Promise((resolve, reject) => {
      // Use fs.statfs if available, otherwise fallback
      if (typeof fs.statfs === "function") {
        fs.statfs(dirPath, (err, stats) => {
          if (err) {
            reject(err);
            return;
          }

          resolve({
            available: stats.bavail * stats.bsize,
            total: stats.blocks * stats.bsize,
            used: (stats.blocks - stats.bfree) * stats.bsize,
          });
        });
      } else {
        // Simple fallback with default values
        resolve({
          available: 1024 * 1024 * 1024 * 10, // 10GB
          total: 1024 * 1024 * 1024 * 100, // 100GB
          used: 1024 * 1024 * 1024 * 90, // 90GB
        });
      }
    });
  },

  /**
   * Safely writes a file with atomic operations
   * @param {string} filePath - Path to write to
   * @param {*} data - Data to write
   * @returns {Promise<void>}
   */
  async atomicWriteFile(filePath, data) {
    const tempPath = `${filePath}.tmp`;

    try {
      // Write to temporary file
      await this.writeFile(tempPath, data);

      // Rename temporary file to target file
      await this.renameFile(tempPath, filePath);
    } catch (error) {
      // Clean up temporary file if it exists
      try {
        if (await this.fileExists(tempPath)) {
          await this.deleteFile(tempPath);
        }
      } catch (cleanupError) {
        // Ignore cleanup errors
      }

      throw new PrimeStorageError(
        `Failed to write file atomically: ${error.message}`,
        { path: filePath },
        "STORAGE_ATOMIC_WRITE_FAILED",
        error,
      );
    }
  },

  /**
   * Writes a file
   * @private
   * @param {string} filePath - Path to write to
   * @param {*} data - Data to write
   * @returns {Promise<void>}
   */
  async writeFile(filePath, data) {
    return new Promise((resolve, reject) => {
      fs.writeFile(filePath, data, (err) => {
        if (err) {
          reject(err);
        } else {
          resolve();
        }
      });
    });
  },

  /**
   * Renames a file
   * @private
   * @param {string} oldPath - Old path
   * @param {string} newPath - New path
   * @returns {Promise<void>}
   */
  async renameFile(oldPath, newPath) {
    return new Promise((resolve, reject) => {
      fs.rename(oldPath, newPath, (err) => {
        if (err) {
          reject(err);
        } else {
          resolve();
        }
      });
    });
  },

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
  },

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
          reject(err);
        } else {
          resolve();
        }
      });
    });
  },

  /**
   * Creates a temporary file
   * @param {string} [prefix='primeos-'] - Filename prefix
   * @param {*} [data] - Optional data to write
   * @returns {Promise<string>} Path to the temporary file
   */
  async createTempFile(prefix = "primeos-", data) {
    const tempDir = os.tmpdir();
    const randomName = crypto.randomBytes(16).toString("hex");
    const filePath = path.join(tempDir, `${prefix}${randomName}`);

    if (data !== undefined) {
      await this.writeFile(filePath, data);
    } else {
      // Create an empty file
      await this.writeFile(filePath, "");
    }

    return filePath;
  },

  /**
   * Creates a temporary directory
   * @param {string} [prefix='primeos-'] - Directory name prefix
   * @returns {Promise<string>} Path to the temporary directory
   */
  async createTempDir(prefix = "primeos-") {
    const tempDir = os.tmpdir();
    const randomName = crypto.randomBytes(16).toString("hex");
    const dirPath = path.join(tempDir, `${prefix}${randomName}`);

    return new Promise((resolve, reject) => {
      fs.mkdir(dirPath, { recursive: true }, (err) => {
        if (err) {
          reject(err);
        } else {
          resolve(dirPath);
        }
      });
    });
  },
};

module.exports = NodeStorageUtils;
