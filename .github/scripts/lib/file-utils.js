/**
 * File utilities for UOR model repository maintenance
 */

const fs = require('fs');
const path = require('path');

/**
 * Walk through directories recursively
 * @param {string} dir - The directory to start walking from
 * @param {object} options - Options for walking
 * @param {RegExp|string} options.exclude - Pattern to exclude directories
 * @param {RegExp|string} options.include - Pattern to include directories
 * @returns {string[]} Array of directory paths
 */
function walkDirectories(dir, options = {}) {
  const exclude = options.exclude ? new RegExp(options.exclude) : null;
  const include = options.include ? new RegExp(options.include) : null;
  const results = [];

  // Helper function for recursive directory walking
  function walk(currentDir) {
    // Exclude directories that match the exclude pattern
    if (exclude && exclude.test(currentDir)) {
      return;
    }

    // Include only directories that match the include pattern, if specified
    if (include && !include.test(currentDir)) {
      return;
    }

    results.push(currentDir);

    try {
      const items = fs.readdirSync(currentDir, { withFileTypes: true });
      
      for (const item of items) {
        if (item.isDirectory()) {
          const itemPath = path.join(currentDir, item.name);
          walk(itemPath);
        }
      }
    } catch (error) {
      console.error(`Error reading directory ${currentDir}: ${error.message}`);
    }
  }

  walk(dir);
  return results;
}

/**
 * Check if required files exist in a directory
 * @param {string} dirPath - The directory to check
 * @param {string[]} requiredFiles - Array of required file names
 * @returns {string[]} Array of missing files
 */
function checkMissingFiles(dirPath, requiredFiles) {
  const missingFiles = [];

  for (const file of requiredFiles) {
    const filePath = path.join(dirPath, file);
    if (!fs.existsSync(filePath)) {
      missingFiles.push(file);
    }
  }

  return missingFiles;
}

/**
 * Safely creates a file if it doesn't exist
 * @param {string} filePath - Path to create the file at
 * @param {string|Function} content - Content or function that returns content
 * @returns {boolean} True if file was created, false if it already existed
 */
function safeCreateFile(filePath, content) {
  // Don't overwrite existing files
  if (fs.existsSync(filePath)) {
    return false;
  }

  try {
    // Create containing directory if it doesn't exist
    const dirPath = path.dirname(filePath);
    if (!fs.existsSync(dirPath)) {
      fs.mkdirSync(dirPath, { recursive: true });
    }

    // Write content to file
    const fileContent = typeof content === 'function' ? content() : content;
    fs.writeFileSync(filePath, fileContent);
    return true;
  } catch (error) {
    console.error(`Error creating file ${filePath}: ${error.message}`);
    return false;
  }
}

/**
 * Lists all directories in the given path
 * @param {string} dirPath - The directory to list
 * @returns {string[]} Array of directory names
 */
function listDirectories(dirPath) {
  try {
    return fs.readdirSync(dirPath, { withFileTypes: true })
      .filter(dirent => dirent.isDirectory())
      .map(dirent => dirent.name);
  } catch (error) {
    console.error(`Error listing directories in ${dirPath}: ${error.message}`);
    return [];
  }
}

module.exports = {
  walkDirectories,
  checkMissingFiles,
  safeCreateFile,
  listDirectories
};
