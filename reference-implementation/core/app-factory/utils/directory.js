/**
 * PrimeOS App Factory - Directory Utility
 * 
 * Provides utility functions for working with directories and file paths.
 */

const DIR_SEPARATOR = '/';
const PATH_SEPARATOR_REGEX = /\/|\\/g;
const ALLOWED_PATH_CHARS = /^[a-zA-Z0-9_\-\.\/\\]+$/;

/**
 * Validates a file path to ensure it contains only allowed characters
 * @param {string} path - Path to validate
 * @returns {boolean} Whether the path is valid
 */
function isValidPath(path) {
  if (!path || typeof path !== 'string') {
    return false;
  }
  
  return ALLOWED_PATH_CHARS.test(path);
}

/**
 * Normalizes a file path to use consistent separators
 * @param {string} path - Path to normalize
 * @returns {string} Normalized path
 */
function normalizePath(path) {
  if (!path || typeof path !== 'string') {
    return '';
  }
  
  // Convert to forward slashes
  return path.replace(PATH_SEPARATOR_REGEX, DIR_SEPARATOR);
}

/**
 * Joins path segments together with proper separators
 * @param {...string} paths - Path segments to join
 * @returns {string} Joined path
 */
function joinPaths(...paths) {
  if (!paths || paths.length === 0) {
    return '';
  }
  
  // Filter out empty segments
  const segments = paths.filter(p => p && typeof p === 'string');
  
  if (segments.length === 0) {
    return '';
  }
  
  // Normalize each segment first
  const normalizedSegments = segments.map(segment => {
    // Remove leading/trailing slashes
    return segment.replace(/^\/+|\/+$/g, '');
  });
  
  // Join normalized segments
  return normalizedSegments.join(DIR_SEPARATOR);
}

/**
 * Gets the directory part of a path
 * @param {string} path - Path to parse
 * @returns {string} Directory path
 */
function getDirectoryPath(path) {
  if (!path || typeof path !== 'string') {
    return '';
  }
  
  const normalizedPath = normalizePath(path);
  const lastSeparatorIndex = normalizedPath.lastIndexOf(DIR_SEPARATOR);
  
  if (lastSeparatorIndex < 0) {
    return '';
  }
  
  return normalizedPath.substring(0, lastSeparatorIndex);
}

/**
 * Gets the filename part of a path
 * @param {string} path - Path to parse
 * @returns {string} Filename
 */
function getFileName(path) {
  if (!path || typeof path !== 'string') {
    return '';
  }
  
  const normalizedPath = normalizePath(path);
  const lastSeparatorIndex = normalizedPath.lastIndexOf(DIR_SEPARATOR);
  
  if (lastSeparatorIndex < 0) {
    return normalizedPath;
  }
  
  return normalizedPath.substring(lastSeparatorIndex + 1);
}

/**
 * Gets the extension part of a filename
 * @param {string} path - Path to parse
 * @returns {string} File extension
 */
function getFileExtension(path) {
  const fileName = getFileName(path);
  const lastDotIndex = fileName.lastIndexOf('.');
  
  if (lastDotIndex < 0) {
    return '';
  }
  
  return fileName.substring(lastDotIndex + 1);
}

/**
 * Gets a safe filename from a string
 * @param {string} name - String to convert to a filename
 * @returns {string} Safe filename
 */
function getSafeFileName(name) {
  if (!name || typeof name !== 'string') {
    return '';
  }
  
  // Replace spaces with hyphens and remove invalid characters
  return name
    .toLowerCase()
    .replace(/\s+/g, '-')
    .replace(/[^a-z0-9\-_\.]/g, '');
}

// Export directory utilities
module.exports = {
  isValidPath,
  normalizePath,
  joinPaths,
  getDirectoryPath,
  getFileName,
  getFileExtension,
  getSafeFileName
};