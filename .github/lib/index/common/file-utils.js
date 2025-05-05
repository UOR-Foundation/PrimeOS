/**
 * Common utilities for file operations
 */

const fs = require('fs');
const path = require('path');

/**
 * Gets the repository root directory
 * 
 * @returns {string} - The absolute path to the repository root
 */
function getRepoRoot() {
  return process.env.REPO_ROOT || process.cwd();
}

/**
 * Constructs a filename based on the API name, endpoint name, and media type
 * 
 * @param {string} apiName - The name of the API
 * @param {string} endpointName - The name of the endpoint
 * @param {string} mediaType - The media type identifier
 * @returns {string} - The constructed filename
 */
function constructFilename(apiName, endpointName, mediaType) {
  return `${apiName}.${endpointName}.${mediaType}`;
}

/**
 * Parses a filename into its components (API name, endpoint name, media type)
 * 
 * @param {string} filename - The filename to parse
 * @returns {Object} - The parsed components or null if the format is invalid
 */
function parseFilename(filename) {
  const parts = filename.split('.');
  if (parts.length < 3) {
    return null;
  }
  
  // The media type might contain dots (e.g., application.json)
  const apiName = parts[0];
  const endpointName = parts[1];
  const mediaType = parts.slice(2).join('.');
  
  return {
    apiName,
    endpointName,
    mediaType
  };
}

/**
 * Lists all files in the repository root that match the API naming convention
 * 
 * @returns {Array<string>} - Array of filenames
 */
function listApiFiles() {
  try {
    const repoRoot = getRepoRoot();
    const files = fs.readdirSync(repoRoot);
    
    // Filter files that match the API naming convention
    return files.filter(file => {
      const stats = fs.statSync(path.join(repoRoot, file));
      return stats.isFile() && parseFilename(file) !== null;
    });
  } catch (error) {
    throw new Error(`Failed to list API files: ${error.message}`);
  }
}

/**
 * Reads a file from the repository root
 * 
 * @param {string} filename - The filename at the repository root
 * @returns {string} - The file content
 */
function readFile(filename) {
  try {
    const repoRoot = getRepoRoot();
    const filePath = path.join(repoRoot, filename);
    return fs.readFileSync(filePath, 'utf8');
  } catch (error) {
    throw new Error(`Failed to read file ${filename}: ${error.message}`);
  }
}

/**
 * Writes content to a file at the repository root
 * 
 * @param {string} filename - The filename at the repository root
 * @param {string} content - The content to write
 */
function writeFile(filename, content) {
  try {
    const repoRoot = getRepoRoot();
    const filePath = path.join(repoRoot, filename);
    fs.writeFileSync(filePath, content, 'utf8');
  } catch (error) {
    throw new Error(`Failed to write file ${filename}: ${error.message}`);
  }
}

/**
 * Checks if a file exists at the repository root
 * 
 * @param {string} filename - The filename at the repository root
 * @returns {boolean} - True if the file exists, false otherwise
 */
function fileExists(filename) {
  try {
    const repoRoot = getRepoRoot();
    const filePath = path.join(repoRoot, filename);
    return fs.existsSync(filePath);
  } catch (error) {
    return false;
  }
}

module.exports = {
  getRepoRoot,
  constructFilename,
  parseFilename,
  listApiFiles,
  readFile,
  writeFile,
  fileExists
};
