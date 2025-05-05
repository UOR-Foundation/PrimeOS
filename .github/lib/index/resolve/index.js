/**
 * Index API - Resolve Endpoint
 * 
 * Resolves JSON from the index
 */

const { readJsonFile } = require('../common/schema-utils');
const { readFile, fileExists } = require('../common/file-utils');
const { findInIndex, getFilenameForEntry } = require('../common/index-manager');

/**
 * Resolves JSON content from the index
 * 
 * @param {string} apiName - The name of the API
 * @param {string} endpointName - The name of the endpoint
 * @param {string} mediaType - The media type identifier
 * @returns {Object} - Result of the resolve operation
 */
function resolveJson(apiName, endpointName, mediaType) {
  try {
    // Find the entry in the index
    const entry = findInIndex(apiName, endpointName, mediaType);
    
    if (!entry) {
      return {
        success: false,
        error: `Entry not found for ${apiName}.${endpointName}.${mediaType}`
      };
    }
    
    // Get the filename for the entry
    const filename = getFilenameForEntry(entry);
    
    if (!fileExists(filename)) {
      return {
        success: false,
        error: `File ${filename} not found`
      };
    }
    
    // Read and parse the JSON content
    const content = readJsonFile(filename);
    
    return {
      success: true,
      content,
      entry
    };
  } catch (error) {
    return {
      success: false,
      error: error.message
    };
  }
}

/**
 * Resolves raw content from the index
 * 
 * @param {string} apiName - The name of the API
 * @param {string} endpointName - The name of the endpoint
 * @param {string} mediaType - The media type identifier
 * @returns {Object} - Result of the resolve operation
 */
function resolveRaw(apiName, endpointName, mediaType) {
  try {
    // Find the entry in the index
    const entry = findInIndex(apiName, endpointName, mediaType);
    
    if (!entry) {
      return {
        success: false,
        error: `Entry not found for ${apiName}.${endpointName}.${mediaType}`
      };
    }
    
    // Get the filename for the entry
    const filename = getFilenameForEntry(entry);
    
    if (!fileExists(filename)) {
      return {
        success: false,
        error: `File ${filename} not found`
      };
    }
    
    // Read the raw content
    const content = readFile(filename);
    
    return {
      success: true,
      content,
      entry
    };
  } catch (error) {
    return {
      success: false,
      error: error.message
    };
  }
}

/**
 * Main resolve function that determines the type of resolution to perform
 * 
 * @param {Object} params - Resolution parameters
 * @returns {Object} - Result of the resolve operation
 */
function resolve(params) {
  const { apiName, endpointName, mediaType, raw } = params;
  
  if (!apiName || !endpointName || !mediaType) {
    return {
      success: false,
      error: 'Missing required parameters: apiName, endpointName, and mediaType are required'
    };
  }
  
  // If raw is true, resolve as raw content
  if (raw) {
    return resolveRaw(apiName, endpointName, mediaType);
  }
  
  // Otherwise, resolve as JSON
  return resolveJson(apiName, endpointName, mediaType);
}

module.exports = {
  resolve,
  resolveJson,
  resolveRaw
};
