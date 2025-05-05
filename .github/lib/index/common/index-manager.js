/**
 * Index management utilities
 */

const { readJsonFile, writeJsonFile } = require('./schema-utils');
const { fileExists, constructFilename } = require('./file-utils');

// The name of the index file
const INDEX_FILE = 'index.json';

/**
 * Gets the current index or creates a new one if it doesn't exist
 * 
 * @returns {Array} - The current index
 */
function getIndex() {
  try {
    if (fileExists(INDEX_FILE)) {
      return readJsonFile(INDEX_FILE);
    } else {
      // Create a new empty index
      const emptyIndex = [];
      writeJsonFile(INDEX_FILE, emptyIndex);
      return emptyIndex;
    }
  } catch (error) {
    throw new Error(`Failed to get index: ${error.message}`);
  }
}

/**
 * Adds an entry to the index
 * 
 * @param {string} apiName - The name of the API
 * @param {string} endpointName - The name of the endpoint
 * @param {string} mediaType - The media type identifier
 * @returns {Object} - The added entry
 */
function addToIndex(apiName, endpointName, mediaType) {
  try {
    const index = getIndex();
    
    // Check if the entry already exists
    const existingEntryIndex = index.findIndex(entry => 
      entry.anchor === apiName && 
      entry.endpoint === endpointName && 
      entry.media === mediaType
    );
    
    const entry = {
      anchor: apiName,
      endpoint: endpointName,
      media: mediaType
    };
    
    if (existingEntryIndex >= 0) {
      // Update existing entry
      index[existingEntryIndex] = entry;
    } else {
      // Add new entry
      index.push(entry);
    }
    
    // Save the updated index
    writeJsonFile(INDEX_FILE, index);
    
    // Validate that the entry was added to the index
    const updatedIndex = getIndex();
    const entryExists = updatedIndex.some(e => 
      e.anchor === apiName && 
      e.endpoint === endpointName && 
      e.media === mediaType
    );
    
    if (!entryExists) {
      throw new Error(`Failed to add entry to index: Entry validation failed`);
    }
    
    return entry;
  } catch (error) {
    throw new Error(`Failed to add to index: ${error.message}`);
  }
}

/**
 * Removes an entry from the index
 * 
 * @param {string} apiName - The name of the API
 * @param {string} endpointName - The name of the endpoint
 * @param {string} mediaType - The media type identifier
 * @returns {boolean} - True if the entry was removed, false if it wasn't found
 */
function removeFromIndex(apiName, endpointName, mediaType) {
  try {
    const index = getIndex();
    
    // Find the entry to remove
    const entryIndex = index.findIndex(entry => 
      entry.anchor === apiName && 
      entry.endpoint === endpointName && 
      entry.media === mediaType
    );
    
    if (entryIndex >= 0) {
      // Remove the entry
      index.splice(entryIndex, 1);
      
      // Save the updated index
      writeJsonFile(INDEX_FILE, index);
      
      return true;
    }
    
    return false;
  } catch (error) {
    throw new Error(`Failed to remove from index: ${error.message}`);
  }
}

/**
 * Finds an entry in the index
 * 
 * @param {string} apiName - The name of the API
 * @param {string} endpointName - The name of the endpoint
 * @param {string} mediaType - The media type identifier
 * @returns {Object|null} - The found entry or null if not found
 */
function findInIndex(apiName, endpointName, mediaType) {
  try {
    const index = getIndex();
    
    // Find the entry
    const entry = index.find(entry => 
      entry.anchor === apiName && 
      entry.endpoint === endpointName && 
      entry.media === mediaType
    );
    
    return entry || null;
  } catch (error) {
    throw new Error(`Failed to find in index: ${error.message}`);
  }
}

/**
 * Gets the filename for an indexed entry
 * 
 * @param {Object} entry - The index entry
 * @returns {string} - The filename
 */
function getFilenameForEntry(entry) {
  return constructFilename(entry.anchor, entry.endpoint, entry.media);
}

module.exports = {
  getIndex,
  addToIndex,
  removeFromIndex,
  findInIndex,
  getFilenameForEntry
};
