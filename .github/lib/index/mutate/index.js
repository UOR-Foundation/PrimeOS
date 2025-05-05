/**
 * Index API - Mutate Endpoint
 * 
 * Indexes arbitrary JSON (including its JSON schema)
 */

const { validateSchema, validateJson } = require('../validate/index');
const { writeJsonFile, readJsonFile } = require('../common/schema-utils');
const { writeFile, constructFilename, fileExists } = require('../common/file-utils');
const { addToIndex, findInIndex, getFilenameForEntry } = require('../common/index-manager');

/**
 * Indexes a JSON schema
 * 
 * @param {Object} schema - The JSON schema to index
 * @param {string} apiName - The name of the API
 * @param {string} endpointName - The name of the endpoint
 * @param {string} mediaType - The media type identifier
 * @returns {Object} - Result of the indexing operation
 */
function indexSchema(schema, apiName, endpointName, mediaType) {
  try {
    // Validate the schema first
    const validationResult = validateSchema(schema);
    
    if (!validationResult.isValid) {
      return {
        success: false,
        error: 'Invalid JSON schema',
        details: validationResult.errors
      };
    }
    
    // Construct the filename
    const filename = constructFilename(apiName, endpointName, mediaType);
    
    // Write the schema to the file
    writeJsonFile(filename, schema);
    
    // Add to the index
    const indexEntry = addToIndex(apiName, endpointName, mediaType);
    
    return {
      success: true,
      message: `Schema indexed successfully as ${filename}`,
      entry: indexEntry
    };
  } catch (error) {
    return {
      success: false,
      error: error.message
    };
  }
}

/**
 * Indexes arbitrary JSON content
 * 
 * @param {Object} content - The JSON content to index
 * @param {string} apiName - The name of the API
 * @param {string} endpointName - The name of the endpoint
 * @param {string} mediaType - The media type identifier
 * @returns {Object} - Result of the indexing operation
 */
function indexContent(content, apiName, endpointName, mediaType) {
  try {
    // Look for a schema for this content type
    // Convention: Schema is stored with endpointName = "schema"
    const schemaApiName = apiName;
    const schemaEndpointName = "schema";
    const schemaMediaType = mediaType;
    
    // Check if schema exists in the index
    const schemaEntry = findInIndex(schemaApiName, schemaEndpointName, schemaMediaType);
    
    // Schema MUST exist
    if (!schemaEntry) {
      return {
        success: false,
        error: `Schema not found for ${apiName}.${schemaEndpointName}.${mediaType}. Content cannot be indexed without a schema.`
      };
    }
    
    const schemaFilename = getFilenameForEntry(schemaEntry);
    
    // Schema file MUST exist
    if (!fileExists(schemaFilename)) {
      return {
        success: false,
        error: `Schema file ${schemaFilename} not found. Content cannot be indexed without a schema.`
      };
    }
    
    // Read and parse the schema
    const schema = readJsonFile(schemaFilename);
    
    // Validate content against schema - MUST pass validation
    const validationResult = validateJson(content, schema);
    
    if (!validationResult.isValid) {
      return {
        success: false,
        error: 'Content does not validate against schema',
        details: validationResult.errors
      };
    }
    
    // Only proceed with indexing if validation passes
    const filename = constructFilename(apiName, endpointName, mediaType);
    writeJsonFile(filename, content);
    const indexEntry = addToIndex(apiName, endpointName, mediaType);
    
    return {
      success: true,
      message: `Content indexed successfully as ${filename}`,
      entry: indexEntry
    };
  } catch (error) {
    return {
      success: false,
      error: error.message
    };
  }
}

/**
 * Indexes raw content (string)
 * 
 * @param {string} content - The raw content to index
 * @param {string} apiName - The name of the API
 * @param {string} endpointName - The name of the endpoint
 * @param {string} mediaType - The media type identifier
 * @returns {Object} - Result of the indexing operation
 */
function indexRawContent(content, apiName, endpointName, mediaType) {
  // Raw content cannot be validated against a JSON schema
  return {
    success: false,
    error: 'Raw content cannot be indexed as it cannot be validated against a JSON schema. All mutations must pass validation.'
  };
}

/**
 * Main mutate function that determines the type of indexing to perform
 * 
 * @param {Object} params - Indexing parameters
 * @returns {Object} - Result of the indexing operation
 */
function mutate(params) {
  const { content, apiName, endpointName, mediaType, isSchema, isRaw } = params;
  
  if (!apiName || !endpointName || !mediaType) {
    return {
      success: false,
      error: 'Missing required parameters: apiName, endpointName, and mediaType are required'
    };
  }
  
  if (content === undefined) {
    return {
      success: false,
      error: 'Missing required parameter: content is required'
    };
  }
  
  // If it's a schema, index it as a schema
  if (isSchema) {
    return indexSchema(content, apiName, endpointName, mediaType);
  }
  
  // If it's raw content, index it as raw
  if (isRaw) {
    return indexRawContent(content, apiName, endpointName, mediaType);
  }
  
  // Otherwise, index it as JSON content
  return indexContent(content, apiName, endpointName, mediaType);
}

module.exports = {
  mutate,
  indexSchema,
  indexContent,
  indexRawContent
};
