/**
 * Index API - Validate Endpoint
 * 
 * Validates JSON against a schema or validates a JSON schema against the JSON Schema specification
 */

const { validateAgainstSchema, validateJsonSchema, readJsonFile } = require('../common/schema-utils');
const { readFile, fileExists, constructFilename } = require('../common/file-utils');
const { findInIndex, getFilenameForEntry } = require('../common/index-manager');

/**
 * Validates JSON data against a JSON schema
 * 
 * @param {Object} data - The JSON data to validate
 * @param {Object} schema - The JSON schema to validate against
 * @returns {Object} - Validation result with isValid and errors properties
 */
function validateJson(data, schema) {
  return validateAgainstSchema(data, schema);
}

/**
 * Validates a JSON schema against the JSON Schema specification
 * 
 * @param {Object} schema - The JSON schema to validate
 * @returns {Object} - Validation result with isValid and errors properties
 */
function validateSchema(schema) {
  return validateJsonSchema(schema);
}

/**
 * Validates JSON data against a schema identified by API name, endpoint name, and media type
 * 
 * @param {Object} data - The JSON data to validate
 * @param {string} apiName - The name of the API
 * @param {string} endpointName - The name of the endpoint
 * @param {string} mediaType - The media type identifier
 * @returns {Object} - Validation result with isValid and errors properties
 */
function validateJsonAgainstIndexedSchema(data, apiName, endpointName, mediaType) {
  try {
    // Find the schema in the index
    const entry = findInIndex(apiName, endpointName, mediaType);
    
    if (!entry) {
      return {
        isValid: false,
        errors: [{ message: `Schema not found for ${apiName}.${endpointName}.${mediaType}` }]
      };
    }
    
    // Get the filename for the schema
    const schemaFilename = getFilenameForEntry(entry);
    
    if (!fileExists(schemaFilename)) {
      return {
        isValid: false,
        errors: [{ message: `Schema file ${schemaFilename} not found` }]
      };
    }
    
    // Read and parse the schema
    const schemaContent = readFile(schemaFilename);
    const schema = JSON.parse(schemaContent);
    
    // Validate the data against the schema
    return validateJson(data, schema);
  } catch (error) {
    return {
      isValid: false,
      errors: [{ message: error.message }]
    };
  }
}

/**
 * Main validate function that determines the type of validation to perform
 * 
 * @param {Object} params - Validation parameters
 * @returns {Object} - Validation result
 */
function validate(params) {
  const { data, schema, apiName, endpointName, mediaType, validateSchemaOnly } = params;
  
  // If validateSchemaOnly is true, validate the schema against the JSON Schema specification
  if (validateSchemaOnly && schema) {
    return validateSchema(schema);
  }
  
  // If schema is provided directly, validate data against it
  if (schema) {
    return validateJson(data, schema);
  }
  
  // If API name, endpoint name, and media type are provided, validate against indexed schema
  if (apiName && endpointName && mediaType) {
    return validateJsonAgainstIndexedSchema(data, apiName, endpointName, mediaType);
  }
  
  // If no valid validation method is determined
  return {
    isValid: false,
    errors: [{ message: 'Invalid validation parameters. Provide either schema or apiName, endpointName, and mediaType.' }]
  };
}

module.exports = {
  validate,
  validateJson,
  validateSchema,
  validateJsonAgainstIndexedSchema
};
