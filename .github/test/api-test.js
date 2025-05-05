/**
 * Tests for the Repository API
 * 
 * Tests the validate, mutate, and resolve endpoints directly
 */

const validateLib = require('../lib/index/validate/index.js');
const mutateLib = require('../lib/index/mutate/index.js');
const resolveLib = require('../lib/index/resolve/index.js');
const { readJsonFile, writeJsonFile } = require('../lib/index/common/schema-utils.js');
const { fileExists } = require('../lib/index/common/file-utils.js');
const { getIndex } = require('../lib/index/common/index-manager.js');

// Test data - fully compliant with JSON Schema Draft 2020-12
const testSchema = {
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://example.com/person.schema.json",
  "title": "Person",
  "description": "A person schema",
  "type": "object",
  "properties": {
    "name": { 
      "type": "string",
      "description": "The person's name"
    },
    "age": { 
      "type": "integer", 
      "description": "The person's age in years",
      "minimum": 0 
    }
  },
  "required": ["name", "age"],
  "additionalProperties": false
};

const validData = {
  "name": "John Doe",
  "age": 30
};

const invalidData = {
  "name": "John Doe",
  "age": -5
};

/**
 * Run all tests
 */
async function runTests() {
  console.log('Running Repository API Tests...');
  
  // Print the current working directory
  console.log('Current working directory:', process.cwd());
  
  // Test validate endpoint
  testValidateEndpoint();
  
  // Test mutate endpoint
  testMutateEndpoint();
  
  // Test resolve endpoint
  testResolveEndpoint();
  
  console.log('All tests completed!');
}

/**
 * Test the validate endpoint
 */
function testValidateEndpoint() {
  console.log('\n--- Testing Validate Endpoint ---');
  
  // Test validating data against a schema directly
  const validResult = validateLib.validateJson(validData, testSchema);
  console.log('Validate valid data against schema directly:', validResult.isValid ? 'PASS' : 'FAIL');
  
  const invalidResult = validateLib.validateJson(invalidData, testSchema);
  console.log('Validate invalid data against schema directly:', !invalidResult.isValid ? 'PASS' : 'FAIL');
  
  // Test validating a schema against JSON Schema specification
  const schemaValidationResult = validateLib.validateSchema(testSchema);
  console.log('Validate schema against JSON Schema specification:', schemaValidationResult.isValid ? 'PASS' : 'FAIL');
  
  // Test the main validate function
  const mainValidResult = validateLib.validate({
    data: validData,
    schema: testSchema
  });
  console.log('Main validate function with valid data:', mainValidResult.isValid ? 'PASS' : 'FAIL');
  
  const mainInvalidResult = validateLib.validate({
    data: invalidData,
    schema: testSchema
  });
  console.log('Main validate function with invalid data:', !mainInvalidResult.isValid ? 'PASS' : 'FAIL');
}

/**
 * Test the mutate endpoint
 */
function testMutateEndpoint() {
  console.log('\n--- Testing Mutate Endpoint ---');
  
  // Test indexing a schema
  const indexSchemaResult = mutateLib.mutate({
    content: testSchema,
    apiName: 'test',
    endpointName: 'schema',
    mediaType: 'entities',
    isSchema: true
  });
  console.log('Index schema:', indexSchemaResult.success ? 'PASS' : 'FAIL');
  
  // Test indexing JSON content
  const indexContentResult = mutateLib.mutate({
    content: validData,
    apiName: 'test',
    endpointName: 'data',
    mediaType: 'entities'
  });
  console.log('Index JSON content:', indexContentResult.success ? 'PASS' : 'FAIL');
  
  // Verify the files were created
  console.log('Verify schema file exists:', fileExists('test.schema.entities') ? 'PASS' : 'FAIL');
  console.log('Verify data file exists:', fileExists('test.data.entities') ? 'PASS' : 'FAIL');
  
  // Verify the index was updated
  const index = getIndex();
  const hasSchemaEntry = index.some(entry => 
    entry.anchor === 'test' && 
    entry.endpoint === 'schema' && 
    entry.media === 'entities'
  );
  const hasDataEntry = index.some(entry => 
    entry.anchor === 'test' && 
    entry.endpoint === 'data' && 
    entry.media === 'entities'
  );
  
  console.log('Verify index has schema entry:', hasSchemaEntry ? 'PASS' : 'FAIL');
  console.log('Verify index has data entry:', hasDataEntry ? 'PASS' : 'FAIL');
  
  // Test strict validation requirements
  
  // 1. Test indexing content without a schema
  const noSchemaApiName = 'no-schema-test';
  const indexWithoutSchemaResult = mutateLib.mutate({
    content: validData,
    apiName: noSchemaApiName,
    endpointName: 'data',
    mediaType: 'entities'
  });
  console.log('Reject indexing without schema:', !indexWithoutSchemaResult.success ? 'PASS' : 'FAIL');
  
  // 2. Test indexing invalid content
  const indexInvalidResult = mutateLib.mutate({
    content: invalidData,
    apiName: 'test',
    endpointName: 'invalid-data',
    mediaType: 'entities'
  });
  console.log('Reject invalid content:', !indexInvalidResult.success ? 'PASS' : 'FAIL');
  
  // 3. Test indexing raw content
  const indexRawResult = mutateLib.mutate({
    content: "This is raw content",
    apiName: 'test',
    endpointName: 'raw',
    mediaType: 'text',
    isRaw: true
  });
  console.log('Reject raw content:', !indexRawResult.success ? 'PASS' : 'FAIL');
}

/**
 * Test the resolve endpoint
 */
function testResolveEndpoint() {
  console.log('\n--- Testing Resolve Endpoint ---');
  
  // Test resolving the schema
  const resolveSchemaResult = resolveLib.resolve({
    apiName: 'test',
    endpointName: 'schema',
    mediaType: 'entities'
  });
  console.log('Resolve schema:', resolveSchemaResult.success ? 'PASS' : 'FAIL');
  
  if (resolveSchemaResult.success) {
    // Verify the resolved schema matches the original
    const schemaMatches = JSON.stringify(resolveSchemaResult.content) === JSON.stringify(testSchema);
    console.log('Verify resolved schema matches original:', schemaMatches ? 'PASS' : 'FAIL');
  }
  
  // Test resolving the data
  const resolveDataResult = resolveLib.resolve({
    apiName: 'test',
    endpointName: 'data',
    mediaType: 'entities'
  });
  console.log('Resolve data:', resolveDataResult.success ? 'PASS' : 'FAIL');
  
  if (resolveDataResult.success) {
    // Verify the resolved data matches the original
    const dataMatches = JSON.stringify(resolveDataResult.content) === JSON.stringify(validData);
    console.log('Verify resolved data matches original:', dataMatches ? 'PASS' : 'FAIL');
  }
  
  // Test resolving non-existent content
  const resolveNonExistentResult = resolveLib.resolve({
    apiName: 'nonexistent',
    endpointName: 'endpoint',
    mediaType: 'entities'
  });
  console.log('Resolve non-existent content:', !resolveNonExistentResult.success ? 'PASS' : 'FAIL');
}

// Run the tests
runTests().catch(console.error);
