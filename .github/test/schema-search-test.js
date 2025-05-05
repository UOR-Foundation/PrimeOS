/**
 * Tests for the Schema Search functionality
 */

const searchLib = require('../lib/index/search/index.js');
const mutateLib = require('../lib/index/mutate/index.js');
const { getIndex } = require('../lib/index/common/index-manager.js');

// Test schemas with different types and properties
const testSchemas = [
  {
    name: 'test-axiom',
    schema: {
      "$schema": "https://json-schema.org/draft/2020-12/schema",
      "$id": "https://uor.foundation/test/axiom-test",
      "title": "Test Axiom Schema",
      "description": "A test axiom schema",
      "type": "object",
      "schemaType": "axiom",
      "namespace": "uor.foundation/test",
      "properties": {
        "axiomName": {
          "type": "string",
          "description": "Name of the axiom"
        },
        "axiomStatement": {
          "type": "string",
          "description": "Statement of the axiom"
        }
      }
    }
  },
  {
    name: 'test-entity',
    schema: {
      "$schema": "https://json-schema.org/draft/2020-12/schema",
      "$id": "https://uor.foundation/test/entity-test",
      "title": "Test Entity Schema",
      "description": "A test entity schema",
      "type": "object",
      "schemaType": "entity",
      "namespace": "uor.foundation/test",
      "properties": {
        "id": {
          "type": "string",
          "description": "Entity identifier"
        },
        "name": {
          "type": "string",
          "description": "Entity name"
        },
        "attributes": {
          "type": "object",
          "description": "Entity attributes"
        }
      }
    }
  },
  {
    name: 'test-component',
    schema: {
      "$schema": "https://json-schema.org/draft/2020-12/schema",
      "$id": "https://uor.foundation/test/component-test",
      "title": "Test Component Schema",
      "description": "A test component schema",
      "type": "object",
      "schemaType": "component",
      "namespace": "uor.foundation/test",
      "properties": {
        "componentId": {
          "type": "string",
          "description": "Component identifier"
        },
        "dependencies": {
          "type": "array",
          "items": {
            "$ref": "https://uor.foundation/test/entity-test"
          },
          "description": "Component dependencies"
        }
      }
    }
  }
];

/**
 * Run all schema search tests
 */
async function runTests() {
  console.log('Running Schema Search Tests...');
  
  // Setup test data
  setupTestData();
  
  // Test namespace filtering
  testNamespaceFiltering();
  
  // Test schema type filtering
  testSchemaTypeFiltering();
  
  // Test property search
  testPropertySearch();
  
  // Test reference search
  testReferenceSearch();
  
  // Test pattern matching
  testPatternMatching();
  
  console.log('All schema search tests completed!');
}

/**
 * Setup test data by indexing test schemas
 */
function setupTestData() {
  console.log('\n--- Setting up test schema data ---');
  
  // Index test schemas
  for (const { name, schema } of testSchemas) {
    const result = mutateLib.mutate({
      content: schema,
      apiName: 'uor.foundation',
      endpointName: name,
      mediaType: 'schema.json',
      isSchema: true
    });
    
    console.log(`Index ${name} schema:`, result.success ? 'PASS' : 'FAIL');
  }
}

/**
 * Test namespace filtering
 */
function testNamespaceFiltering() {
  console.log('\n--- Testing Namespace Filtering ---');
  
  const result = searchLib.searchIndex({ namespace: 'uor.foundation/test' });
  
  console.log('Filter by namespace:', 
    result.success && result.results.length >= 3 ? 'PASS' : 'FAIL',
    `(Found ${result.results.length} schemas)`
  );
}

/**
 * Test schema type filtering
 */
function testSchemaTypeFiltering() {
  console.log('\n--- Testing Schema Type Filtering ---');
  
  // Test filtering by axiom type
  const axiomResult = searchLib.searchIndex({ schemaType: 'axiom' });
  console.log('Filter by axiom type:', 
    axiomResult.success && axiomResult.results.some(r => r.type === 'axiom') ? 'PASS' : 'FAIL',
    `(Found ${axiomResult.results.length} schemas)`
  );
  
  // Test filtering by entity type
  const entityResult = searchLib.searchIndex({ schemaType: 'entity' });
  console.log('Filter by entity type:', 
    entityResult.success && entityResult.results.some(r => r.type === 'entity') ? 'PASS' : 'FAIL',
    `(Found ${entityResult.results.length} schemas)`
  );
}

/**
 * Test property search
 */
function testPropertySearch() {
  console.log('\n--- Testing Property Search ---');
  
  // Test searching for schemas with a specific property
  const propertyResult = searchLib.searchIndex({ property: 'axiomName' });
  console.log('Search by property name:', 
    propertyResult.success && propertyResult.results.length >= 1 ? 'PASS' : 'FAIL',
    `(Found ${propertyResult.results.length} schemas)`
  );
  
  // Test searching for schemas with a property of specific type
  const propertyTypeResult = searchLib.searchIndex({ 
    property: 'dependencies', 
    propertyType: 'array' 
  });
  console.log('Search by property with type:', 
    propertyTypeResult.success && propertyTypeResult.results.length >= 1 ? 'PASS' : 'FAIL',
    `(Found ${propertyTypeResult.results.length} schemas)`
  );
}

/**
 * Test reference search
 */
function testReferenceSearch() {
  console.log('\n--- Testing Reference Search ---');
  
  // Test searching for schemas that reference another schema
  const referenceResult = searchLib.searchIndex({ 
    references: 'https://uor.foundation/test/entity-test' 
  });
  console.log('Search by reference:', 
    referenceResult.success && referenceResult.results.length >= 1 ? 'PASS' : 'FAIL',
    `(Found ${referenceResult.results.length} schemas)`
  );
}

/**
 * Test pattern matching
 */
function testPatternMatching() {
  console.log('\n--- Testing Pattern Matching ---');
  
  // Test searching by text pattern
  const patternResult = searchLib.searchIndex({ pattern: 'component' });
  console.log('Search by text pattern:', 
    patternResult.success && patternResult.results.length >= 1 ? 'PASS' : 'FAIL',
    `(Found ${patternResult.results.length} schemas)`
  );
}

// Run the tests
runTests().catch(console.error);
