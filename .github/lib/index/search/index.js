/**
 * Index API - Search Endpoint
 * 
 * Search for schemas in the index
 */

const { getIndex } = require('../common/index-manager');
const resolveLib = require('../resolve/index');

/**
 * Search the index for schemas based on criteria
 * 
 * @param {Object} params - Search parameters
 * @returns {Object} - Search results with schema metadata
 */
function searchIndex(params) {
  const { 
    namespace,        // Filter by namespace (e.g., "uor.foundation")
    schemaType,       // Filter by schema type (e.g., "axiom", "test", "core")
    property,         // Search for schemas containing specific property
    propertyType,     // Filter by property type
    references,       // Find schemas that reference another schema by $id
    pattern,          // Pattern to match against schema $id, title, or description
    includeContent,   // Whether to include full schema content in results
    limit,
    offset,
    sortBy,
    sortOrder
  } = params;
  
  try {
    // Get the full index
    const index = getIndex();
    let results = [];
    
    // First pass: collect all matching entries from the index
    let matchingEntries = [...index];
    
    // Apply basic filters on index entries if provided
    // No filtering at the index level for namespace, as namespace is a property of the schema
    // We'll filter by namespace after resolving the schema content
    
    // For each matching entry, resolve the schema and apply deeper filters
    for (const entry of matchingEntries) {
      try {
        // Resolve the schema content
        const resolveResult = resolveLib.resolveJson(
          entry.anchor, 
          entry.endpoint, 
          entry.media
        );
        
        if (!resolveResult.success) continue;
        
        const schema = resolveResult.content;
        let matches = true;
        
        // Filter by namespace if specified
        if (namespace && matches) {
          const schemaNamespace = schema.namespace || entry.anchor;
          if (!schemaNamespace.startsWith(namespace)) {
            matches = false;
          }
        }
        
        // Filter by schema type if specified
        if (schemaType && schema.schemaType !== schemaType && matches) {
          matches = false;
        }
        
        // Search for specific property if specified
        if (property && matches) {
          matches = hasProperty(schema, property, propertyType);
        }
        
        // Search for references to another schema
        if (references && matches) {
          matches = hasReference(schema, references);
        }
        
        // Apply pattern matching if specified
        if (pattern && matches) {
          const searchableText = [
            schema.$id || '',
            schema.title || '',
            schema.description || ''
          ].join(' ').toLowerCase();
          
          matches = searchableText.includes(pattern.toLowerCase());
        }
        
        // If all filters pass, add to results
        if (matches) {
          const result = {
            id: schema.$id || `${entry.anchor}.${entry.endpoint}.${entry.media}`,
            title: schema.title || entry.endpoint,
            type: schema.schemaType || 'unknown',
            namespace: schema.namespace || entry.anchor,
            description: schema.description || '',
            entry: {
              apiName: entry.anchor,
              endpointName: entry.endpoint,
              mediaType: entry.media
            }
          };
          
          // Include full schema content if requested
          if (includeContent) {
            result.schema = schema;
          }
          
          results.push(result);
        }
      } catch (error) {
        console.error(`Error processing entry ${entry.anchor}.${entry.endpoint}.${entry.media}: ${error.message}`);
        // Continue with next entry
      }
    }
    
    // Calculate total count before sorting and pagination
    const totalCount = results.length;
    
    // Sort results if requested
    if (sortBy) {
      results.sort((a, b) => {
        let aValue = a[sortBy];
        let bValue = b[sortBy];
        
        // Handle nested properties
        if (sortBy.includes('.')) {
          const parts = sortBy.split('.');
          aValue = parts.reduce((obj, part) => obj && obj[part], a);
          bValue = parts.reduce((obj, part) => obj && obj[part], b);
        }
        
        if (typeof aValue === 'string' && typeof bValue === 'string') {
          return sortOrder === 'desc' 
            ? bValue.localeCompare(aValue) 
            : aValue.localeCompare(bValue);
        }
        
        return sortOrder === 'desc' ? bValue - aValue : aValue - bValue;
      });
    }
    
    // Apply pagination if requested
    if (limit !== undefined) {
      const start = offset || 0;
      results = results.slice(start, start + limit);
    }
    
    return {
      success: true,
      results,
      totalCount,
      count: results.length
    };
  } catch (error) {
    return {
      success: false,
      error: error.message
    };
  }
}

/**
 * Check if a schema has a specific property
 * 
 * @param {Object} schema - The schema to check
 * @param {string} propertyName - The name of the property to find
 * @param {string} propertyType - Optional type of the property
 * @returns {boolean} - Whether the schema has the property
 */
function hasProperty(schema, propertyName, propertyType) {
  // Check direct properties
  if (schema.properties && schema.properties[propertyName]) {
    if (!propertyType || schema.properties[propertyName].type === propertyType) {
      return true;
    }
  }
  
  // Check nested properties
  if (schema.properties) {
    for (const prop in schema.properties) {
      if (schema.properties[prop].type === 'object' && schema.properties[prop].properties) {
        if (hasProperty(schema.properties[prop], propertyName, propertyType)) {
          return true;
        }
      }
    }
  }
  
  // Check definitions/components
  if (schema.definitions) {
    for (const def in schema.definitions) {
      if (hasProperty(schema.definitions[def], propertyName, propertyType)) {
        return true;
      }
    }
  }
  
  return false;
}

/**
 * Check if a schema references another schema
 * 
 * @param {Object} schema - The schema to check
 * @param {string} reference - The reference to find (schema $id)
 * @returns {boolean} - Whether the schema references the other schema
 */
function hasReference(schema, reference) {
  // Convert schema to string and check for reference
  const schemaStr = JSON.stringify(schema);
  return schemaStr.includes(reference);
}

module.exports = {
  searchIndex
};
