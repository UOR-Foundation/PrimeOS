/**
 * Simple Example PrimeApp Schema Registry
 */

// In a real implementation, this would use the PrimeOS schema system
const SchemaRegistry = {
  namespace: 'simple-example',
  version: '1.0.0',
  
  schemas: {
    MessageResult: {
      type: 'object',
      properties: {
        original: { type: 'string' },
        processed: { type: 'string' },
        timestamp: { type: 'number' },
        counter: { type: 'number' }
      }
    }
  },
  
  // Validate a message result
  validateMessageResult(result) {
    const schema = this.schemas.MessageResult;
    
    // Simple validation
    if (!result || typeof result !== 'object') return false;
    if (typeof result.original !== 'string') return false;
    if (typeof result.processed !== 'string') return false;
    if (typeof result.timestamp !== 'number') return false;
    if (typeof result.counter !== 'number') return false;
    
    return true;
  }
};

module.exports = SchemaRegistry;