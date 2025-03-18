/**
 * Claude API Integration for App Factory - Browser Version
 * 
 * This module provides browser-compatible integration with the Claude API
 * for generating application specifications and code.
 */

/**
 * Claude API Client for browser environments
 */
class ClaudeAPIClientBrowser {
  constructor(options = {}) {
    this.apiKey = options.apiKey;
    this.model = options.model || 'claude-3-sonnet-20240229';
    this.baseUrl = 'https://api.anthropic.com/v1/messages';
    
    // In browser, we'll set the API key via the UI
    this.ready = !!this.apiKey;
  }
  
  /**
   * Set the API key
   * @param {string} apiKey - Claude API key
   */
  setApiKey(apiKey) {
    this.apiKey = apiKey;
    this.ready = !!apiKey;
    return this.ready;
  }
  
  /**
   * Set the model to use
   * @param {string} model - Claude model name
   */
  setModel(model) {
    this.model = model;
  }
  
  /**
   * Send a completion request to Claude API
   * @param {string} prompt - The prompt text
   * @param {Object} options - Additional options
   * @returns {Promise<Object>} Claude API response
   */
  async completion(prompt, options = {}) {
    if (!this.ready) {
      throw new Error('API key not set');
    }
    
    const requestBody = {
      model: options.model || this.model,
      max_tokens: options.max_tokens || 4000,
      messages: [
        { role: 'user', content: prompt }
      ],
      temperature: options.temperature || 0.7,
      stream: false
    };
    
    try {
      const response = await fetch(this.baseUrl, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          'x-api-key': this.apiKey,
          'anthropic-version': '2023-06-01'
        },
        body: JSON.stringify(requestBody)
      });
      
      if (!response.ok) {
        const errorData = await response.json();
        throw new Error(`Claude API error: ${response.status} - ${errorData.error?.message || 'Unknown error'}`);
      }
      
      const result = await response.json();
      return result;
    } catch (error) {
      console.error('Claude API request failed:', error);
      throw error;
    }
  }
  
  /**
   * Generate domain insights from user input
   * @param {Object} domainData - Domain data provided by user
   * @returns {Promise<Object>} Enhanced domain data with insights
   */
  async generateDomainInsights(domainData) {
    try {
      const prompt = `
You are an expert application architect tasked with understanding the domain of a new application. 
Please analyze the following information:

Purpose: ${domainData.purpose || 'Not specified'}
Target Audience: ${domainData.audience || 'Not specified'}

Based on this information, please provide:
1. 3-5 domain insights that would be valuable for development
2. 3-5 potential user archetypes or personas
3. 3-5 key functional areas for this application

Format your response as JSON with the following structure:
{
  "insights": ["insight 1", "insight 2", ...],
  "personas": ["persona 1", "persona 2", ...],
  "functionalAreas": ["area 1", "area 2", ...]
}
`;

      const response = await this.completion(prompt, {
        temperature: 0.3,
        max_tokens: 1000
      });
      
      // Extract the JSON from the response
      const content = response.content[0].text;
      
      // Parse the JSON response, handling potential JSON extraction issues
      let jsonStart = content.indexOf('{');
      let jsonEnd = content.lastIndexOf('}');
      
      if (jsonStart === -1 || jsonEnd === -1) {
        throw new Error('Invalid response format from Claude API');
      }
      
      const jsonText = content.substring(jsonStart, jsonEnd + 1);
      const result = JSON.parse(jsonText);
      
      // Combine with original domain data
      return {
        ...domainData,
        insights: result.insights || [],
        personas: result.personas || [],
        functionalAreas: result.functionalAreas || []
      };
    } catch (error) {
      console.error('Failed to generate domain insights:', error);
      // Return original data with error flag if API call fails
      return {
        ...domainData,
        insights: [`Error: ${error.message}`],
        error: true
      };
    }
  }
  
  /**
   * Generate app requirements suggestions based on domain
   * @param {Object} domain - Domain data with insights
   * @returns {Promise<Object>} Suggested requirements
   */
  async suggestRequirements(domain) {
    try {
      const prompt = `
You are an expert requirements analyst for software applications.
Based on the following domain information:

Purpose: ${domain.purpose || 'Not specified'}
Target Audience: ${domain.audience || 'Not specified'}
Domain Insights: ${domain.insights?.join(', ') || 'None'}
Personas: ${domain.personas?.join(', ') || 'None'}
Functional Areas: ${domain.functionalAreas?.join(', ') || 'None'}

Please suggest:
1. 3-5 data entities with their fields and relationships
2. 5-7 key features the application should have
3. 3-5 non-functional requirements (performance, security, etc.)

Format your response as JSON with the following structure:
{
  "entities": [
    {
      "name": "Entity name",
      "description": "Entity description",
      "fields": [
        { "name": "fieldName", "type": "string", "description": "field description" },
        ...
      ]
    },
    ...
  ],
  "features": [
    { "name": "Feature name", "description": "Feature description", "priority": "High/Medium/Low" },
    ...
  ],
  "nonFunctionalRequirements": [
    { "category": "Category", "description": "Requirement description" },
    ...
  ]
}
`;

      const response = await this.completion(prompt, {
        temperature: 0.4,
        max_tokens: 2000
      });
      
      // Extract the JSON from the response
      const content = response.content[0].text;
      
      // Parse the JSON response, handling potential JSON extraction issues
      let jsonStart = content.indexOf('{');
      let jsonEnd = content.lastIndexOf('}');
      
      if (jsonStart === -1 || jsonEnd === -1) {
        throw new Error('Invalid response format from Claude API');
      }
      
      const jsonText = content.substring(jsonStart, jsonEnd + 1);
      return JSON.parse(jsonText);
    } catch (error) {
      console.error('Failed to suggest requirements:', error);
      
      // Return fallback data if API call fails
      return {
        entities: [
          {
            name: 'User',
            description: 'Application user',
            fields: [
              { name: 'id', type: 'string', description: 'User ID' },
              { name: 'name', type: 'string', description: 'User name' }
            ]
          }
        ],
        features: [
          { name: 'User Authentication', description: 'Login and registration', priority: 'High' }
        ],
        nonFunctionalRequirements: [
          { category: 'Performance', description: 'The application should respond within 2 seconds' }
        ],
        error: true
      };
    }
  }
}

// Export for browser
if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.ClaudeAPIClientBrowser = ClaudeAPIClientBrowser;
}