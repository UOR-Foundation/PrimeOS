/**
 * PrimeOS Reference Implementation - Network Adapter
 * 
 * Provides a consistent interface for network communication with remote PrimeOS instances.
 * Handles authentication, request formatting, and error handling.
 */

/**
 * NetworkAdapter
 * 
 * A simple adapter for making HTTP requests to remote PrimeOS endpoints.
 */
class NetworkAdapter {
  /**
   * Create a new NetworkAdapter
   * @param {Object} options - Configuration options
   * @param {Function} [options.requestHandler] - Custom request handler (for testing)
   * @param {Object} [options.headers] - Default headers to include with requests
   */
  constructor(options = {}) {
    this.requestHandler = options.requestHandler || this._defaultRequestHandler;
    this.headers = {
      'Content-Type': 'application/json',
      'Accept': 'application/json',
      ...(options.headers || {})
    };
    this.authToken = null;
  }
  
  /**
   * Set authentication token
   * @param {string} token - Authentication token
   */
  setAuthToken(token) {
    this.authToken = token;
  }
  
  /**
   * Perform GET request
   * @param {string} url - Target URL
   * @param {Object} [options] - Request options
   * @returns {Promise<Object>} Response data
   */
  async get(url, options = {}) {
    return this._request('GET', url, null, options);
  }
  
  /**
   * Perform POST request
   * @param {string} url - Target URL
   * @param {Object} data - Request payload
   * @param {Object} [options] - Request options
   * @returns {Promise<Object>} Response data
   */
  async post(url, data, options = {}) {
    return this._request('POST', url, data, options);
  }
  
  /**
   * Perform PUT request
   * @param {string} url - Target URL
   * @param {Object} data - Request payload
   * @param {Object} [options] - Request options
   * @returns {Promise<Object>} Response data
   */
  async put(url, data, options = {}) {
    return this._request('PUT', url, data, options);
  }
  
  /**
   * Perform DELETE request
   * @param {string} url - Target URL
   * @param {Object} [options] - Request options
   * @returns {Promise<Object>} Response data
   */
  async delete(url, options = {}) {
    return this._request('DELETE', url, null, options);
  }
  
  /**
   * Perform HTTP request
   * @param {string} method - HTTP method
   * @param {string} url - Target URL
   * @param {Object|null} data - Request payload
   * @param {Object} [options] - Request options
   * @returns {Promise<Object>} Response data
   * @private
   */
  async _request(method, url, data = null, options = {}) {
    try {
      // Prepare headers
      const headers = { ...this.headers, ...options.headers };
      
      // Add auth token if available
      if (this.authToken) {
        headers['Authorization'] = `Bearer ${this.authToken}`;
      }
      
      // Prepare request object
      const requestObj = {
        method,
        headers,
        timeout: options.timeout || 30000,
        ...options
      };
      
      // Add body for methods that support it
      if (['POST', 'PUT', 'PATCH'].includes(method) && data !== null) {
        requestObj.body = JSON.stringify(data);
      }
      
      // Send request
      const response = await this.requestHandler(url, requestObj);
      
      // Return normalized response
      return {
        data: response.data,
        status: response.status,
        headers: response.headers,
        originalResponse: response
      };
    } catch (error) {
      // Normalize error
      const normalizedError = this._normalizeError(error);
      throw normalizedError;
    }
  }
  
  /**
   * Default request handler implementation using fetch
   * @param {string} url - Target URL
   * @param {Object} requestObj - Request configuration
   * @returns {Promise<Object>} Response object
   * @private
   */
  async _defaultRequestHandler(url, requestObj) {
    // Use fetch API
    const response = await fetch(url, requestObj);
    
    // Check for HTTP errors
    if (!response.ok) {
      const errorData = await response.json().catch(() => ({}));
      const error = new Error(errorData.message || response.statusText || 'Network request failed');
      error.status = response.status;
      error.data = errorData;
      throw error;
    }
    
    // Parse JSON response
    const data = await response.json().catch(() => ({}));
    
    // Return normalized response
    return {
      data,
      status: response.status,
      headers: Object.fromEntries(response.headers.entries()),
      ok: response.ok
    };
  }
  
  /**
   * Normalize error object
   * @param {Error} error - Original error
   * @returns {Error} Normalized error
   * @private
   */
  _normalizeError(error) {
    // If already normalized, return as is
    if (error.isNetworkError) {
      return error;
    }
    
    // Create normalized error
    const normalizedError = new Error(error.message || 'Network error');
    normalizedError.isNetworkError = true;
    normalizedError.originalError = error;
    normalizedError.status = error.status || 0;
    normalizedError.data = error.data || null;
    
    return normalizedError;
  }
}

// Export module
module.exports = { NetworkAdapter };