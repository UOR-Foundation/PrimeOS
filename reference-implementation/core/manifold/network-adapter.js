/**
 * Network Adapter
 * 
 * Provides HTTP communication for the Manifold Import/Export system.
 */

class NetworkAdapter {
  constructor() {
    this.authToken = null;
  }
  
  /**
   * Set authentication token
   */
  setAuthToken(token) {
    this.authToken = token;
  }
  
  /**
   * Make a GET request
   */
  async get(url) {
    try {
      const headers = {
        'Content-Type': 'application/json'
      };
      
      if (this.authToken) {
        headers['Authorization'] = `Bearer ${this.authToken}`;
      }
      
      const response = await fetch(url, {
        method: 'GET',
        headers
      });
      
      const data = await response.json();
      
      return { data };
    } catch (error) {
      throw new Error(`Network error: ${error.message}`);
    }
  }
  
  /**
   * Make a POST request
   */
  async post(url, data) {
    try {
      const headers = {
        'Content-Type': 'application/json'
      };
      
      if (this.authToken) {
        headers['Authorization'] = `Bearer ${this.authToken}`;
      }
      
      const response = await fetch(url, {
        method: 'POST',
        headers,
        body: JSON.stringify(data)
      });
      
      const responseData = await response.json();
      
      return { data: responseData };
    } catch (error) {
      throw new Error(`Network error: ${error.message}`);
    }
  }
}

// CommonJS export
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { NetworkAdapter };
}

// ES module export
export { NetworkAdapter };
