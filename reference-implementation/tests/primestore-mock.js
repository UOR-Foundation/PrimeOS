/**
 * PrimeOS Reference Implementation - Mock for PrimeStore
 * 
 * This file provides a mock implementation of IndexedDB for unit testing PrimeStore.
 */

// Create a mock implementation of IndexedDB
class MockIndexedDB {
  constructor() {
    this.databases = {};
    this.objectStores = {};
    this.records = {};
  }
  
  // Mock open method
  open(name, version) {
    const request = this._createRequest();
    
    // Create the database if it doesn't exist
    if (!this.databases[name]) {
      this.databases[name] = {
        name,
        version,
        objectStoreNames: []
      };
      
      // Create a transaction for the upgrade
      const transaction = {
        objectStore: (storeName) => this._getObjectStore(storeName)
      };
      
      // Simulate the upgrade event
      setTimeout(() => {
        if (request.onupgradeneeded) {
          request.transaction = transaction;
          request.result = this.databases[name];
          request.target = { result: this.databases[name] };
          request.oldVersion = 0;
          request.newVersion = version;
          
          request.onupgradeneeded({
            target: request,
            oldVersion: 0,
            newVersion: version
          });
        }
        
        // Simulate the success event
        if (request.onsuccess) {
          request.result = this._createDatabaseConnection(name);
          request.target = { result: request.result };
          request.onsuccess({ target: request });
        }
      }, 0);
    } else {
      // Return the existing database
      setTimeout(() => {
        if (request.onsuccess) {
          request.result = this._createDatabaseConnection(name);
          request.target = { result: request.result };
          request.onsuccess({ target: request });
        }
      }, 0);
    }
    
    return request;
  }
  
  // Mock deleteDatabase method
  deleteDatabase(name) {
    const request = this._createRequest();
    
    setTimeout(() => {
      // Delete the database data
      delete this.databases[name];
      
      // Clear related records
      Object.keys(this.records).forEach(storeName => {
        if (storeName.startsWith(`${name}:`)) {
          delete this.records[storeName];
        }
      });
      
      if (request.onsuccess) {
        request.onsuccess({ target: request });
      }
    }, 0);
    
    return request;
  }
  
  // Helper to create database connection
  _createDatabaseConnection(name) {
    const db = this.databases[name];
    
    return {
      name: db.name,
      version: db.version,
      objectStoreNames: db.objectStoreNames,
      
      // Mock createObjectStore method
      createObjectStore: (storeName, options) => {
        // Add to objectStoreNames
        if (!db.objectStoreNames.includes(storeName)) {
          db.objectStoreNames.push(storeName);
        }
        
        // Create the store if it doesn't exist
        const storeKey = `${name}:${storeName}`;
        if (!this.objectStores[storeKey]) {
          this.objectStores[storeKey] = {
            name: storeName,
            keyPath: options.keyPath,
            autoIncrement: options.autoIncrement || false,
            indexes: {}
          };
          
          // Initialize the records for this store
          this.records[storeKey] = {};
        }
        
        return this._getObjectStore(storeKey);
      },
      
      // Mock transaction method
      transaction: (storeNames, mode) => {
        const storesList = Array.isArray(storeNames) ? storeNames : [storeNames];
        
        return {
          mode,
          objectStore: (storeName) => {
            return this._getObjectStore(`${name}:${storeName}`);
          }
        };
      },
      
      // Mock close method
      close: () => {}
    };
  }
  
  // Helper to get an object store
  _getObjectStore(storeKey) {
    const store = this.objectStores[storeKey];
    
    return {
      name: store.name,
      keyPath: store.keyPath,
      indexNames: Object.keys(store.indexes),
      
      // Mock put method
      put: (value) => {
        const request = this._createRequest();
        
        setTimeout(() => {
          try {
            const key = value[store.keyPath];
            if (key === undefined) {
              throw new Error(`Object doesn't have keyPath property: ${store.keyPath}`);
            }
            
            this.records[storeKey][key] = { ...value };
            
            request.result = key;
            request.target = { result: key };
            
            if (request.onsuccess) {
              request.onsuccess({ target: request });
            }
          } catch (error) {
            request.error = error;
            
            if (request.onerror) {
              request.onerror({ target: request });
            }
          }
        }, 0);
        
        return request;
      },
      
      // Mock get method
      get: (key) => {
        const request = this._createRequest();
        
        setTimeout(() => {
          try {
            request.result = this.records[storeKey][key];
            request.target = { result: request.result };
            
            if (request.onsuccess) {
              request.onsuccess({ target: request });
            }
          } catch (error) {
            request.error = error;
            
            if (request.onerror) {
              request.onerror({ target: request });
            }
          }
        }, 0);
        
        return request;
      },
      
      // Mock getAll method
      getAll: () => {
        const request = this._createRequest();
        
        setTimeout(() => {
          try {
            request.result = Object.values(this.records[storeKey]);
            request.target = { result: request.result };
            
            if (request.onsuccess) {
              request.onsuccess({ target: request });
            }
          } catch (error) {
            request.error = error;
            
            if (request.onerror) {
              request.onerror({ target: request });
            }
          }
        }, 0);
        
        return request;
      },
      
      // Mock delete method
      delete: (key) => {
        const request = this._createRequest();
        
        setTimeout(() => {
          try {
            delete this.records[storeKey][key];
            
            if (request.onsuccess) {
              request.onsuccess({ target: request });
            }
          } catch (error) {
            request.error = error;
            
            if (request.onerror) {
              request.onerror({ target: request });
            }
          }
        }, 0);
        
        return request;
      },
      
      // Mock clear method
      clear: () => {
        const request = this._createRequest();
        
        setTimeout(() => {
          try {
            this.records[storeKey] = {};
            
            if (request.onsuccess) {
              request.onsuccess({ target: request });
            }
          } catch (error) {
            request.error = error;
            
            if (request.onerror) {
              request.onerror({ target: request });
            }
          }
        }, 0);
        
        return request;
      },
      
      // Mock createIndex method
      createIndex: (name, keyPath, options) => {
        store.indexes[name] = {
          name,
          keyPath,
          unique: options?.unique || false
        };
        
        return {
          name,
          keyPath,
          unique: options?.unique || false
        };
      },
      
      // Mock index method
      index: (name) => {
        const index = store.indexes[name];
        
        return {
          name: index.name,
          keyPath: index.keyPath,
          unique: index.unique,
          
          // Mock getAll method
          getAll: (query) => {
            const request = this._createRequest();
            
            setTimeout(() => {
              try {
                let results = Object.values(this.records[storeKey]);
                
                if (query && typeof query === 'object' && 'only' in query) {
                  results = results.filter(record => {
                    return record[index.keyPath] === query.only;
                  });
                }
                
                request.result = results;
                request.target = { result: results };
                
                if (request.onsuccess) {
                  request.onsuccess({ target: request });
                }
              } catch (error) {
                request.error = error;
                
                if (request.onerror) {
                  request.onerror({ target: request });
                }
              }
            }, 0);
            
            return request;
          }
        };
      }
    };
  }
  
  // Helper to create an IDBRequest-like object
  _createRequest() {
    return {
      result: undefined,
      error: null,
      source: null,
      transaction: null,
      readyState: 'pending',
      onsuccess: null,
      onerror: null,
      onupgradeneeded: null
    };
  }
}

// Create IDBKeyRange mock
const MockIDBKeyRange = {
  only: (value) => ({ only: value }),
  lowerBound: (lower, open) => ({ lower, open, lowerBound: true }),
  upperBound: (upper, open) => ({ upper, open, upperBound: true }),
  bound: (lower, upper, lowerOpen, upperOpen) => ({ 
    lower, upper, lowerOpen, upperOpen, bound: true 
  })
};

module.exports = {
  MockIndexedDB,
  MockIDBKeyRange
};