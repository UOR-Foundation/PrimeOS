/**
 * PrimeStore - Coherence-aware IndexedDB Storage System
 * Core storage service for the PrimeOS Reference Implementation
 */

// Global connection and stores configuration
const DB_VERSION = 1;
const DB_NAME = 'PrimeOS_Store';
let db = null;

// Object stores configuration
const storeConfigs = {
    system: {
        name: 'system',
        keyPath: 'id',
        indexes: [
            { name: 'type', keyPath: 'type', unique: false }
        ],
        coherenceRules: [
            { name: 'ValidID', check: record => typeof record.id === 'string' && record.id.length > 0 },
            { name: 'ValidType', check: record => typeof record.type === 'string' && record.type.length > 0 }
        ]
    },
    files: {
        name: 'files',
        keyPath: 'path',
        indexes: [
            { name: 'name', keyPath: 'name', unique: false },
            { name: 'type', keyPath: 'type', unique: false },
            { name: 'created', keyPath: 'created', unique: false },
            { name: 'modified', keyPath: 'modified', unique: false }
        ],
        coherenceRules: [
            { name: 'ValidPath', check: record => typeof record.path === 'string' && record.path.length > 0 },
            { name: 'ValidCreated', check: record => record.created instanceof Date },
            { name: 'ValidModified', check: record => record.modified instanceof Date },
            { name: 'ValidTimestamps', check: record => record.modified >= record.created }
        ]
    },
    apps: {
        name: 'apps',
        keyPath: 'id',
        indexes: [
            { name: 'name', keyPath: 'name', unique: false },
            { name: 'version', keyPath: 'version', unique: false },
            { name: 'installed', keyPath: 'installed', unique: false }
        ],
        coherenceRules: [
            { name: 'ValidID', check: record => typeof record.id === 'string' && record.id.length > 0 },
            { name: 'ValidName', check: record => typeof record.name === 'string' && record.name.length > 0 },
            { name: 'ValidVersion', check: record => typeof record.version === 'string' && /^\d+\.\d+\.\d+/.test(record.version) }
        ]
    },
    identity: {
        name: 'identity',
        keyPath: 'id',
        indexes: [
            { name: 'username', keyPath: 'username', unique: true },
            { name: 'lastLogin', keyPath: 'lastLogin', unique: false }
        ],
        coherenceRules: [
            { name: 'ValidID', check: record => typeof record.id === 'string' && record.id.length > 0 },
            { name: 'ValidUsername', check: record => typeof record.username === 'string' && record.username.length >= 3 }
        ]
    }
};

/**
 * Initialize the database
 * @returns {Promise} Promise that resolves when DB is ready
 */
async function initializeDatabase() {
    return new Promise((resolve, reject) => {
        if (db) {
            resolve(db);
            return;
        }
        
        if (!window.indexedDB) {
            reject(new Error('IndexedDB is not supported in this browser'));
            return;
        }
        
        const request = indexedDB.open(DB_NAME, DB_VERSION);
        
        request.onupgradeneeded = function(event) {
            const db = event.target.result;
            const existingStoreNames = Array.from(db.objectStoreNames);
            
            // Create or update object stores
            for (const storeConfig of Object.values(storeConfigs)) {
                let objectStore;
                
                // Create store if it doesn't exist
                if (!existingStoreNames.includes(storeConfig.name)) {
                    objectStore = db.createObjectStore(storeConfig.name, { keyPath: storeConfig.keyPath });
                    console.log(`Created object store: ${storeConfig.name}`);
                } else {
                    objectStore = event.target.transaction.objectStore(storeConfig.name);
                }
                
                // Create indexes
                if (storeConfig.indexes) {
                    const existingIndexNames = Array.from(objectStore.indexNames);
                    
                    for (const indexConfig of storeConfig.indexes) {
                        if (!existingIndexNames.includes(indexConfig.name)) {
                            objectStore.createIndex(indexConfig.name, indexConfig.keyPath, { 
                                unique: indexConfig.unique || false 
                            });
                            console.log(`Created index: ${indexConfig.name} on ${storeConfig.name}`);
                        }
                    }
                }
            }
            
            // Log confirmation message 
            console.log(`Initialized ${Object.keys(storeConfigs).length} object stores: ${Object.keys(storeConfigs).join(', ')}`);
        };
        
        request.onsuccess = function(event) {
            db = event.target.result;
            console.log('PrimeStore database initialized successfully');
            resolve(db);
        };
        
        request.onerror = function(event) {
            console.error('Failed to initialize PrimeStore database:', event.target.error);
            reject(event.target.error);
        };
    });
}

/**
 * PrimeStore Constructor - Creates a new store instance
 * @param {string} storeName - The name of the store to use
 */
function PrimeStore(storeName) {
    // Validate store name
    if (!storeName) {
        console.error('No store name provided to PrimeStore constructor');
        storeName = 'system'; // Default to system store as fallback
    }
    
    // Check if the store config exists
    if (storeName && !storeConfigs[storeName]) {
        console.warn(`Unknown store name "${storeName}" provided to PrimeStore. Available stores: ${Object.keys(storeConfigs).join(', ')}`);
        
        // Fall back to first available store if provided store doesn't exist
        if (Object.keys(storeConfigs).length > 0) {
            storeName = Object.keys(storeConfigs)[0];
            console.warn(`Falling back to "${storeName}" store instead`);
        }
    }
    
    this.storeName = storeName;
    this.initialized = false;
    
    // Log creation
    console.log(`PrimeStore instance created for "${this.storeName}" store`);
}

/**
 * Initialize this store instance
 * @returns {Promise} Promise that resolves when ready
 */
PrimeStore.prototype.initialize = async function() {
    if (this.initialized) return;
    
    try {
        await initializeDatabase();
        this.initialized = true;
        console.log(`PrimeStore instance for ${this.storeName} initialized`);
    } catch (error) {
        console.error(`Failed to initialize PrimeStore for ${this.storeName}:`, error);
        throw error;
    }
};

/**
 * Check data coherence against rules
 * @param {Object} record - Record to check
 * @returns {Object} Coherence check result with violations if any
 */
PrimeStore.prototype.checkCoherence = function(record) {
    const storeConfig = storeConfigs[this.storeName];
    if (!storeConfig) {
        throw new Error(`Unknown store: ${this.storeName}`);
    }
    
    // Skip coherence checks for app preferences which have a special format
    if (typeof record.id === 'string' && record.id.startsWith('app_preferences_')) {
        return {
            isCoherent: true,
            violations: [],
            record
        };
    }
    
    const rules = storeConfig.coherenceRules || [];
    const violations = [];
    
    for (const rule of rules) {
        try {
            if (!rule.check(record)) {
                violations.push({
                    rule: rule.name,
                    message: `Failed coherence rule: ${rule.name}`
                });
            }
        } catch (error) {
            violations.push({
                rule: rule.name,
                message: `Error during coherence check: ${error.message}`,
                error
            });
        }
    }
    
    return {
        isCoherent: violations.length === 0,
        violations,
        record
    };
};

/**
 * Store a record with coherence validation
 * @param {string|number} key - The key if different from record's keyPath
 * @param {Object} record - Record to store
 * @param {Object} options - Options
 * @returns {Promise} Promise resolving to stored record
 */
PrimeStore.prototype.put = async function(key, record, options = {}) {
    await this.initialize();
    
    // Handle case where only record is provided (key is part of the record)
    if (typeof key === 'object' && record === undefined) {
        record = key;
        key = undefined;
    }
    
    // Check coherence if not disabled
    if (!options.skipCoherenceCheck) {
        const coherenceResult = this.checkCoherence(record);
        
        if (!coherenceResult.isCoherent) {
            if (options.force) {
                console.warn('Storing incoherent record (forced):', coherenceResult.violations);
            } else {
                throw new Error(`Coherence violation: ${JSON.stringify(coherenceResult.violations)}`);
            }
        }
    }
    
    return new Promise((resolve, reject) => {
        const transaction = db.transaction([this.storeName], 'readwrite');
        const objectStore = transaction.objectStore(this.storeName);
        
        // Add metadata
        const enhancedRecord = { ...record };
        if (this.storeName === 'files') {
            enhancedRecord.modified = new Date();
            if (!enhancedRecord.created) {
                enhancedRecord.created = new Date();
            }
        }
        
        // Use put with or without explicit key
        const request = key !== undefined 
            ? objectStore.put(enhancedRecord, key)
            : objectStore.put(enhancedRecord);
        
        request.onsuccess = function() {
            resolve(enhancedRecord);
        };
        
        request.onerror = function(event) {
            reject(event.target.error);
        };
    });
};

/**
 * Save multiple items with same key prefix
 * @param {string} keyPrefix - Key prefix for the collection
 * @param {Array} values - Array of values to store
 * @returns {Promise} Promise that resolves when all items are saved
 */
PrimeStore.prototype.saveAll = async function(keyPrefix, values) {
    await this.initialize();
    
    if (!Array.isArray(values)) {
        throw new Error('Values must be an array');
    }
    
    const transaction = db.transaction([this.storeName], 'readwrite');
    const objectStore = transaction.objectStore(this.storeName);
    
    // Create a single promise that resolves when the transaction completes
    return new Promise((resolve, reject) => {
        transaction.oncomplete = function() {
            resolve(values);
        };
        
        transaction.onerror = function(event) {
            reject(event.target.error);
        };
        
        // Add or update each record
        values.forEach(value => {
            try {
                objectStore.put(value);
            } catch (error) {
                console.error('Error saving item:', error);
                // Continue with other records even if one fails
            }
        });
    });
};

/**
 * Get a record by key
 * @param {string|number} key - Record key
 * @returns {Promise} Promise resolving to the record
 */
PrimeStore.prototype.get = async function(key) {
    await this.initialize();
    
    return new Promise((resolve, reject) => {
        const transaction = db.transaction([this.storeName], 'readonly');
        const objectStore = transaction.objectStore(this.storeName);
        const request = objectStore.get(key);
        
        request.onsuccess = function() {
            resolve(request.result);
        };
        
        request.onerror = function(event) {
            reject(event.target.error);
        };
    });
};

/**
 * Delete a record by key
 * @param {string|number} key - Record key
 * @returns {Promise} Promise resolving when the record is deleted
 */
PrimeStore.prototype.remove = async function(key) {
    await this.initialize();
    
    return new Promise((resolve, reject) => {
        const transaction = db.transaction([this.storeName], 'readwrite');
        const objectStore = transaction.objectStore(this.storeName);
        const request = objectStore.delete(key);
        
        request.onsuccess = function() {
            resolve();
        };
        
        request.onerror = function(event) {
            reject(event.target.error);
        };
    });
};

/**
 * Query records by index
 * @param {Object} query - Query parameters
 * @returns {Promise} Promise resolving to matching records
 */
PrimeStore.prototype.query = async function(query = {}) {
    await this.initialize();
    
    return new Promise((resolve, reject) => {
        const transaction = db.transaction([this.storeName], 'readonly');
        const objectStore = transaction.objectStore(this.storeName);
        
        let request;
        
        if (query.index && query.value !== undefined) {
            // Query by index
            const index = objectStore.index(query.index);
            const range = query.range || IDBKeyRange.only(query.value);
            request = index.getAll(range);
        } else {
            // Get all records
            request = objectStore.getAll();
        }
        
        request.onsuccess = function() {
            const results = request.result;
            
            // Apply filters if provided
            if (query.filter && typeof query.filter === 'function') {
                resolve(results.filter(query.filter));
            } else {
                resolve(results);
            }
        };
        
        request.onerror = function(event) {
            reject(event.target.error);
        };
    });
};

/**
 * Get all records from the store
 * @returns {Promise} Promise resolving to all records
 */
PrimeStore.prototype.getAll = async function() {
    return this.query();
};

/**
 * Create a coherence report for all records in the store
 * @returns {Promise} Promise resolving to coherence report
 */
PrimeStore.prototype.checkStoreCoherence = async function() {
    const records = await this.getAll();
    
    const results = {
        storeName: this.storeName,
        totalRecords: records.length,
        coherentRecords: 0,
        incoherentRecords: 0,
        violations: []
    };
    
    for (const record of records) {
        const coherenceResult = this.checkCoherence(record);
        
        if (coherenceResult.isCoherent) {
            results.coherentRecords++;
        } else {
            results.incoherentRecords++;
            results.violations.push({
                record: this.getRecordIdentifier(record),
                violations: coherenceResult.violations
            });
        }
    }
    
    results.coherenceScore = results.totalRecords > 0 
        ? results.coherentRecords / results.totalRecords
        : 1;
    
    return results;
};

/**
 * Get a readable identifier for a record
 * @private
 * @param {Object} record - The record
 * @returns {string} Record identifier
 */
PrimeStore.prototype.getRecordIdentifier = function(record) {
    const storeConfig = storeConfigs[this.storeName];
    if (!storeConfig) return 'unknown';
    
    const keyValue = record[storeConfig.keyPath];
    return `${this.storeName}:${keyValue}`;
};

/**
 * Clear all data in the store
 * @returns {Promise} Promise resolving when the store is cleared
 */
PrimeStore.prototype.clear = async function() {
    await this.initialize();
    
    return new Promise((resolve, reject) => {
        const transaction = db.transaction([this.storeName], 'readwrite');
        const objectStore = transaction.objectStore(this.storeName);
        const request = objectStore.clear();
        
        request.onsuccess = function() {
            resolve();
        };
        
        request.onerror = function(event) {
            reject(event.target.error);
        };
    });
};

/**
 * Delete the entire database
 * @returns {Promise} Promise resolving when the database is deleted
 */
PrimeStore.deleteDatabase = async function() {
    if (db) {
        db.close();
        db = null;
    }
    
    return new Promise((resolve, reject) => {
        const request = indexedDB.deleteDatabase(DB_NAME);
        
        request.onsuccess = function() {
            console.log('PrimeStore database deleted');
            resolve();
        };
        
        request.onerror = function(event) {
            reject(event.target.error);
        };
    });
};

// Add store names to constructor for reference
PrimeStore.stores = Object.keys(storeConfigs);

// Export for use in the PrimeOS environment
if (typeof window !== 'undefined') {
    window.PrimeStore = PrimeStore;
}

// Export using CommonJS for module use and testing
if (typeof module !== 'undefined' && module.exports) {
    module.exports = PrimeStore;
}