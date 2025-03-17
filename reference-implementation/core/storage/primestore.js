/**
 * PrimeStore - Coherence-aware IndexedDB Storage System
 * Core storage service for the PrimeOS Reference Implementation
 */

// PrimeStore namespace
const PrimeStore = (function() {
    // Storage version - increment when schema changes
    const DB_VERSION = 1;
    const DB_NAME = 'PrimeOS_Store';
    
    // Database connection
    let db = null;
    
    // Object stores configuration
    const stores = {
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
    async function initialize() {
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
                for (const storeConfig of Object.values(stores)) {
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
            };
            
            request.onsuccess = function(event) {
                db = event.target.result;
                console.log('PrimeStore initialized successfully');
                resolve(db);
            };
            
            request.onerror = function(event) {
                console.error('Failed to initialize PrimeStore:', event.target.error);
                reject(event.target.error);
            };
        });
    }
    
    /**
     * Check data coherence against rules
     * @param {string} storeName - Name of the store
     * @param {Object} record - Record to check
     * @returns {Object} Coherence check result with violations if any
     */
    function checkCoherence(storeName, record) {
        const storeConfig = stores[storeName];
        if (!storeConfig) {
            throw new Error(`Unknown store: ${storeName}`);
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
    }
    
    /**
     * Store a record with coherence validation
     * @param {string} storeName - Name of the store
     * @param {Object} record - Record to store
     * @param {Object} options - Options
     * @returns {Promise} Promise resolving to stored record
     */
    async function put(storeName, record, options = {}) {
        await initialize();
        
        // Check coherence if not disabled
        if (!options.skipCoherenceCheck) {
            const coherenceResult = checkCoherence(storeName, record);
            
            if (!coherenceResult.isCoherent) {
                if (options.force) {
                    console.warn('Storing incoherent record (forced):', coherenceResult.violations);
                } else {
                    throw new Error(`Coherence violation: ${JSON.stringify(coherenceResult.violations)}`);
                }
            }
        }
        
        return new Promise((resolve, reject) => {
            const transaction = db.transaction([storeName], 'readwrite');
            const objectStore = transaction.objectStore(storeName);
            
            // Add metadata
            const enhancedRecord = { ...record };
            if (storeName === 'files') {
                enhancedRecord.modified = new Date();
                if (!enhancedRecord.created) {
                    enhancedRecord.created = new Date();
                }
            }
            
            const request = objectStore.put(enhancedRecord);
            
            request.onsuccess = function() {
                resolve(enhancedRecord);
            };
            
            request.onerror = function(event) {
                reject(event.target.error);
            };
        });
    }
    
    /**
     * Get a record by key
     * @param {string} storeName - Name of the store
     * @param {string|number} key - Record key
     * @returns {Promise} Promise resolving to the record
     */
    async function get(storeName, key) {
        await initialize();
        
        return new Promise((resolve, reject) => {
            const transaction = db.transaction([storeName], 'readonly');
            const objectStore = transaction.objectStore(storeName);
            const request = objectStore.get(key);
            
            request.onsuccess = function() {
                resolve(request.result);
            };
            
            request.onerror = function(event) {
                reject(event.target.error);
            };
        });
    }
    
    /**
     * Delete a record by key
     * @param {string} storeName - Name of the store
     * @param {string|number} key - Record key
     * @returns {Promise} Promise resolving when the record is deleted
     */
    async function remove(storeName, key) {
        await initialize();
        
        return new Promise((resolve, reject) => {
            const transaction = db.transaction([storeName], 'readwrite');
            const objectStore = transaction.objectStore(storeName);
            const request = objectStore.delete(key);
            
            request.onsuccess = function() {
                resolve();
            };
            
            request.onerror = function(event) {
                reject(event.target.error);
            };
        });
    }
    
    /**
     * Query records by index
     * @param {string} storeName - Name of the store
     * @param {Object} query - Query parameters
     * @returns {Promise} Promise resolving to matching records
     */
    async function query(storeName, query = {}) {
        await initialize();
        
        return new Promise((resolve, reject) => {
            const transaction = db.transaction([storeName], 'readonly');
            const objectStore = transaction.objectStore(storeName);
            
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
    }
    
    /**
     * Get all records from a store
     * @param {string} storeName - Name of the store
     * @returns {Promise} Promise resolving to all records
     */
    async function getAll(storeName) {
        return query(storeName);
    }
    
    /**
     * Create a coherence report for all records in a store
     * @param {string} storeName - Name of the store
     * @returns {Promise} Promise resolving to coherence report
     */
    async function checkStoreCoherence(storeName) {
        const records = await getAll(storeName);
        
        const results = {
            storeName,
            totalRecords: records.length,
            coherentRecords: 0,
            incoherentRecords: 0,
            violations: []
        };
        
        for (const record of records) {
            const coherenceResult = checkCoherence(storeName, record);
            
            if (coherenceResult.isCoherent) {
                results.coherentRecords++;
            } else {
                results.incoherentRecords++;
                results.violations.push({
                    record: getRecordIdentifier(storeName, record),
                    violations: coherenceResult.violations
                });
            }
        }
        
        results.coherenceScore = results.totalRecords > 0 
            ? results.coherentRecords / results.totalRecords
            : 1;
        
        return results;
    }
    
    /**
     * Get a readable identifier for a record
     * @private
     * @param {string} storeName - Store name
     * @param {Object} record - The record
     * @returns {string} Record identifier
     */
    function getRecordIdentifier(storeName, record) {
        const storeConfig = stores[storeName];
        if (!storeConfig) return 'unknown';
        
        const keyValue = record[storeConfig.keyPath];
        return `${storeName}:${keyValue}`;
    }
    
    /**
     * Clear all data in a store
     * @param {string} storeName - Name of the store
     * @returns {Promise} Promise resolving when the store is cleared
     */
    async function clear(storeName) {
        await initialize();
        
        return new Promise((resolve, reject) => {
            const transaction = db.transaction([storeName], 'readwrite');
            const objectStore = transaction.objectStore(storeName);
            const request = objectStore.clear();
            
            request.onsuccess = function() {
                resolve();
            };
            
            request.onerror = function(event) {
                reject(event.target.error);
            };
        });
    }
    
    /**
     * Delete the entire database
     * @returns {Promise} Promise resolving when the database is deleted
     */
    async function deleteDatabase() {
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
    }
    
    // Public API
    return {
        initialize,
        get,
        put,
        remove,
        query,
        getAll,
        clear,
        deleteDatabase,
        checkCoherence,
        checkStoreCoherence,
        stores: Object.keys(stores)
    };
})();

// Export for use in the PrimeOS environment
if (typeof module !== 'undefined' && module.exports) {
    module.exports = PrimeStore;
} else if (typeof window !== 'undefined') {
    window.PrimeStore = PrimeStore;
}