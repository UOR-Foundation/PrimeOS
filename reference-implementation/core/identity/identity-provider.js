/**
 * Prime Identity Provider (PIP)
 * Authentication and identity management for PrimeOS
 */

// Dependency on PrimeStore for user data storage
// This would be imported in a real implementation
// import PrimeStore from '../storage/primestore.js';

// Prime Identity Provider constructor
function PrimeIdentity() {
    // Current user session
    this.currentSession = null;
    
    // Event callbacks
    this.eventCallbacks = {
        login: [],
        logout: [],
        sessionChange: []
    };
}

/**
 * Generate a secure session token
 * @private
 * @returns {string} Random session token
 */
PrimeIdentity.prototype.generateSessionToken = function() {
    const array = new Uint8Array(32);
    if (window.crypto && window.crypto.getRandomValues) {
        window.crypto.getRandomValues(array);
    } else {
        // Fallback to less secure random numbers
        for (let i = 0; i < array.length; i++) {
            array[i] = Math.floor(Math.random() * 256);
        }
    }
    
    return Array.from(array, byte => byte.toString(16).padStart(2, '0')).join('');
};

/**
 * Initialize the identity provider
 * @returns {Promise} Promise that resolves when initialized
 */
PrimeIdentity.prototype.initialize = async function() {
    try {
        // Check for existing session
        await this.checkSession();
        
        return { success: true };
    } catch (error) {
        console.error('Failed to initialize Prime Identity Provider:', error);
        return { success: false, error };
    }
};

/**
 * Check for an existing session in storage
 * @returns {Promise} Promise that resolves with session info
 */
PrimeIdentity.prototype.checkSession = async function() {
    try {
        console.log('Checking for existing session...');
        
        // For demo purposes, create a guest account if needed
        try {
            // Create a guest user account if it doesn't exist
            if (window.PrimeStore) {
                const identityStore = new window.PrimeStore('identity');
                if (typeof identityStore.initialize === 'function') {
                    await identityStore.initialize();
                }
                
                // Check if we have any users
                const users = await identityStore.query ? await identityStore.query() : [];
                console.log('Existing users count:', users ? users.length : 0);
                
                if (!users || users.length === 0) {
                    console.log('No users found, creating guest account');
                    await this.createUser('guest', 'guest123', {
                        displayName: 'Guest User',
                        email: 'guest@primeos.example',
                        roles: ['user']
                    });
                    console.log('Guest account created (username: guest, password: guest123)');
                }
            }
        } catch (err) {
            console.warn('Failed to create guest account:', err);
        }
        
        // Try to get session from local storage
        const sessionData = localStorage.getItem('prime_session');
        
        if (sessionData) {
            console.log('Found session data in localStorage');
            const session = JSON.parse(sessionData);
            
            // Check if session is still valid
            if (new Date(session.expiresAt) > new Date()) {
                console.log('Session is still valid');
                // Get user data
                if (window.PrimeStore) {
                    const identityStore = new window.PrimeStore('identity');
                    
                    // Initialize the store before using it
                    if (typeof identityStore.initialize === 'function') {
                        await identityStore.initialize();
                    }
                    
                    const userData = await identityStore.get(session.userId);
                    if (userData) {
                        console.log('Found user data for session:', userData.username);
                        // Set current session
                        this.currentSession = {
                            ...session,
                            user: userData
                        };
                        
                        // Trigger session change event
                        this.triggerEvent('sessionChange', { 
                            type: 'restored',
                            session: { ...this.currentSession, user: { ...userData, passwordHash: undefined } }
                        });
                        
                        return true;
                    } else {
                        console.log('User data not found for session userId:', session.userId);
                    }
                } else {
                    console.warn('PrimeStore not available for session check');
                }
            } else {
                console.log('Session has expired');
                // Session expired, remove it
                localStorage.removeItem('prime_session');
            }
        } else {
            console.log('No session data found in localStorage');
        }
        
        // No valid session
        this.currentSession = null;
        console.log('No valid session found, returning false');
        return false;
    } catch (error) {
        console.error('Error checking existing session:', error);
        this.currentSession = null;
        return false;
    }
};

/**
 * Create a new user account
 * @param {string} username - Username
 * @param {string} password - Password
 * @param {Object} userData - Additional user data
 * @returns {Promise} Promise resolving with the created user
 */
PrimeIdentity.prototype.createUser = async function(username, password, userData = {}) {
    if (!username || !password) {
        throw new Error('Username and password are required');
    }
    
    // Check if PrimeStore is available
    if (!window.PrimeStore) {
        throw new Error('Storage system not available');
    }
    
    try {
        const identityStore = new window.PrimeStore('identity');
        
        // Initialize the store before using it
        if (typeof identityStore.initialize === 'function') {
            await identityStore.initialize();
        }
        
        // Query for existing users by username
        const existingUsers = await identityStore.query({
            index: 'username',
            value: username
        });
        
        if (existingUsers && existingUsers.length > 0) {
            throw new Error('Username already exists');
        }
        
        // Create a password hash
        // In a real implementation, use a proper password hashing library
        const passwordHash = await this.hashPassword(password);
        
        // Create user object
        const user = {
            id: 'user_' + Date.now().toString(36) + Math.random().toString(36).substring(2),
            username: username,
            displayName: userData.displayName || username,
            email: userData.email,
            passwordHash,
            created: new Date(),
            lastLogin: null,
            roles: userData.roles || ['user'],
            settings: userData.settings || {}
        };
        
        // Store user data
        await identityStore.put(user);
        
        // Return user without sensitive data
        const safeUser = { ...user };
        delete safeUser.passwordHash;
        
        return true;
    } catch (error) {
        console.error('Error creating user:', error);
        return false;
    }
};

/**
 * Hash a password using a secure method
 * @private
 * @param {string} password - Plain text password
 * @returns {Promise<string>} Hashed password
 */
PrimeIdentity.prototype.hashPassword = async function(password) {
    // In a real implementation, use a secure password hashing library
    // This is a placeholder implementation using SHA-256
    if (window.crypto && window.crypto.subtle) {
        try {
            const encoder = new TextEncoder();
            const data = encoder.encode(password);
            const hashBuffer = await window.crypto.subtle.digest('SHA-256', data);
            
            // Convert hash to hex string
            return Array.from(new Uint8Array(hashBuffer))
                .map(b => b.toString(16).padStart(2, '0'))
                .join('');
        } catch (error) {
            console.error('Error hashing password:', error);
            // Fallback to insecure hash (not for production)
            return btoa(password + 'prime_salt');
        }
    } else {
        // Fallback to insecure hash (not for production)
        return btoa(password + 'prime_salt');
    }
};

/**
 * Verify a password against a hash
 * @private
 * @param {string} password - Plain text password
 * @param {string} storedHash - Stored hash to compare against
 * @returns {Promise<boolean>} Whether password matches
 */
PrimeIdentity.prototype.verifyPassword = async function(password, storedHash) {
    const computedHash = await this.hashPassword(password);
    return computedHash === storedHash;
};

/**
 * Log in with username and password
 * @param {string} username - Username
 * @param {string} password - Password
 * @returns {Promise} Promise resolving with login result
 */
PrimeIdentity.prototype.login = async function(username, password) {
    if (!username || !password) {
        return false;
    }
    
    // Check if PrimeStore is available
    if (!window.PrimeStore) {
        return false;
    }
    
    try {
        const identityStore = new window.PrimeStore('identity');
        
        // Initialize the store before using it
        if (typeof identityStore.initialize === 'function') {
            await identityStore.initialize();
        }
        
        // Find user by username
        const users = await identityStore.query({
            index: 'username',
            value: username
        });
        
        if (!users || users.length === 0) {
            return false;
        }
        
        const user = users[0];
        
        // Verify password
        const passwordMatch = await this.verifyPassword(password, user.passwordHash);
        
        if (!passwordMatch) {
            return false;
        }
        
        // Update last login time
        user.lastLogin = new Date();
        await identityStore.put(user);
        
        // Create session
        const session = this.createSession(user);
        
        // Store session in local storage
        localStorage.setItem('prime_session', JSON.stringify({
            userId: user.id,
            token: session.token,
            expiresAt: session.expiresAt
        }));
        
        // Set current session
        this.currentSession = session;
        
        // Create safe user object without password hash
        const safeUser = { ...user };
        delete safeUser.passwordHash;
        
        // Trigger login event
        this.triggerEvent('login', { user: safeUser });
        this.triggerEvent('sessionChange', { 
            type: 'login',
            session: { ...session, user: safeUser }
        });
        
        return true;
    } catch (error) {
        console.error('Login error:', error);
        return false;
    }
};

/**
 * Create a new session for a user
 * @private
 * @param {Object} user - User object
 * @returns {Object} Session object
 */
PrimeIdentity.prototype.createSession = function(user) {
    // Session expiration (24 hours)
    const expiresAt = new Date();
    expiresAt.setHours(expiresAt.getHours() + 24);
    
    return {
        userId: user.id,
        user,
        token: this.generateSessionToken(),
        created: new Date(),
        expiresAt,
        permissions: this.calculatePermissions(user)
    };
};

/**
 * Calculate user permissions based on roles
 * @private
 * @param {Object} user - User object
 * @returns {Object} Permissions object
 */
PrimeIdentity.prototype.calculatePermissions = function(user) {
    const permissions = {
        files: { read: false, write: false, admin: false },
        apps: { run: false, install: false, admin: false },
        system: { access: false, admin: false }
    };
    
    // Apply role-based permissions
    (user.roles || []).forEach(role => {
        switch (role) {
            case 'user':
                permissions.files.read = true;
                permissions.files.write = true;
                permissions.apps.run = true;
                break;
            case 'developer':
                permissions.files.read = true;
                permissions.files.write = true;
                permissions.apps.run = true;
                permissions.apps.install = true;
                break;
            case 'admin':
                permissions.files.read = true;
                permissions.files.write = true;
                permissions.files.admin = true;
                permissions.apps.run = true;
                permissions.apps.install = true;
                permissions.apps.admin = true;
                permissions.system.access = true;
                permissions.system.admin = true;
                break;
        }
    });
    
    return permissions;
};

/**
 * Log out the current user
 * @returns {Object} Logout result
 */
PrimeIdentity.prototype.logout = function() {
    // Clear session data
    localStorage.removeItem('prime_session');
    
    // Store previous user for event
    const previousUser = this.currentSession ? { ...this.currentSession.user } : null;
    if (previousUser) {
        delete previousUser.passwordHash;
    }
    
    // Clear current session
    this.currentSession = null;
    
    // Trigger logout event
    this.triggerEvent('logout', { user: previousUser });
    this.triggerEvent('sessionChange', { type: 'logout', user: previousUser });
    
    return true;
};

/**
 * Get the current user
 * @returns {Object|null} Current user or null if not logged in
 */
PrimeIdentity.prototype.getCurrentUser = function() {
    if (this.currentSession && this.currentSession.user) {
        // Create a copy without sensitive data
        const user = { ...this.currentSession.user };
        delete user.passwordHash;
        return user;
    }
    return null;
};

/**
 * Check if user is currently authenticated
 * @returns {boolean} True if authenticated
 */
PrimeIdentity.prototype.isAuthenticated = function() {
    return this.currentSession !== null;
};

/**
 * Check if current user has a specific permission
 * @param {string} resource - Resource type (files, apps, system)
 * @param {string} action - Action type (read, write, admin, etc.)
 * @returns {boolean} True if user has permission
 */
PrimeIdentity.prototype.hasPermission = function(resource, action) {
    if (!this.currentSession || !this.currentSession.permissions) {
        return false;
    }
    
    const permissions = this.currentSession.permissions;
    return permissions[resource] && permissions[resource][action] === true;
};

/**
 * Register an event callback
 * @param {string} event - Event name
 * @param {Function} callback - Callback function
 * @returns {Function} Function to remove the callback
 */
PrimeIdentity.prototype.on = function(event, callback) {
    if (!this.eventCallbacks[event]) {
        this.eventCallbacks[event] = [];
    }
    
    this.eventCallbacks[event].push(callback);
    
    // Return function to remove the callback
    return () => {
        const index = this.eventCallbacks[event].indexOf(callback);
        if (index !== -1) {
            this.eventCallbacks[event].splice(index, 1);
        }
    };
};

/**
 * Trigger an event
 * @private
 * @param {string} event - Event name
 * @param {Object} data - Event data
 */
PrimeIdentity.prototype.triggerEvent = function(event, data) {
    if (this.eventCallbacks[event]) {
        for (const callback of this.eventCallbacks[event]) {
            try {
                callback(data);
            } catch (error) {
                console.error(`Error in ${event} event handler:`, error);
            }
        }
    }
};

// Export for use in the PrimeOS environment
if (typeof window !== 'undefined') {
    window.PrimeIdentity = PrimeIdentity;
}