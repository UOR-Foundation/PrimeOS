/**
 * Prime Identity Provider (PIP)
 * Authentication and identity management for PrimeOS
 */

// Dependency on PrimeStore for user data storage
// This would be imported in a real implementation
// const PrimeStore = require('../storage/primestore');

// Prime Identity Provider namespace
const PrimeIdentity = (function() {
    // Current user session
    let currentSession = null;
    
    // Event callbacks
    const eventCallbacks = {
        login: [],
        logout: [],
        sessionChange: []
    };
    
    /**
     * Generate a secure session token
     * @private
     * @returns {string} Random session token
     */
    function generateSessionToken() {
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
    }
    
    /**
     * Initialize the identity provider
     * @returns {Promise} Promise that resolves when initialized
     */
    async function initialize() {
        try {
            // Initialize storage if needed
            if (window.PrimeStore) {
                await window.PrimeStore.initialize();
            }
            
            // Check for existing session
            await checkExistingSession();
            
            return { success: true };
        } catch (error) {
            console.error('Failed to initialize Prime Identity Provider:', error);
            return { success: false, error };
        }
    }
    
    /**
     * Check for an existing session in storage
     * @private
     * @returns {Promise} Promise that resolves with session info
     */
    async function checkExistingSession() {
        try {
            // Try to get session from local storage
            const sessionData = localStorage.getItem('prime_session');
            
            if (sessionData) {
                const session = JSON.parse(sessionData);
                
                // Check if session is still valid
                if (new Date(session.expiresAt) > new Date()) {
                    // Get user data
                    if (window.PrimeStore) {
                        const userData = await window.PrimeStore.get('identity', session.userId);
                        if (userData) {
                            // Set current session
                            currentSession = {
                                ...session,
                                user: userData
                            };
                            
                            // Trigger session change event
                            triggerEvent('sessionChange', { 
                                type: 'restored',
                                session: { ...currentSession, user: { ...userData, passwordHash: undefined } }
                            });
                            
                            return currentSession;
                        }
                    }
                } else {
                    // Session expired, remove it
                    localStorage.removeItem('prime_session');
                }
            }
            
            // No valid session
            currentSession = null;
            return null;
        } catch (error) {
            console.error('Error checking existing session:', error);
            currentSession = null;
            return null;
        }
    }
    
    /**
     * Create a new user account
     * @param {Object} userData - User data
     * @returns {Promise} Promise resolving with the created user
     */
    async function createUser(userData) {
        if (!userData.username || !userData.password) {
            throw new Error('Username and password are required');
        }
        
        // Check if PrimeStore is available
        if (!window.PrimeStore) {
            throw new Error('Storage system not available');
        }
        
        try {
            // Check if username already exists
            const existingUsers = await window.PrimeStore.query('identity', {
                index: 'username',
                value: userData.username
            });
            
            if (existingUsers && existingUsers.length > 0) {
                throw new Error('Username already exists');
            }
            
            // Create a password hash
            // In a real implementation, use a proper password hashing library
            const passwordHash = await hashPassword(userData.password);
            
            // Create user object
            const user = {
                id: 'user_' + Date.now().toString(36) + Math.random().toString(36).substring(2),
                username: userData.username,
                displayName: userData.displayName || userData.username,
                email: userData.email,
                passwordHash,
                created: new Date(),
                lastLogin: null,
                roles: userData.roles || ['user'],
                settings: userData.settings || {}
            };
            
            // Store user data
            await window.PrimeStore.put('identity', user);
            
            // Return user without sensitive data
            const safeUser = { ...user };
            delete safeUser.passwordHash;
            
            return { success: true, user: safeUser };
        } catch (error) {
            console.error('Error creating user:', error);
            return { success: false, error };
        }
    }
    
    /**
     * Hash a password using a secure method
     * @private
     * @param {string} password - Plain text password
     * @returns {Promise<string>} Hashed password
     */
    async function hashPassword(password) {
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
    }
    
    /**
     * Verify a password against a hash
     * @private
     * @param {string} password - Plain text password
     * @param {string} storedHash - Stored hash to compare against
     * @returns {Promise<boolean>} Whether password matches
     */
    async function verifyPassword(password, storedHash) {
        const computedHash = await hashPassword(password);
        return computedHash === storedHash;
    }
    
    /**
     * Log in with username and password
     * @param {string} username - Username
     * @param {string} password - Password
     * @returns {Promise} Promise resolving with login result
     */
    async function login(username, password) {
        if (!username || !password) {
            return { success: false, error: 'Username and password are required' };
        }
        
        // Check if PrimeStore is available
        if (!window.PrimeStore) {
            return { success: false, error: 'Storage system not available' };
        }
        
        try {
            // Find user by username
            const users = await window.PrimeStore.query('identity', {
                index: 'username',
                value: username
            });
            
            if (!users || users.length === 0) {
                return { success: false, error: 'Invalid username or password' };
            }
            
            const user = users[0];
            
            // Verify password
            const passwordMatch = await verifyPassword(password, user.passwordHash);
            
            if (!passwordMatch) {
                return { success: false, error: 'Invalid username or password' };
            }
            
            // Update last login time
            user.lastLogin = new Date();
            await window.PrimeStore.put('identity', user);
            
            // Create session
            const session = createSession(user);
            
            // Store session in local storage
            localStorage.setItem('prime_session', JSON.stringify({
                userId: user.id,
                token: session.token,
                expiresAt: session.expiresAt
            }));
            
            // Set current session
            currentSession = session;
            
            // Create safe user object without password hash
            const safeUser = { ...user };
            delete safeUser.passwordHash;
            
            // Trigger login event
            triggerEvent('login', { user: safeUser });
            triggerEvent('sessionChange', { 
                type: 'login',
                session: { ...session, user: safeUser }
            });
            
            return { 
                success: true,
                user: safeUser,
                token: session.token,
                expiresAt: session.expiresAt
            };
        } catch (error) {
            console.error('Login error:', error);
            return { success: false, error: error.message };
        }
    }
    
    /**
     * Create a new session for a user
     * @private
     * @param {Object} user - User object
     * @returns {Object} Session object
     */
    function createSession(user) {
        // Session expiration (24 hours)
        const expiresAt = new Date();
        expiresAt.setHours(expiresAt.getHours() + 24);
        
        return {
            userId: user.id,
            user,
            token: generateSessionToken(),
            created: new Date(),
            expiresAt,
            permissions: calculatePermissions(user)
        };
    }
    
    /**
     * Calculate user permissions based on roles
     * @private
     * @param {Object} user - User object
     * @returns {Object} Permissions object
     */
    function calculatePermissions(user) {
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
    }
    
    /**
     * Log out the current user
     * @returns {Object} Logout result
     */
    function logout() {
        // Clear session data
        localStorage.removeItem('prime_session');
        
        // Store previous user for event
        const previousUser = currentSession ? { ...currentSession.user } : null;
        if (previousUser) {
            delete previousUser.passwordHash;
        }
        
        // Clear current session
        currentSession = null;
        
        // Trigger logout event
        triggerEvent('logout', { user: previousUser });
        triggerEvent('sessionChange', { type: 'logout', user: previousUser });
        
        return { success: true };
    }
    
    /**
     * Get the current user session
     * @returns {Object|null} Current session or null if not logged in
     */
    function getCurrentSession() {
        if (currentSession) {
            // Create a copy without sensitive data
            const session = { ...currentSession };
            session.user = { ...session.user };
            delete session.user.passwordHash;
            return session;
        }
        return null;
    }
    
    /**
     * Check if user is currently authenticated
     * @returns {boolean} True if authenticated
     */
    function isAuthenticated() {
        return currentSession !== null;
    }
    
    /**
     * Check if current user has a specific permission
     * @param {string} resource - Resource type (files, apps, system)
     * @param {string} action - Action type (read, write, admin, etc.)
     * @returns {boolean} True if user has permission
     */
    function hasPermission(resource, action) {
        if (!currentSession || !currentSession.permissions) {
            return false;
        }
        
        const permissions = currentSession.permissions;
        return permissions[resource] && permissions[resource][action] === true;
    }
    
    /**
     * Register an event callback
     * @param {string} event - Event name
     * @param {Function} callback - Callback function
     * @returns {Function} Function to remove the callback
     */
    function on(event, callback) {
        if (!eventCallbacks[event]) {
            eventCallbacks[event] = [];
        }
        
        eventCallbacks[event].push(callback);
        
        // Return function to remove the callback
        return () => {
            const index = eventCallbacks[event].indexOf(callback);
            if (index !== -1) {
                eventCallbacks[event].splice(index, 1);
            }
        };
    }
    
    /**
     * Trigger an event
     * @private
     * @param {string} event - Event name
     * @param {Object} data - Event data
     */
    function triggerEvent(event, data) {
        if (eventCallbacks[event]) {
            for (const callback of eventCallbacks[event]) {
                try {
                    callback(data);
                } catch (error) {
                    console.error(`Error in ${event} event handler:`, error);
                }
            }
        }
    }
    
    // Public API
    return {
        initialize,
        createUser,
        login,
        logout,
        getCurrentSession,
        isAuthenticated,
        hasPermission,
        on
    };
})();

// Export for use in the PrimeOS environment
if (typeof module !== 'undefined' && module.exports) {
    module.exports = PrimeIdentity;
} else if (typeof window !== 'undefined') {
    window.PrimeIdentity = PrimeIdentity;
}