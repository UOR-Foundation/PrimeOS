/**
 * PrimeOS Reference Implementation - Identity Provider Tests
 * 
 * Tests for the PrimeIdentity module, which handles authentication, session management,
 * and user identity functions.
 */

// Import test utilities
const { describe, it, expect, beforeEach } = require('@jest/globals');

// Create our own mock since the real module uses ES modules
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

// Implement all necessary methods for testing - full implementation
PrimeIdentity.prototype.checkSession = async function() {
  try {
    // Try to get session from local storage
    const sessionData = localStorage.getItem('prime_session');
    
    if (sessionData) {
      const session = JSON.parse(sessionData);
      
      // Check if session is still valid
      if (new Date(session.expiresAt) > new Date()) {
        // Get user data
        if (window.PrimeStore) {
          const identityStore = window.PrimeStore('identity');
          
          if (typeof identityStore.initialize === 'function') {
            await identityStore.initialize();
          }
          
          const userData = await identityStore.get(session.userId);
          if (userData) {
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
          }
        }
      } else {
        // Session expired, remove it
        localStorage.removeItem('prime_session');
      }
    }
    
    // No valid session
    this.currentSession = null;
    return false;
  } catch (error) {
    console.error('Error checking existing session:', error);
    this.currentSession = null;
    return false;
  }
};

/**
 * Create a new user account
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
    const identityStore = window.PrimeStore('identity');
    
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
    
    return true;
  } catch (error) {
    console.error('Error creating user:', error);
    return false;
  }
};

/**
 * Verify a password against a hash
 */
PrimeIdentity.prototype.verifyPassword = async function(password, storedHash) {
  const computedHash = await this.hashPassword(password);
  return computedHash === storedHash;
};

/**
 * Log in with username and password
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
    const identityStore = window.PrimeStore('identity');
    
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
 * Calculate permissions based on roles
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
 */
PrimeIdentity.prototype.isAuthenticated = function() {
  return this.currentSession !== null;
};

/**
 * Check if current user has a specific permission
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

// Mock localStorage
global.localStorage = {
  store: {},
  getItem(key) {
    return this.store[key];
  },
  setItem(key, value) {
    this.store[key] = value;
  },
  removeItem(key) {
    delete this.store[key];
  },
  clear() {
    this.store = {};
  }
};

// Mock the window.crypto for secure token generation
global.window = {
  crypto: {
    getRandomValues: jest.fn((array) => {
      // Fill with deterministic values for testing
      for (let i = 0; i < array.length; i++) {
        array[i] = (i % 256);
      }
      return array;
    }),
    subtle: {
      digest: jest.fn().mockResolvedValue(new Uint8Array([1, 2, 3, 4, 5]).buffer)
    }
  },
  PrimeStore: null
};

// Mock the PrimeStore implementation
const mockPrimeStore = function(storeName) {
  return {
    storeName,
    initialize: jest.fn().mockResolvedValue(true),
    get: jest.fn(),
    put: jest.fn(),
    query: jest.fn(),
    saveAll: jest.fn()
  };
};

// Tests
describe('PrimeIdentity', () => {
  let identity;
  
  beforeEach(() => {
    // Clear mock storage before each test
    localStorage.clear();
    jest.clearAllMocks();
    
    // Configure PrimeStore mock for window global
    window.PrimeStore = mockPrimeStore;
    
    // Create new instance for each test
    identity = new PrimeIdentity();
  });
  
  describe('Session Management', () => {
    it('should initialize without a session', async () => {
      await identity.initialize();
      expect(identity.currentSession).toBeNull();
    });
    
    it('should restore a valid session from localStorage', async () => {
      // Create a mock session
      const mockSession = {
        userId: 'user-123',
        token: 'test-token',
        expiresAt: new Date(Date.now() + 3600000).toISOString() // 1 hour in future
      };
      
      // Store in localStorage
      localStorage.setItem('prime_session', JSON.stringify(mockSession));
      
      // Mock user data retrieval
      const mockUser = { id: 'user-123', username: 'testuser' };
      const mockStore = mockPrimeStore('identity');
      mockStore.get.mockResolvedValue(mockUser);
      window.PrimeStore = jest.fn().mockReturnValue(mockStore);
      
      // Check session
      const result = await identity.checkSession();
      
      // Session should be restored
      expect(result).toBe(true);
      expect(identity.currentSession).not.toBeNull();
      expect(identity.currentSession.userId).toBe('user-123');
      expect(identity.currentSession.user).toEqual(mockUser);
    });
    
    it('should reject expired sessions', async () => {
      // Create an expired session
      const mockSession = {
        userId: 'user-123',
        token: 'test-token',
        expiresAt: new Date(Date.now() - 3600000).toISOString() // 1 hour in past
      };
      
      // Store in localStorage
      localStorage.setItem('prime_session', JSON.stringify(mockSession));
      
      // Check session
      const result = await identity.checkSession();
      
      // Session should be rejected
      expect(result).toBe(false);
      expect(identity.currentSession).toBeNull();
      
      // Session should be removed from localStorage
      expect(localStorage.getItem('prime_session')).toBeNull();
    });
  });
  
  describe('User Authentication', () => {
    it('should create a user successfully', async () => {
      // Mock user store
      const mockStore = mockPrimeStore('identity');
      mockStore.query.mockResolvedValue([]);
      mockStore.put.mockResolvedValue(true);
      window.PrimeStore = jest.fn().mockReturnValue(mockStore);
      
      // Create user
      const result = await identity.createUser('newuser', 'password123');
      
      // Should succeed
      expect(result).toBe(true);
      
      // Should call store methods
      expect(mockStore.initialize).toHaveBeenCalled();
      expect(mockStore.query).toHaveBeenCalledWith({
        index: 'username',
        value: 'newuser'
      });
      expect(mockStore.put).toHaveBeenCalled();
      
      // Should create user with correct properties
      const userCreated = mockStore.put.mock.calls[0][0];
      expect(userCreated.username).toBe('newuser');
      expect(userCreated.passwordHash).toBeDefined();
      expect(userCreated.created instanceof Date).toBe(true);
    });
    
    it('should reject creation of duplicate usernames', async () => {
      // Mock user store with existing user
      const mockStore = mockPrimeStore('identity');
      mockStore.query.mockResolvedValue([{ id: 'existing', username: 'newuser' }]);
      window.PrimeStore = jest.fn().mockReturnValue(mockStore);
      
      // Try to create user with same username
      const result = await identity.createUser('newuser', 'password123');
      
      // Should fail
      expect(result).toBe(false);
      
      // Should not call put to store
      expect(mockStore.put).not.toHaveBeenCalled();
    });
    
    it('should login successfully with correct credentials', async () => {
      // Mock user store with a user
      const mockUser = {
        id: 'user-123',
        username: 'testuser',
        passwordHash: await identity.hashPassword('correctpassword')
      };
      
      const mockStore = mockPrimeStore('identity');
      mockStore.query.mockResolvedValue([mockUser]);
      window.PrimeStore = jest.fn().mockReturnValue(mockStore);
      
      // Login with correct password
      const result = await identity.login('testuser', 'correctpassword');
      
      // Should succeed
      expect(result).toBe(true);
      
      // Should set current session
      expect(identity.currentSession).not.toBeNull();
      expect(identity.currentSession.userId).toBe('user-123');
      
      // Should update last login time
      expect(mockStore.put).toHaveBeenCalled();
      
      // Should store session in localStorage
      const storedSession = JSON.parse(localStorage.getItem('prime_session'));
      expect(storedSession).toBeDefined();
      expect(storedSession.userId).toBe('user-123');
    });
    
    it('should reject login with incorrect password', async () => {
      // Mock user store with a user
      const mockUser = {
        id: 'user-123',
        username: 'testuser',
        passwordHash: await identity.hashPassword('correctpassword')
      };
      
      const mockStore = mockPrimeStore('identity');
      mockStore.query.mockResolvedValue([mockUser]);
      window.PrimeStore = jest.fn().mockReturnValue(mockStore);
      
      // Login with wrong password
      const result = await identity.login('testuser', 'wrongpassword');
      
      // Should fail
      expect(result).toBe(false);
      
      // Should not set current session
      expect(identity.currentSession).toBeNull();
      
      // Should not update last login time
      expect(mockStore.put).not.toHaveBeenCalled();
      
      // Should not store session in localStorage
      const storedSession = localStorage.getItem('prime_session');
      expect(storedSession).toBeNull();
    });
    
    it('should logout successfully', async () => {
      // Set up a current session
      identity.currentSession = {
        userId: 'user-123',
        user: { id: 'user-123', username: 'testuser' },
        token: 'test-token'
      };
      
      // Store in localStorage
      localStorage.setItem('prime_session', JSON.stringify({
        userId: 'user-123',
        token: 'test-token',
        expiresAt: new Date(Date.now() + 3600000).toISOString()
      }));
      
      // Logout
      const result = identity.logout();
      
      // Should succeed
      expect(result).toBe(true);
      
      // Should clear current session
      expect(identity.currentSession).toBeNull();
      
      // Should remove session from localStorage
      expect(localStorage.getItem('prime_session')).toBeNull();
    });
  });
  
  describe('Permissions', () => {
    it('should calculate permissions based on user roles', () => {
      // Create users with different roles
      const regularUser = { id: 'user1', roles: ['user'] };
      const developerUser = { id: 'user2', roles: ['user', 'developer'] };
      const adminUser = { id: 'user3', roles: ['user', 'admin'] };
      
      // Calculate permissions
      const regularPerms = identity.calculatePermissions(regularUser);
      const developerPerms = identity.calculatePermissions(developerUser);
      const adminPerms = identity.calculatePermissions(adminUser);
      
      // Regular user should have basic permissions
      expect(regularPerms.files.read).toBe(true);
      expect(regularPerms.files.write).toBe(true);
      expect(regularPerms.apps.run).toBe(true);
      expect(regularPerms.apps.install).toBe(false);
      expect(regularPerms.system.admin).toBe(false);
      
      // Developer should have additional permissions
      expect(developerPerms.files.read).toBe(true);
      expect(developerPerms.files.write).toBe(true);
      expect(developerPerms.apps.run).toBe(true);
      expect(developerPerms.apps.install).toBe(true);
      expect(developerPerms.system.admin).toBe(false);
      
      // Admin should have all permissions
      expect(adminPerms.files.read).toBe(true);
      expect(adminPerms.files.write).toBe(true);
      expect(adminPerms.files.admin).toBe(true);
      expect(adminPerms.apps.run).toBe(true);
      expect(adminPerms.apps.install).toBe(true);
      expect(adminPerms.apps.admin).toBe(true);
      expect(adminPerms.system.access).toBe(true);
      expect(adminPerms.system.admin).toBe(true);
    });
    
    it('should check permissions correctly', () => {
      // Set up a session with permissions
      identity.currentSession = {
        userId: 'user-123',
        user: { id: 'user-123', username: 'testuser', roles: ['user'] },
        permissions: {
          files: { read: true, write: true, admin: false },
          apps: { run: true, install: false, admin: false },
          system: { access: false, admin: false }
        }
      };
      
      // Check permissions
      expect(identity.hasPermission('files', 'read')).toBe(true);
      expect(identity.hasPermission('files', 'admin')).toBe(false);
      expect(identity.hasPermission('apps', 'install')).toBe(false);
      expect(identity.hasPermission('system', 'admin')).toBe(false);
    });
    
    it('should deny all permissions when not authenticated', () => {
      // No session
      identity.currentSession = null;
      
      // All permissions should be denied
      expect(identity.hasPermission('files', 'read')).toBe(false);
      expect(identity.hasPermission('apps', 'run')).toBe(false);
      expect(identity.hasPermission('system', 'access')).toBe(false);
    });
  });
  
  describe('Events', () => {
    it('should register and trigger event callbacks', () => {
      // Create mock callbacks
      const loginCallback = jest.fn();
      const logoutCallback = jest.fn();
      
      // Register callbacks
      identity.on('login', loginCallback);
      identity.on('logout', logoutCallback);
      
      // Trigger events
      identity.triggerEvent('login', { user: { id: 'user1' } });
      identity.triggerEvent('logout', { user: { id: 'user1' } });
      
      // Callbacks should be called
      expect(loginCallback).toHaveBeenCalled();
      expect(logoutCallback).toHaveBeenCalled();
      
      // Should be called with correct data
      expect(loginCallback).toHaveBeenCalledWith({ user: { id: 'user1' } });
      expect(logoutCallback).toHaveBeenCalledWith({ user: { id: 'user1' } });
    });
    
    it('should unregister events when callback is removed', () => {
      // Create mock callback
      const loginCallback = jest.fn();
      
      // Register callback and get unsubscribe function
      const unsubscribe = identity.on('login', loginCallback);
      
      // Unsubscribe
      unsubscribe();
      
      // Trigger event
      identity.triggerEvent('login', { user: { id: 'user1' } });
      
      // Callback should not be called
      expect(loginCallback).not.toHaveBeenCalled();
    });
  });
});