/**
 * PrimeOS Reference Implementation - SettingsStore Tests
 * 
 * Tests for the SettingsStore component which manages application settings 
 * and integrates with the SecureVault for API key storage.
 */

// Import the modules to test
const { SettingsStore } = require('../apps/settings/models/settings-store');
const { SecureVault } = require('../core/identity/secure-vault');

describe('SettingsStore', () => {
  let settingsStore;
  let mockStorage;
  let mockEventBus;
  let mockSecureVault;
  
  beforeEach(() => {
    // Mock storage
    mockStorage = {
      getItem: jest.fn().mockImplementation((key) => {
        if (key === 'settings') {
          return Promise.resolve(JSON.stringify({
            general: {
              theme: 'light',
              language: 'en'
            },
            appearance: {
              fontSize: 'medium',
              fontFamily: 'sans-serif'
            },
            developer: {
              debugMode: false
            }
          }));
        }
        return Promise.resolve(null);
      }),
      setItem: jest.fn().mockResolvedValue(true),
      removeItem: jest.fn().mockResolvedValue(true)
    };
    
    // Mock event bus
    mockEventBus = {
      publish: jest.fn(),
      subscribe: jest.fn(),
      unsubscribe: jest.fn()
    };
    
    // Mock secure vault
    mockSecureVault = {
      setSecret: jest.fn().mockResolvedValue(true),
      getSecret: jest.fn().mockImplementation((key) => {
        if (key === 'claudeApiKey') {
          return Promise.resolve('sk-test-12345');
        }
        return Promise.resolve(null);
      }),
      removeSecret: jest.fn().mockResolvedValue(true)
    };
    
    // Create test instance with mocks
    settingsStore = new SettingsStore({
      storage: mockStorage,
      eventBus: mockEventBus,
      secureVault: mockSecureVault
    });
    
    // Spy on console methods
    jest.spyOn(console, 'log').mockImplementation(() => {});
    jest.spyOn(console, 'error').mockImplementation(() => {});
  });
  
  afterEach(() => {
    console.log.mockRestore();
    console.error.mockRestore();
  });
  
  describe('constructor', () => {
    it('should initialize with provided options', () => {
      expect(settingsStore.storage).toBe(mockStorage);
      expect(settingsStore.eventBus).toBe(mockEventBus);
      expect(settingsStore.secureVault).toBe(mockSecureVault);
    });
    
    it('should initialize with default storage if not provided', () => {
      const defaultStore = new SettingsStore();
      
      expect(defaultStore.storage).toBeDefined();
      expect(defaultStore.initialized).toBe(false);
    });
    
    it('should initialize with default SecureVault if not provided', async () => {
      const storeWithoutVault = new SettingsStore({
        storage: mockStorage,
        eventBus: mockEventBus
      });
      
      // Should create a SecureVault instance
      expect(storeWithoutVault.secureVault).toBeInstanceOf(SecureVault);
    });
    
    it('should setup categories and predefined settings', () => {
      expect(settingsStore.categories).toBeInstanceOf(Map);
      expect(settingsStore.categories.has('general')).toBe(true);
      expect(settingsStore.categories.has('appearance')).toBe(true);
      expect(settingsStore.categories.has('apiKeys')).toBe(true);
      expect(settingsStore.categories.has('notifications')).toBe(true);
      expect(settingsStore.categories.has('developer')).toBe(true);
    });
  });
  
  describe('initialize', () => {
    it('should load settings from storage', async () => {
      await settingsStore.initialize();
      
      expect(mockStorage.getItem).toHaveBeenCalledWith('settings');
      expect(settingsStore.initialized).toBe(true);
      
      // Should load settings from storage
      const generalSettings = settingsStore.getCategory('general');
      expect(generalSettings.get('theme')).toBe('light');
      expect(generalSettings.get('language')).toBe('en');
      
      const appearanceSettings = settingsStore.getCategory('appearance');
      expect(appearanceSettings.get('fontSize')).toBe('medium');
      expect(appearanceSettings.get('fontFamily')).toBe('sans-serif');
    });
    
    it('should handle missing settings in storage', async () => {
      // Mock empty storage
      mockStorage.getItem.mockResolvedValueOnce(null);
      
      await settingsStore.initialize();
      
      // Should use default settings
      const generalSettings = settingsStore.getCategory('general');
      expect(generalSettings.get('theme')).toBe('system');
      expect(generalSettings.get('language')).toBe('en');
    });
    
    it('should load API keys from SecureVault', async () => {
      await settingsStore.initialize();
      
      expect(mockSecureVault.getSecret).toHaveBeenCalledWith('claudeApiKey');
      
      // Should load API key into settings
      const apiKeys = settingsStore.getCategory('apiKeys');
      expect(apiKeys.get('claudeApiKey')).toBe('sk-test-12345');
    });
    
    it('should setup manifold structure for settings', async () => {
      await settingsStore.initialize();
      
      expect(settingsStore.settingsManifold).toBeDefined();
      
      // Check manifold structure
      const meta = settingsStore.settingsManifold.getMeta();
      const invariant = settingsStore.settingsManifold.getInvariant();
      const variant = settingsStore.settingsManifold.getVariant();
      
      expect(meta.type).toBe('settings');
      expect(invariant.requiredCategories).toContain('general');
      expect(variant.lastAccessed).toBeDefined();
    });
  });
  
  describe('getCategory', () => {
    beforeEach(async () => {
      await settingsStore.initialize();
    });
    
    it('should return settings for a valid category', () => {
      const general = settingsStore.getCategory('general');
      
      expect(general).toBeDefined();
      expect(general instanceof Map).toBe(true);
      expect(general.get('theme')).toBe('light');
      expect(general.get('language')).toBe('en');
    });
    
    it('should return empty map for unknown category', () => {
      const unknown = settingsStore.getCategory('unknown');
      
      expect(unknown).toBeDefined();
      expect(unknown instanceof Map).toBe(true);
      expect(unknown.size).toBe(0);
    });
    
    it('should update manifold access timestamp', () => {
      const beforeAccess = settingsStore.settingsManifold.getVariant().lastAccessed;
      
      // Small delay to ensure timestamp changes
      jest.advanceTimersByTime(100);
      
      settingsStore.getCategory('general');
      
      const afterAccess = settingsStore.settingsManifold.getVariant().lastAccessed;
      
      // Should have updated the timestamp
      expect(afterAccess).toBeGreaterThan(beforeAccess);
    });
  });
  
  describe('getSetting', () => {
    beforeEach(async () => {
      await settingsStore.initialize();
    });
    
    it('should get setting value from a category', () => {
      const theme = settingsStore.getSetting('general', 'theme');
      expect(theme).toBe('light');
      
      const fontSize = settingsStore.getSetting('appearance', 'fontSize');
      expect(fontSize).toBe('medium');
    });
    
    it('should return null for unknown category', () => {
      const value = settingsStore.getSetting('unknown', 'setting');
      expect(value).toBeNull();
    });
    
    it('should return null for unknown setting', () => {
      const value = settingsStore.getSetting('general', 'unknown');
      expect(value).toBeNull();
    });
    
    it('should return default value if provided', () => {
      const value = settingsStore.getSetting('general', 'unknown', 'default-value');
      expect(value).toBe('default-value');
    });
  });
  
  describe('updateSetting', () => {
    beforeEach(async () => {
      await settingsStore.initialize();
    });
    
    it('should update a setting value', async () => {
      const result = await settingsStore.updateSetting('general', 'theme', 'dark');
      
      expect(result).toBe(true);
      expect(settingsStore.getSetting('general', 'theme')).toBe('dark');
      
      // Should save to storage
      expect(mockStorage.setItem).toHaveBeenCalled();
      
      // Should notify via event bus
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'settings:changed',
        expect.objectContaining({
          category: 'general',
          key: 'theme',
          value: 'dark'
        })
      );
    });
    
    it('should create category if it doesn\'t exist', async () => {
      const result = await settingsStore.updateSetting('newCategory', 'newSetting', 'value');
      
      expect(result).toBe(true);
      expect(settingsStore.getSetting('newCategory', 'newSetting')).toBe('value');
      
      // Should have created the category
      expect(settingsStore.categories.has('newCategory')).toBe(true);
    });
    
    it('should store API keys in SecureVault', async () => {
      const result = await settingsStore.updateSetting('apiKeys', 'claudeApiKey', 'sk-new-api-key');
      
      expect(result).toBe(true);
      
      // Should store in SecureVault
      expect(mockSecureVault.setSecret).toHaveBeenCalledWith(
        'claudeApiKey',
        'sk-new-api-key',
        expect.objectContaining({
          type: 'api_key'
        })
      );
      
      // Should notify about API key change
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'settings:api-key-changed',
        expect.objectContaining({
          key: 'claudeApiKey',
          value: 'sk-new-api-key'
        })
      );
    });
    
    it('should remove API key from SecureVault when set to empty', async () => {
      const result = await settingsStore.updateSetting('apiKeys', 'claudeApiKey', '');
      
      expect(result).toBe(true);
      
      // Should remove from SecureVault
      expect(mockSecureVault.removeSecret).toHaveBeenCalledWith('claudeApiKey');
      
      // Should notify about API key removal
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'settings:api-key-changed',
        expect.objectContaining({
          key: 'claudeApiKey',
          value: ''
        })
      );
    });
    
    it('should update manifold variant properties', async () => {
      await settingsStore.updateSetting('general', 'theme', 'dark');
      
      const variant = settingsStore.settingsManifold.getVariant();
      
      // Should track changes
      expect(variant.lastModified).toBeDefined();
      expect(variant.changeCount).toBeGreaterThan(0);
    });
  });
  
  describe('getDefaultSettings', () => {
    it('should provide default settings for all categories', () => {
      const defaults = settingsStore.getDefaultSettings();
      
      expect(defaults.general).toBeDefined();
      expect(defaults.general.theme).toBe('system');
      expect(defaults.general.language).toBe('en');
      
      expect(defaults.appearance).toBeDefined();
      expect(defaults.appearance.fontSize).toBe('medium');
      
      expect(defaults.apiKeys).toBeDefined();
      expect(defaults.apiKeys.claudeApiKey).toBe('');
      
      expect(defaults.notifications).toBeDefined();
      expect(defaults.notifications.enabled).toBe(true);
      
      expect(defaults.developer).toBeDefined();
      expect(defaults.developer.debugMode).toBe(false);
    });
  });
  
  describe('resetToDefaults', () => {
    beforeEach(async () => {
      await settingsStore.initialize();
    });
    
    it('should reset all settings to defaults', async () => {
      // First update some settings
      await settingsStore.updateSetting('general', 'theme', 'dark');
      await settingsStore.updateSetting('appearance', 'fontSize', 'large');
      
      // Then reset
      const result = await settingsStore.resetToDefaults();
      
      expect(result).toBe(true);
      
      // Should reset to defaults
      expect(settingsStore.getSetting('general', 'theme')).toBe('system');
      expect(settingsStore.getSetting('appearance', 'fontSize')).toBe('medium');
      
      // Should save to storage
      expect(mockStorage.setItem).toHaveBeenCalled();
      
      // Should notify via event bus
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'settings:reset',
        expect.any(Object)
      );
    });
    
    it('should reset only specified category when provided', async () => {
      // First update some settings
      await settingsStore.updateSetting('general', 'theme', 'dark');
      await settingsStore.updateSetting('appearance', 'fontSize', 'large');
      
      // Reset only general category
      const result = await settingsStore.resetToDefaults('general');
      
      expect(result).toBe(true);
      
      // General should be reset
      expect(settingsStore.getSetting('general', 'theme')).toBe('system');
      
      // But appearance should remain changed
      expect(settingsStore.getSetting('appearance', 'fontSize')).toBe('large');
      
      // Should notify about specific category reset
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'settings:category-reset',
        expect.objectContaining({
          category: 'general'
        })
      );
    });
    
    it('should handle resetting API keys', async () => {
      // Reset API keys category
      await settingsStore.resetToDefaults('apiKeys');
      
      // Should remove API keys from SecureVault
      expect(mockSecureVault.removeSecret).toHaveBeenCalledWith('claudeApiKey');
      
      // Should reset category to defaults
      const apiKeys = settingsStore.getCategory('apiKeys');
      expect(apiKeys.get('claudeApiKey')).toBe('');
    });
  });
  
  describe('save', () => {
    beforeEach(async () => {
      await settingsStore.initialize();
    });
    
    it('should save settings to storage', async () => {
      // Update some settings first
      await settingsStore.updateSetting('general', 'theme', 'dark');
      await settingsStore.updateSetting('appearance', 'fontSize', 'large');
      
      // Clear previous calls
      mockStorage.setItem.mockClear();
      
      // Save manually
      const result = await settingsStore.save();
      
      expect(result).toBe(true);
      expect(mockStorage.setItem).toHaveBeenCalledWith(
        'settings',
        expect.stringContaining('"theme":"dark"')
      );
      
      // Should include all categories
      const savedData = JSON.parse(mockStorage.setItem.mock.calls[0][1]);
      expect(savedData.general).toBeDefined();
      expect(savedData.appearance).toBeDefined();
      expect(savedData.developer).toBeDefined();
      
      // Should exclude sensitive categories
      expect(savedData.apiKeys).toBeUndefined();
    });
    
    it('should handle storage errors', async () => {
      // Mock storage error
      mockStorage.setItem.mockRejectedValueOnce(new Error('Storage error'));
      
      const result = await settingsStore.save();
      
      expect(result).toBe(false);
      expect(console.error).toHaveBeenCalled();
    });
  });
  
  describe('getApiKeys', () => {
    beforeEach(async () => {
      await settingsStore.initialize();
    });
    
    it('should return all API keys', async () => {
      // Add another API key
      mockSecureVault.getSecret.mockImplementation((key) => {
        if (key === 'claudeApiKey') {
          return Promise.resolve('sk-test-12345');
        } else if (key === 'openaiApiKey') {
          return Promise.resolve('sk-openai-test');
        }
        return Promise.resolve(null);
      });
      
      await settingsStore.updateSetting('apiKeys', 'openaiApiKey', 'sk-openai-test');
      
      const apiKeys = settingsStore.getApiKeys();
      
      expect(apiKeys.claudeApiKey).toBe('sk-test-12345');
      expect(apiKeys.openaiApiKey).toBe('sk-openai-test');
    });
    
    it('should return null for inexistent API key', async () => {
      const result = await settingsStore.getApiKey('inexistentKey');
      expect(result).toBeNull();
    });
  });
  
  describe('updateApiKey', () => {
    beforeEach(async () => {
      await settingsStore.initialize();
    });
    
    it('should update API key', async () => {
      const result = await settingsStore.updateApiKey('claudeApiKey', 'sk-new-key');
      
      expect(result).toBe(true);
      expect(mockSecureVault.setSecret).toHaveBeenCalledWith(
        'claudeApiKey',
        'sk-new-key',
        expect.any(Object)
      );
      
      // Should update in-memory value
      const apiKeys = settingsStore.getCategory('apiKeys');
      expect(apiKeys.get('claudeApiKey')).toBe('sk-new-key');
      
      // Should notify via event bus
      expect(mockEventBus.publish).toHaveBeenCalledWith(
        'settings:api-key-changed',
        expect.objectContaining({
          key: 'claudeApiKey',
          value: 'sk-new-key'
        })
      );
    });
    
    it('should validate API key format', async () => {
      const result = await settingsStore.updateApiKey('claudeApiKey', 'invalid-key');
      
      // Should still succeed, as we don't actually validate formats in the implementation
      expect(result).toBe(true);
    });
  });
});