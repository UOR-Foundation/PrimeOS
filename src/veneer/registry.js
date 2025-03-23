/**
 * PrimeOS Veneer - PrimeApp Registry
 * Manages all available PrimeApps and their versions
 */

const Prime = require("../core");
const { PrimeError } = require("../core/error");
const path = require("path");
const { PrimeVeneerError } = require("./core");
const semver = require("semver");

/**
 * PrimeApp Registry Error class
 */
class PrimeAppRegistryError extends PrimeError {
  constructor(message, details = {}, code = "REGISTRY_ERROR") {
    super(message, details, code);
    this.name = "PrimeAppRegistryError";
  }
}

/**
 * PrimeApp Registry
 * Manages app discovery, version tracking, and dependency resolution
 */
class PrimeAppRegistry {
  /**
   * Create a new PrimeApp registry
   * @param {Object} options - Registry options
   */
  constructor(options = {}) {
    this.options = {
      appDirectories: [],
      allowUnsigned: process.env.NODE_ENV === "development",
      ...options,
    };

    // Map of registered app manifests by app ID
    this.apps = new Map();

    // Map of app versions by app ID
    this.versions = new Map();

    // Map of app interdependencies
    this.dependencies = new Map();

    // Map of app capabilities/interfaces
    this.interfaces = {
      providers: new Map(),
      consumers: new Map(),
    };

    // Veneer reference
    this.veneer = null;

    Prime.Logger.info("PrimeApp Registry initialized", {
      options: this.options,
    });
  }

  /**
   * Set the veneer instance
   * @param {Object} veneer - PrimeVeneer instance
   */
  setVeneer(veneer) {
    this.veneer = veneer;
  }

  /**
   * Register a PrimeApp with the registry
   * @param {Object} manifest - App manifest
   * @param {string} appPath - Path to the app
   * @param {Object} options - Registration options
   * @returns {string} - App ID
   */
  registerApp(manifest, appPath, options = {}) {
    if (!manifest.name) {
      throw new PrimeAppRegistryError(
        "Invalid manifest: missing name",
        {
          manifest,
        },
        "INVALID_MANIFEST",
      );
    }

    if (!manifest.version) {
      throw new PrimeAppRegistryError(
        "Invalid manifest: missing version",
        {
          manifest,
        },
        "INVALID_MANIFEST",
      );
    }

    const appId = manifest.name;
    const appVersion = manifest.version;

    // Check if app is already registered
    if (
      this.apps.has(appId) &&
      this.versions.has(appId) &&
      this.versions.get(appId).includes(appVersion) &&
      !options.force
    ) {
      throw new PrimeAppRegistryError(
        "App version already registered",
        {
          appId,
          version: appVersion,
        },
        "APP_VERSION_EXISTS",
      );
    }

    // Store app manifest
    const appInfo = {
      manifest,
      path: appPath,
      registeredAt: Date.now(),
      status: "available",
      metadata: {
        ...manifest,
        interfaces: manifest.interfaces || { provides: [], consumes: [] },
      },
    };

    // Store app by ID
    this.apps.set(appId, appInfo);

    // Track version
    if (!this.versions.has(appId)) {
      this.versions.set(appId, []);
    }

    if (!this.versions.get(appId).includes(appVersion)) {
      this.versions.get(appId).push(appVersion);
      // Sort versions in descending order (newest first)
      this.versions.get(appId).sort((a, b) => semver.compare(b, a));
    }

    // Track dependencies
    if (manifest.dependencies) {
      this.dependencies.set(appId, manifest.dependencies);
    }

    // Track interfaces
    if (manifest.interfaces) {
      // Track provided interfaces
      if (
        manifest.interfaces.provides &&
        Array.isArray(manifest.interfaces.provides)
      ) {
        for (const interfaceName of manifest.interfaces.provides) {
          if (!this.interfaces.providers.has(interfaceName)) {
            this.interfaces.providers.set(interfaceName, []);
          }

          const providers = this.interfaces.providers.get(interfaceName);
          if (
            !providers.some(
              (p) => p.appId === appId && p.version === appVersion,
            )
          ) {
            providers.push({
              appId,
              version: appVersion,
              priority: manifest.interfaces.priority || 0,
            });
          }
        }
      }

      // Track consumed interfaces
      if (
        manifest.interfaces.consumes &&
        Array.isArray(manifest.interfaces.consumes)
      ) {
        for (const interfaceName of manifest.interfaces.consumes) {
          if (!this.interfaces.consumers.has(interfaceName)) {
            this.interfaces.consumers.set(interfaceName, []);
          }

          const consumers = this.interfaces.consumers.get(interfaceName);
          if (
            !consumers.some(
              (c) => c.appId === appId && c.version === appVersion,
            )
          ) {
            consumers.push({
              appId,
              version: appVersion,
            });
          }
        }
      }
    }

    Prime.Logger.info("App registered in registry", {
      appId,
      version: appVersion,
      path: appPath,
    });

    return appId;
  }

  /**
   * Unregister a PrimeApp from the registry
   * @param {string} appId - App ID
   * @param {string} version - App version (optional, if not provided all versions are unregistered)
   * @returns {boolean} - True if successfully unregistered
   */
  unregisterApp(appId, version) {
    if (!this.apps.has(appId)) {
      return false;
    }

    if (version) {
      // Unregister specific version
      if (this.versions.has(appId)) {
        const versionIndex = this.versions.get(appId).indexOf(version);

        if (versionIndex !== -1) {
          // Remove version
          this.versions.get(appId).splice(versionIndex, 1);

          // If no versions left, remove the app entirely
          if (this.versions.get(appId).length === 0) {
            this.apps.delete(appId);
            this.versions.delete(appId);
            this.dependencies.delete(appId);

            // Clean up interfaces
            this._cleanupAppInterfaces(appId);
          }

          Prime.Logger.info("App version unregistered", { appId, version });
          return true;
        }
      }

      return false;
    } else {
      // Unregister all versions
      this.apps.delete(appId);
      this.versions.delete(appId);
      this.dependencies.delete(appId);

      // Clean up interfaces
      this._cleanupAppInterfaces(appId);

      Prime.Logger.info("App unregistered from registry", { appId });
      return true;
    }
  }

  /**
   * Get available apps
   * @param {Object} options - Filter options
   * @returns {Array<Object>} - List of app manifests
   */
  getAvailableApps(options = {}) {
    const { interface: interfaceName, latestVersionOnly = false } = options;

    let appList = Array.from(this.apps.entries()).map(([appId, appInfo]) => ({
      id: appId,
      ...appInfo.metadata,
    }));

    // Filter by interface if provided
    if (interfaceName) {
      const providers = this.interfaces.providers.get(interfaceName) || [];
      const providerIds = providers.map((p) => p.appId);

      appList = appList.filter((app) => providerIds.includes(app.id));
    }

    // If latest version only, filter out older versions
    if (latestVersionOnly) {
      appList = appList.filter((app) => {
        const appVersions = this.versions.get(app.id) || [];
        return appVersions.length === 0 || app.version === appVersions[0];
      });
    }

    return appList;
  }

  /**
   * Get app manifest by ID and version
   * @param {string} appId - App ID
   * @param {string} version - App version (optional, latest used if not provided)
   * @returns {Object|null} - App manifest or null if not found
   */
  getAppManifest(appId, version) {
    if (!this.apps.has(appId)) {
      return null;
    }

    if (!version) {
      // Use latest version
      const versions = this.versions.get(appId) || [];

      if (versions.length === 0) {
        return null;
      }

      version = versions[0];
    } else {
      // Check if version exists
      const versions = this.versions.get(appId) || [];

      if (!versions.includes(version)) {
        return null;
      }
    }

    // Get app info
    const appInfo = this.apps.get(appId);

    if (appInfo.manifest.version !== version) {
      // In a real implementation, we would need to fetch the specific version
      // For now, we'll return null if the current manifest version doesn't match
      return null;
    }

    return { ...appInfo.manifest };
  }

  /**
   * Resolve app dependencies
   * @param {string} appId - App ID
   * @param {Object} options - Resolution options
   * @returns {Object} - Resolved dependencies
   */
  resolveDependencies(appId, options = {}) {
    if (!this.apps.has(appId)) {
      throw new PrimeAppRegistryError(
        "App not found",
        { appId },
        "APP_NOT_FOUND",
      );
    }

    const appInfo = this.apps.get(appId);
    const dependencies = appInfo.manifest.dependencies || {};

    // Check if app has dependencies
    if (Object.keys(dependencies).length === 0) {
      return { resolved: {}, missing: [], conflicts: [] };
    }

    const resolved = {};
    const missing = [];
    const conflicts = [];

    // Resolve each dependency
    for (const [depId, versionRange] of Object.entries(dependencies)) {
      if (!this.apps.has(depId)) {
        missing.push({ id: depId, versionRange });
        continue;
      }

      const availableVersions = this.versions.get(depId) || [];

      if (availableVersions.length === 0) {
        missing.push({ id: depId, versionRange });
        continue;
      }

      // Find compatible version
      const compatibleVersion = availableVersions.find((version) =>
        semver.satisfies(version, versionRange),
      );

      if (!compatibleVersion) {
        conflicts.push({
          id: depId,
          versionRange,
          availableVersions,
        });
        continue;
      }

      resolved[depId] = compatibleVersion;
    }

    return {
      resolved,
      missing,
      conflicts,
    };
  }

  /**
   * Find apps that provide a specific interface
   * @param {string} interfaceName - Interface name
   * @returns {Array<Object>} - List of app IDs that provide the interface
   */
  findInterfaceProviders(interfaceName) {
    if (!this.interfaces.providers.has(interfaceName)) {
      return [];
    }

    const providers = this.interfaces.providers.get(interfaceName);

    // Sort providers by priority
    return [...providers].sort((a, b) => b.priority - a.priority);
  }

  /**
   * Find apps that consume a specific interface
   * @param {string} interfaceName - Interface name
   * @returns {Array<Object>} - List of app IDs that consume the interface
   */
  findInterfaceConsumers(interfaceName) {
    if (!this.interfaces.consumers.has(interfaceName)) {
      return [];
    }

    return [...this.interfaces.consumers.get(interfaceName)];
  }

  /**
   * Discover apps in the configured directories
   * @param {string[]} additionalDirs - Additional directories to search
   * @returns {Promise<Array<Object>>} - Discovered apps
   */
  async discoverApps(additionalDirs = []) {
    const fs = require("fs").promises;
    const dirs = [...this.options.appDirectories, ...additionalDirs];

    if (dirs.length === 0) {
      return [];
    }

    const discoveredApps = [];

    for (const dir of dirs) {
      try {
        // Check if directory exists
        await fs.access(dir);

        // Read directory
        const entries = await fs.readdir(dir, { withFileTypes: true });

        // Find app directories
        for (const entry of entries) {
          if (entry.isDirectory()) {
            const appDir = path.join(dir, entry.name);
            const manifestPath = path.join(appDir, "manifest.json");

            try {
              // Check if manifest exists
              await fs.access(manifestPath);

              // Read manifest
              const manifestContent = await fs.readFile(manifestPath, "utf8");
              const manifest = JSON.parse(manifestContent);

              // Register app
              this.registerApp(manifest, appDir, { force: true });

              discoveredApps.push({
                id: manifest.name,
                version: manifest.version,
                path: appDir,
              });
            } catch (error) {
              // Skip directories without valid manifests
              Prime.Logger.debug("Skipping directory without valid manifest", {
                dir: appDir,
                error: error.message,
              });
            }
          }
        }
      } catch (error) {
        Prime.Logger.warn("Error discovering apps in directory", {
          dir,
          error: error.message,
        });
      }
    }

    return discoveredApps;
  }

  /**
   * Clean up app interfaces when unregistering an app
   * @private
   * @param {string} appId - App ID to clean up
   */
  _cleanupAppInterfaces(appId) {
    // Clean up provider interfaces
    for (const [
      interfaceName,
      providers,
    ] of this.interfaces.providers.entries()) {
      const filteredProviders = providers.filter((p) => p.appId !== appId);

      if (filteredProviders.length === 0) {
        this.interfaces.providers.delete(interfaceName);
      } else {
        this.interfaces.providers.set(interfaceName, filteredProviders);
      }
    }

    // Clean up consumer interfaces
    for (const [
      interfaceName,
      consumers,
    ] of this.interfaces.consumers.entries()) {
      const filteredConsumers = consumers.filter((c) => c.appId !== appId);

      if (filteredConsumers.length === 0) {
        this.interfaces.consumers.delete(interfaceName);
      } else {
        this.interfaces.consumers.set(interfaceName, filteredConsumers);
      }
    }
  }
}

// Add to Prime namespace
Prime.Veneer = Prime.Veneer || {};
Prime.Veneer.PrimeAppRegistry = PrimeAppRegistry;
Prime.Veneer.PrimeAppRegistryError = PrimeAppRegistryError;

module.exports = {
  PrimeAppRegistry,
  PrimeAppRegistryError,
};
