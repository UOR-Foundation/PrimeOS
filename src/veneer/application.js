/**
 * PrimeOS Veneer - Application Base Class
 * Base class for all PrimeOS applications
 */

const Prime = require("../core");
const EventEmitter = require("events");
const { PrimeError } = require("../core/error");
const { PrimeVeneerError } = require("./core");

/**
 * PrimeApplication Error class
 */
class PrimeApplicationError extends PrimeError {
  constructor(message, details = {}, code = "APPLICATION_ERROR") {
    super(message, details, code);
    this.name = "PrimeApplicationError";
  }
}

/**
 * Application state enumeration
 */
const ApplicationState = {
  CREATED: "created",
  INITIALIZING: "initializing",
  INITIALIZED: "initialized",
  STARTING: "starting",
  RUNNING: "running",
  PAUSING: "pausing",
  PAUSED: "paused",
  RESUMING: "resuming",
  STOPPING: "stopping",
  STOPPED: "stopped",
  ERROR: "error",
};

/**
 * PrimeApplication base class
 * Base class for all PrimeOS applications
 */
class PrimeApplication extends EventEmitter {
  /**
   * Create a new PrimeApplication
   * @param {Object} manifest - Application manifest
   * @param {Object} context - Application context
   */
  constructor(manifest = {}, context = {}) {
    super();

    // Validate manifest
    if (!manifest.name) {
      throw new PrimeApplicationError(
        "Invalid manifest: missing name",
        {
          manifest,
        },
        "INVALID_MANIFEST",
      );
    }

    this.manifest = this._validateManifest(manifest);

    this.context = {
      veneer: null,
      appId: manifest.name,
      ...context,
    };

    // Application state
    this.state = ApplicationState.CREATED;

    // Resource handles
    this.resources = {
      storage: null,
      compute: null,
      memory: null,
      network: null,
    };

    // Application metadata exposed to the system
    this.metadata = {
      name: manifest.name,
      displayName: manifest.displayName || manifest.name,
      version: manifest.version || "1.0.0",
      description: manifest.description || "",
      author: manifest.author || "",
      license: manifest.license || "",
      interfaces: manifest.interfaces || { provides: [], consumes: [] },
    };

    // Coherence state
    this.coherence = {
      score: 1.0,
      boundaries: manifest.coherence?.boundaries || {},
      validators: [],
      resolvers: [],
    };

    // Bind lifecycle methods to maintain context
    this.init = this.init.bind(this);
    this.start = this.start.bind(this);
    this.pause = this.pause.bind(this);
    this.resume = this.resume.bind(this);
    this.stop = this.stop.bind(this);

    Prime.Logger.debug("PrimeApplication created", {
      name: this.manifest.name,
    });
  }

  /**
   * Validate the manifest
   * @private
   * @param {Object} manifest - Application manifest
   * @returns {Object} - Validated manifest
   */
  _validateManifest(manifest) {
    // Ensure required fields
    const validated = {
      name: manifest.name,
      version: manifest.version || "1.0.0",
      displayName: manifest.displayName || manifest.name,
      description: manifest.description || "",
      author: manifest.author || "",
      license: manifest.license || "",
      entry: manifest.entry || "./index.js",
      dependencies: manifest.dependencies || {},
      resources: manifest.resources || {},
      permissions: manifest.permissions || [],
      interfaces: manifest.interfaces || { provides: [], consumes: [] },
      coherence: manifest.coherence || { minThreshold: 0.7 },
      schemas: manifest.schemas || {},
    };

    // Validate resources
    if (manifest.resources) {
      validated.resources = {
        storage: manifest.resources.storage || {},
        compute: manifest.resources.compute || {},
        memory: manifest.resources.memory || {},
      };
    }

    return validated;
  }

  /**
   * Set the veneer context
   * @param {Object} veneer - PrimeVeneer instance
   * @param {string} appId - Application ID in the veneer
   */
  setVeneerContext(veneer, appId) {
    this.context.veneer = veneer;
    this.context.appId = appId;
  }

  /**
   * Initialize the application
   * Override this method in your application
   * @returns {Promise<void>}
   */
  async init() {
    if (
      this.state !== ApplicationState.CREATED &&
      this.state !== ApplicationState.STOPPED
    ) {
      throw new PrimeApplicationError(
        "Cannot initialize application in current state",
        {
          currentState: this.state,
          expectedState: ApplicationState.CREATED,
        },
        "INVALID_STATE_TRANSITION",
      );
    }

    try {
      this.state = ApplicationState.INITIALIZING;
      this.emit("initializing");

      // Request resources defined in manifest
      await this._requestResources();

      // Load coherence boundaries
      await this._loadCoherenceBoundaries();

      // Initialize is complete
      this.state = ApplicationState.INITIALIZED;
      this.emit("initialized");

      Prime.Logger.info("Application initialized", {
        name: this.manifest.name,
        appId: this.context.appId,
      });
    } catch (error) {
      this.state = ApplicationState.ERROR;
      this.emit("error", error);

      Prime.Logger.error("Failed to initialize application", {
        name: this.manifest.name,
        error,
      });

      throw new PrimeApplicationError(
        "Failed to initialize application",
        {
          originalError: error,
        },
        "INIT_FAILED",
      );
    }
  }

  /**
   * Start the application
   * Override this method in your application
   * @returns {Promise<void>}
   */
  async start() {
    if (
      this.state !== ApplicationState.INITIALIZED &&
      this.state !== ApplicationState.PAUSED
    ) {
      throw new PrimeApplicationError(
        "Cannot start application in current state",
        {
          currentState: this.state,
          expectedState: [
            ApplicationState.INITIALIZED,
            ApplicationState.PAUSED,
          ],
        },
        "INVALID_STATE_TRANSITION",
      );
    }

    try {
      this.state = ApplicationState.STARTING;
      this.emit("starting");

      // Application is now running
      this.state = ApplicationState.RUNNING;
      this.emit("started");

      Prime.Logger.info("Application started", {
        name: this.manifest.name,
        appId: this.context.appId,
      });
    } catch (error) {
      this.state = ApplicationState.ERROR;
      this.emit("error", error);

      Prime.Logger.error("Failed to start application", {
        name: this.manifest.name,
        error,
      });

      throw new PrimeApplicationError(
        "Failed to start application",
        {
          originalError: error,
        },
        "START_FAILED",
      );
    }
  }

  /**
   * Pause the application
   * Override this method in your application
   * @returns {Promise<void>}
   */
  async pause() {
    if (this.state !== ApplicationState.RUNNING) {
      throw new PrimeApplicationError(
        "Cannot pause application in current state",
        {
          currentState: this.state,
          expectedState: ApplicationState.RUNNING,
        },
        "INVALID_STATE_TRANSITION",
      );
    }

    try {
      this.state = ApplicationState.PAUSING;
      this.emit("pausing");

      // Application is now paused
      this.state = ApplicationState.PAUSED;
      this.emit("paused");

      Prime.Logger.info("Application paused", {
        name: this.manifest.name,
        appId: this.context.appId,
      });
    } catch (error) {
      this.state = ApplicationState.ERROR;
      this.emit("error", error);

      Prime.Logger.error("Failed to pause application", {
        name: this.manifest.name,
        error,
      });

      throw new PrimeApplicationError(
        "Failed to pause application",
        {
          originalError: error,
        },
        "PAUSE_FAILED",
      );
    }
  }

  /**
   * Resume the application
   * Override this method in your application
   * @returns {Promise<void>}
   */
  async resume() {
    if (this.state !== ApplicationState.PAUSED) {
      throw new PrimeApplicationError(
        "Cannot resume application in current state",
        {
          currentState: this.state,
          expectedState: ApplicationState.PAUSED,
        },
        "INVALID_STATE_TRANSITION",
      );
    }

    try {
      this.state = ApplicationState.RESUMING;
      this.emit("resuming");

      // Application is now running
      this.state = ApplicationState.RUNNING;
      this.emit("resumed");

      Prime.Logger.info("Application resumed", {
        name: this.manifest.name,
        appId: this.context.appId,
      });
    } catch (error) {
      this.state = ApplicationState.ERROR;
      this.emit("error", error);

      Prime.Logger.error("Failed to resume application", {
        name: this.manifest.name,
        error,
      });

      throw new PrimeApplicationError(
        "Failed to resume application",
        {
          originalError: error,
        },
        "RESUME_FAILED",
      );
    }
  }

  /**
   * Stop the application
   * Override this method in your application
   * @returns {Promise<void>}
   */
  async stop() {
    // Can stop from running or paused state
    if (
      this.state !== ApplicationState.RUNNING &&
      this.state !== ApplicationState.PAUSED &&
      this.state !== ApplicationState.ERROR
    ) {
      throw new PrimeApplicationError(
        "Cannot stop application in current state",
        {
          currentState: this.state,
          expectedState: [
            ApplicationState.RUNNING,
            ApplicationState.PAUSED,
            ApplicationState.ERROR,
          ],
        },
        "INVALID_STATE_TRANSITION",
      );
    }

    try {
      this.state = ApplicationState.STOPPING;
      this.emit("stopping");

      // Release resources
      await this._releaseResources();

      // Application is now stopped
      this.state = ApplicationState.STOPPED;
      this.emit("stopped");

      Prime.Logger.info("Application stopped", {
        name: this.manifest.name,
        appId: this.context.appId,
      });
    } catch (error) {
      this.state = ApplicationState.ERROR;
      this.emit("error", error);

      Prime.Logger.error("Failed to stop application", {
        name: this.manifest.name,
        error,
      });

      throw new PrimeApplicationError(
        "Failed to stop application",
        {
          originalError: error,
        },
        "STOP_FAILED",
      );
    }
  }

  /**
   * Calculate the application's coherence score
   * @returns {number} - Coherence score between 0 and 1
   */
  calculateCoherence() {
    // Default implementation - should be overridden by applications
    // that need custom coherence calculations
    return this.coherence.score;
  }

  /**
   * Get a resource from the veneer
   * @param {string} resourceType - Type of resource (storage, compute, memory, network)
   * @param {Object} requirements - Resource requirements
   * @returns {Promise<Object>} - Resource handle
   */
  async getResource(resourceType, requirements) {
    if (!this.context.veneer) {
      throw new PrimeApplicationError(
        "No veneer context",
        {},
        "NO_VENEER_CONTEXT",
      );
    }

    // Check if resource is already allocated
    if (this.resources[resourceType]) {
      return this.resources[resourceType];
    }

    // Combine manifest requirements with requested requirements
    const combinedRequirements = {
      ...this.manifest.resources[resourceType],
      ...requirements,
    };

    // Allocate from veneer
    const resourceHandle = await this.context.veneer.allocateResource(
      this.context.appId,
      resourceType,
      combinedRequirements,
    );

    // Store handle
    this.resources[resourceType] = resourceHandle;

    return resourceHandle;
  }

  /**
   * Release a resource
   * @param {string} resourceType - Type of resource to release
   * @returns {Promise<boolean>} - True if successfully released
   */
  async releaseResource(resourceType) {
    if (!this.context.veneer) {
      throw new PrimeApplicationError(
        "No veneer context",
        {},
        "NO_VENEER_CONTEXT",
      );
    }

    if (!this.resources[resourceType]) {
      return false;
    }

    // Release from veneer
    const result = await this.context.veneer.releaseResource(
      this.context.appId,
      resourceType,
    );

    if (result) {
      this.resources[resourceType] = null;
    }

    return result;
  }

  /**
   * Request resources defined in manifest
   * @private
   */
  async _requestResources() {
    if (!this.context.veneer) {
      return;
    }

    // Request storage if defined in manifest
    if (
      this.manifest.resources.storage &&
      Object.keys(this.manifest.resources.storage).length > 0
    ) {
      await this.getResource("storage", this.manifest.resources.storage);
    }

    // Request compute if defined in manifest
    if (
      this.manifest.resources.compute &&
      Object.keys(this.manifest.resources.compute).length > 0
    ) {
      await this.getResource("compute", this.manifest.resources.compute);
    }

    // Request memory if defined in manifest
    if (
      this.manifest.resources.memory &&
      Object.keys(this.manifest.resources.memory).length > 0
    ) {
      await this.getResource("memory", this.manifest.resources.memory);
    }
  }

  /**
   * Release all allocated resources
   * @private
   */
  async _releaseResources() {
    // Release each allocated resource
    for (const resourceType of Object.keys(this.resources)) {
      if (this.resources[resourceType]) {
        await this.releaseResource(resourceType);
      }
    }
  }

  /**
   * Load coherence boundaries
   * @private
   */
  async _loadCoherenceBoundaries() {
    // Load boundaries from manifest
    if (!this.manifest.coherence || !this.manifest.coherence.boundaries) {
      return;
    }

    // For now, just store boundaries
    this.coherence.boundaries = this.manifest.coherence.boundaries;

    // In a real implementation, we would load and instantiate validators and resolvers
    // from the application's code
  }
}

// Add to Prime namespace
Prime.Veneer = Prime.Veneer || {};
Prime.Veneer.PrimeApplication = PrimeApplication;
Prime.Veneer.ApplicationState = ApplicationState;
Prime.Veneer.PrimeApplicationError = PrimeApplicationError;

module.exports = {
  PrimeApplication,
  ApplicationState,
  PrimeApplicationError,
};
