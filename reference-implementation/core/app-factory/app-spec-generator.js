/**
 * PrimeOS App Specification Generator
 * 
 * Service for transforming user requirements into formal application
 * specifications for PrimeOS applications.
 */

class AppSpecGenerator {
  /**
   * Creates a new App Specification Generator instance
   * @param {Object} options - Configuration options
   * @param {Object} options.claudeService - ClaudeService instance for AI assistance
   * @param {Object} options.eventBus - Event bus for notifications
   * @param {Object} options.templates - Optional specification templates
   */
  constructor(options) {
    // Validate required dependencies
    if (!options.claudeService) {
      throw new Error('AppSpecGenerator requires a claudeService instance');
    }
    
    // Store dependencies
    this.claudeService = options.claudeService;
    this.eventBus = options.eventBus || null;
    this.templates = options.templates || this._getDefaultTemplates();
    
    console.log('AppSpecGenerator initialized');
  }
  
  /**
   * Generate domain model from user input
   * @param {Object} description - User-provided app description
   * @returns {Promise<Object>} Domain model
   */
  async generateDomainModel(description) {
    if (!description) {
      throw new Error('App description is required');
    }
    
    console.log('Generating domain model');
    
    try {
      // Delegate to Claude Service
      const domainInsights = await this.claudeService.generateDomainInsights({
        purpose: description
      });
      
      // Notify domain model creation
      this._notifyEvent('domain-model-created', {
        model: domainInsights
      });
      
      return domainInsights;
    } catch (error) {
      console.error('Failed to generate domain model:', error);
      throw error;
    }
  }
  
  /**
   * Generate entity model from requirements
   * @param {Object} requirements - User-provided requirements
   * @param {Object} domainModel - Previously generated domain model
   * @returns {Promise<Object>} Entity model
   */
  async generateEntityModel(requirements, domainModel) {
    if (!requirements) {
      throw new Error('Requirements are required');
    }
    
    console.log('Generating entity model');
    
    try {
      // Delegate to Claude Service
      const enhancedRequirements = await this.claudeService.enhanceRequirements(
        requirements,
        domainModel
      );
      
      // Extract entity model from enhanced requirements
      const entityModel = {
        entities: enhancedRequirements.entities || [],
        relationships: enhancedRequirements.relationships || []
      };
      
      // Notify entity model creation
      this._notifyEvent('entity-model-created', {
        model: entityModel
      });
      
      return entityModel;
    } catch (error) {
      console.error('Failed to generate entity model:', error);
      throw error;
    }
  }
  
  /**
   * Generate full application specification
   * @param {Object} domainModel - Domain model
   * @param {Object} entityModel - Entity model
   * @param {Object} options - Additional options
   * @returns {Promise<Object>} Complete application specification
   */
  async generateAppSpecification(domainModel, entityModel, options = {}) {
    if (!domainModel) {
      throw new Error('Domain model is required');
    }
    
    if (!entityModel) {
      throw new Error('Entity model is required');
    }
    
    console.log('Generating app specification');
    
    try {
      // Prepare combined requirements
      const requirements = {
        entities: entityModel.entities,
        relationships: entityModel.relationships,
        features: options.features || domainModel.coreFeatures || [],
        userInteractions: options.userInteractions || []
      };
      
      // Generate specification via Claude
      const specification = await this.claudeService.generateAppSpecification(
        domainModel,
        requirements
      );
      
      // Apply template defaults
      const completeSpec = this._applyTemplateDefaults(specification, options);
      
      // Break down the specification into manifolds (discrete object depths)
      const manifestedSpec = this._decomposeSpecIntoManifolds(completeSpec);
      
      // Validate the specification
      const validationResult = await this.validateSpecification(manifestedSpec);
      
      if (!validationResult.valid) {
        console.warn('Generated specification has validation issues:', validationResult.errors);
      }
      
      // Notify specification creation
      this._notifyEvent('specification-created', {
        specification: manifestedSpec,
        validationResult
      });
      
      return manifestedSpec;
    } catch (error) {
      console.error('Failed to generate app specification:', error);
      throw error;
    }
  }
  
  /**
   * Validate an application specification
   * @param {Object} specification - Application specification to validate
   * @returns {Promise<Object>} Validation result
   */
  async validateSpecification(specification) {
    if (!specification) {
      throw new Error('Specification is required');
    }
    
    console.log('Validating specification');
    
    try {
      // Basic validation checks
      const basicValidation = this._performBasicValidation(specification);
      
      if (!basicValidation.valid) {
        return basicValidation;
      }
      
      // Delegate to Claude for deeper validation
      return await this.claudeService.validateSpecification(specification);
    } catch (error) {
      console.error('Failed to validate specification:', error);
      return {
        valid: false,
        errors: [error.message]
      };
    }
  }
  
  /**
   * Modify an existing specification
   * @param {Object} specification - Original specification
   * @param {Object} modifications - Modifications to apply
   * @returns {Promise<Object>} Updated specification
   */
  async modifySpecification(specification, modifications) {
    if (!specification) {
      throw new Error('Original specification is required');
    }
    
    if (!modifications) {
      throw new Error('Modifications are required');
    }
    
    console.log('Modifying specification');
    
    try {
      // Deep clone specification to avoid modifying original
      const updatedSpec = JSON.parse(JSON.stringify(specification));
      
      // Apply modifications
      Object.keys(modifications).forEach(key => {
        if (key in updatedSpec) {
          if (Array.isArray(updatedSpec[key]) && Array.isArray(modifications[key])) {
            // Merge arrays
            updatedSpec[key] = [...updatedSpec[key], ...modifications[key]];
          } else if (typeof updatedSpec[key] === 'object' && typeof modifications[key] === 'object') {
            // Merge objects
            updatedSpec[key] = { ...updatedSpec[key], ...modifications[key] };
          } else {
            // Replace value
            updatedSpec[key] = modifications[key];
          }
        } else {
          // Add new property
          updatedSpec[key] = modifications[key];
        }
      });
      
      // Validate the modified specification
      const validationResult = await this.validateSpecification(updatedSpec);
      
      // Notify specification modification
      this._notifyEvent('specification-modified', {
        specification: updatedSpec,
        validationResult
      });
      
      return {
        specification: updatedSpec,
        validationResult
      };
    } catch (error) {
      console.error('Failed to modify specification:', error);
      throw error;
    }
  }
  
  /**
   * Perform basic validation checks on a specification
   * @private
   * @param {Object} specification - Specification to validate
   * @returns {Object} Basic validation result
   */
  _performBasicValidation(specification) {
    const errors = [];
    
    // Check for required top-level properties
    const requiredProps = [
      'appName',
      'dataModels',
      'components',
      'appInterfaces'
    ];
    
    for (const prop of requiredProps) {
      if (!specification[prop]) {
        errors.push(`Missing required property: ${prop}`);
      }
    }
    
    // Check data models
    if (specification.dataModels && Array.isArray(specification.dataModels)) {
      specification.dataModels.forEach((model, index) => {
        if (!model.name) {
          errors.push(`Data model at index ${index} is missing name property`);
        }
        if (!model.properties || !Array.isArray(model.properties)) {
          errors.push(`Data model ${model.name || index} is missing properties array`);
        }
      });
    }
    
    // Check components
    if (specification.components && Array.isArray(specification.components)) {
      specification.components.forEach((component, index) => {
        if (!component.name) {
          errors.push(`Component at index ${index} is missing name property`);
        }
        if (!component.type) {
          errors.push(`Component ${component.name || index} is missing type property`);
        }
      });
    }
    
    return {
      valid: errors.length === 0,
      errors
    };
  }
  
  /**
   * Apply template defaults to a specification
   * @private
   * @param {Object} specification - Generated specification
   * @param {Object} options - Additional options
   * @returns {Object} Specification with defaults applied
   */
  _applyTemplateDefaults(specification, options) {
    // Deep clone specification and template
    const result = JSON.parse(JSON.stringify(specification));
    const template = this._getTemplateForType(options.appType || 'standard');
    
    // Apply template defaults for missing properties
    Object.keys(template).forEach(key => {
      if (result[key] === undefined) {
        result[key] = template[key];
      } else if (typeof template[key] === 'object' && !Array.isArray(template[key]) && 
                 typeof result[key] === 'object' && !Array.isArray(result[key])) {
        // Merge objects one level deep
        result[key] = { ...template[key], ...result[key] };
      }
    });
    
    return result;
  }
  
  /**
   * Get template for a specific app type
   * @private
   * @param {string} appType - Type of application
   * @returns {Object} Template for the app type
   */
  _getTemplateForType(appType) {
    return this.templates[appType] || this.templates.standard;
  }
  
  /**
   * Get default specification templates
   * @private
   * @returns {Object} Default templates
   */
  _getDefaultTemplates() {
    return {
      standard: {
        architecture: {
          type: 'modular',
          layers: ['ui', 'business-logic', 'data'],
          bases: {
            base0: {
              // Neural Network Specification layer
              embedding: { dimensions: 128, algorithm: 'default' },
              logic: { operators: ['basic', 'extended'] },
              representation: { model: 'symmetric' },
              processor: { type: 'spectral' }
            },
            base1: {
              // Resource layer
              runtime: { mode: 'standard' },
              observation: { events: true },
              interaction: { protocols: ['http', 'event'] },
              representation: { formats: ['json', 'binary'] }
            },
            base2: {
              // Kernel layer
              resourceClient: { type: 'standard' },
              appManagement: { lifecycle: true },
              systemManagement: { services: true }
            },
            base3: {
              // Application layer
              behavior: { language: 'javascript' },
              framework: { styling: true },
              structure: { componentBased: true }
            }
          }
        },
        manifestStructure: {
          meta: {
            requiredFields: ['name', 'version', 'description']
          },
          invariant: {
            assets: true,
            staticCode: true
          },
          variant: {
            stateModel: 'immutable',
            persistence: true
          }
        },
        styling: {
          cssFramework: 'primeOS-ui',
          themeSupport: true
        },
        buildConfig: {
          bundler: 'primeOS-bundler',
          minify: true,
          sourceMap: true
        },
        testingStrategy: {
          unit: true,
          integration: true,
          coherenceChecks: true,
          testingFramework: 'jest'
        }
      },
      utility: {
        architecture: {
          type: 'service',
          layers: ['business-logic', 'data'],
          bases: {
            base0: {
              embedding: { dimensions: 64, algorithm: 'lightweight' },
              logic: { operators: ['basic'] },
              representation: { model: 'minimal' },
              processor: { type: 'basic' }
            },
            base1: {
              runtime: { mode: 'headless' },
              observation: { events: true },
              interaction: { protocols: ['event'] },
              representation: { formats: ['json'] }
            },
            base2: {
              resourceClient: { type: 'minimal' },
              appManagement: { lifecycle: true }
            },
            base3: {
              behavior: { language: 'javascript' }
            }
          }
        },
        manifestStructure: {
          meta: {
            requiredFields: ['name', 'version', 'description']
          },
          invariant: {
            staticCode: true
          },
          variant: {
            stateModel: 'functional',
            persistence: false
          }
        },
        uiPresence: 'minimal',
        buildConfig: {
          bundler: 'primeOS-bundler',
          minify: true,
          sourceMap: false
        }
      },
      game: {
        architecture: {
          type: 'component-based',
          layers: ['rendering', 'game-logic', 'input', 'audio'],
          bases: {
            base0: {
              embedding: { dimensions: 256, algorithm: 'optimized' },
              logic: { operators: ['basic', 'extended', 'spatial'] },
              representation: { model: 'dynamic' },
              processor: { type: 'realtime' }
            },
            base1: {
              runtime: { mode: 'performance' },
              observation: { events: true, metrics: true },
              interaction: { protocols: ['event', 'binary'] },
              representation: { formats: ['json', 'binary', 'compressed'] }
            },
            base2: {
              resourceClient: { type: 'optimized' },
              appManagement: { lifecycle: true },
              systemManagement: { services: true }
            },
            base3: {
              behavior: { language: 'javascript' },
              framework: { styling: true },
              structure: { componentBased: true }
            }
          }
        },
        manifestStructure: {
          meta: {
            requiredFields: ['name', 'version', 'description', 'gameType']
          },
          invariant: {
            assets: true,
            staticCode: true
          },
          variant: {
            stateModel: 'immutable',
            persistence: true
          }
        },
        gameLoop: true,
        assetManagement: {
          images: true,
          audio: true,
          models: false
        },
        buildConfig: {
          bundler: 'primeOS-bundler',
          minify: true,
          sourceMap: true
        }
      }
    };
  }
  
  /**
   * Send event notification
   * @private
   * @param {string} event - Event name
   * @param {Object} data - Event data
   */
  _notifyEvent(event, data = {}) {
    if (this.eventBus) {
      this.eventBus.publish(`app-spec-generator:${event}`, {
        timestamp: new Date().toISOString(),
        ...data
      });
    }
  }
  
  /**
   * Decomposes a specification into discrete manifolds (depth levels)
   * This ensures each component has a clear single responsibility
   * @private
   * @param {Object} specification - The complete specification
   * @returns {Object} The decomposed specification with proper manifold structure
   */
  _decomposeSpecIntoManifolds(specification) {
    console.log('Decomposing specification into manifolds');
    
    // Deep clone the specification
    const spec = JSON.parse(JSON.stringify(specification));
    
    // Ensure base architecture manifolds are present
    if (!spec.architecture) {
      spec.architecture = {};
    }
    
    if (!spec.architecture.bases) {
      spec.architecture.bases = {
        base0: {}, // Neural Network Specification
        base1: {}, // Resource
        base2: {}, // Kernel
        base3: {}  // Application
      };
    }
    
    // Ensure manifest structure 
    if (!spec.manifestStructure) {
      spec.manifestStructure = {
        meta: { requiredFields: ['name', 'version', 'description'] },
        invariant: { assets: true, staticCode: true },
        variant: { stateModel: 'immutable', persistence: true }
      };
    }
    
    // Convert components to proper manifold structure
    if (spec.components && Array.isArray(spec.components)) {
      spec.components = this._decomposeComponentsIntoManifolds(spec.components);
    }
    
    // Convert data models to proper manifold structure
    if (spec.dataModels && Array.isArray(spec.dataModels)) {
      spec.dataModels = this._decomposeDataModelsIntoManifolds(spec.dataModels);
    }
    
    // Ensure coherence information
    spec.coherence = spec.coherence || {
      normThreshold: 0.85,
      measurementStrategy: 'dynamic',
      enforceInvariantPreservation: true
    };
    
    return spec;
  }
  
  /**
   * Decomposes components into proper manifold structure
   * @private
   * @param {Array} components - Array of components
   * @returns {Array} - Components with proper manifold structure
   */
  _decomposeComponentsIntoManifolds(components) {
    return components.map(component => {
      // Create deep clone
      const manifestedComponent = JSON.parse(JSON.stringify(component));
      
      // Ensure component has proper manifold structure
      manifestedComponent.meta = manifestedComponent.meta || {
        name: component.name,
        id: component.id || this._generateId(component.name),
        description: component.description || `Component for ${component.name}`,
        version: component.version || '1.0.0'
      };
      
      manifestedComponent.invariant = manifestedComponent.invariant || {
        type: component.type,
        interfaces: component.interfaces || [],
        dependencies: component.dependencies || []
      };
      
      manifestedComponent.variant = manifestedComponent.variant || {
        state: component.state || {},
        defaultConfig: component.defaultConfig || {}
      };
      
      // Determine base assignments
      manifestedComponent.baseAssignments = manifestedComponent.baseAssignments || {
        primary: this._determineComponentPrimaryBase(component),
        secondary: []
      };
      
      // Add coherence constraints for this component
      manifestedComponent.coherenceConstraints = manifestedComponent.coherenceConstraints || {
        requiredInterfaces: manifestedComponent.invariant.interfaces.filter(i => i.required),
        invariantPreservation: true,
        stateValidation: true
      };
      
      return manifestedComponent;
    });
  }
  
  /**
   * Decomposes data models into proper manifold structure
   * @private
   * @param {Array} dataModels - Array of data models
   * @returns {Array} - Data models with proper manifold structure
   */
  _decomposeDataModelsIntoManifolds(dataModels) {
    return dataModels.map(model => {
      // Create deep clone
      const manifestedModel = JSON.parse(JSON.stringify(model));
      
      // Ensure model has proper manifold structure
      manifestedModel.meta = manifestedModel.meta || {
        name: model.name,
        id: model.id || this._generateId(model.name),
        description: model.description || `Data model for ${model.name}`,
        version: model.version || '1.0.0'
      };
      
      manifestedModel.invariant = manifestedModel.invariant || {
        schema: {
          properties: model.properties || [],
          required: model.required || []
        },
        relations: model.relations || []
      };
      
      manifestedModel.variant = manifestedModel.variant || {
        persistence: model.persistence || {
          type: 'memory',
          indexedFields: []
        },
        defaultInstances: model.defaultInstances || []
      };
      
      // Determine manifold depth for properties
      if (manifestedModel.invariant.schema.properties) {
        manifestedModel.invariant.schema.properties = this._assignPropertyManifoldDepths(
          manifestedModel.invariant.schema.properties
        );
      }
      
      // Add coherence constraints
      manifestedModel.coherenceConstraints = manifestedModel.coherenceConstraints || {
        validateRelations: true,
        enforceTypes: true,
        checkCircularDependencies: true
      };
      
      return manifestedModel;
    });
  }
  
  /**
   * Assigns manifold depths to properties based on their complexity
   * @private
   * @param {Array} properties - Array of model properties
   * @returns {Array} - Properties with manifold depth information
   */
  _assignPropertyManifoldDepths(properties) {
    return properties.map(prop => {
      const property = { ...prop };
      
      // Determine manifold depth based on property type and complexity
      if (property.type === 'object' && property.properties) {
        property.manifoldDepth = 2;
        property.properties = this._assignPropertyManifoldDepths(property.properties);
      } else if (property.type === 'array' && property.items && property.items.type === 'object') {
        property.manifoldDepth = 2;
        if (property.items.properties) {
          property.items.properties = this._assignPropertyManifoldDepths(property.items.properties);
        }
      } else if (property.type === 'array') {
        property.manifoldDepth = 1;
      } else {
        property.manifoldDepth = 0;
      }
      
      // Add coherence metadata for types
      property.coherence = property.coherence || {
        preserveType: true,
        validationRules: property.validation || []
      };
      
      return property;
    });
  }
  
  /**
   * Determines the primary base for a component
   * @private
   * @param {Object} component - Component object
   * @returns {string} - Primary base (base0, base1, base2, or base3)
   */
  _determineComponentPrimaryBase(component) {
    // Logic to determine which base this component primarily belongs to
    const type = component.type?.toLowerCase() || '';
    
    if (type.includes('data') || type.includes('model') || type.includes('store')) {
      return 'base1'; // Resource layer
    } else if (type.includes('service') || type.includes('manager') || type.includes('system')) {
      return 'base2'; // Kernel layer
    } else if (type.includes('ui') || type.includes('view') || type.includes('component')) {
      return 'base3'; // Application layer
    } else if (type.includes('logic') || type.includes('algorithm') || type.includes('processor')) {
      return 'base0'; // Neural Network Specification layer
    }
    
    // Default to application layer
    return 'base3';
  }
  
  /**
   * Generates a stable ID from a name
   * @private
   * @param {string} name - Name to generate ID from
   * @returns {string} - Generated ID
   */
  _generateId(name) {
    // Create a simplified slug from the name
    const slug = name
      .toLowerCase()
      .replace(/[^a-z0-9]+/g, '-')
      .replace(/^-|-$/g, '');
      
    // Add a timestamp hash for uniqueness
    const timestamp = Date.now().toString(36);
    
    return `${slug}-${timestamp}`;
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { AppSpecGenerator };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.AppSpecGenerator = AppSpecGenerator;
}