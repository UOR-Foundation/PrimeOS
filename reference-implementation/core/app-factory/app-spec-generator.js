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
      
      // Validate the specification
      const validationResult = await this.validateSpecification(completeSpec);
      
      if (!validationResult.valid) {
        console.warn('Generated specification has validation issues:', validationResult.errors);
      }
      
      // Notify specification creation
      this._notifyEvent('specification-created', {
        specification: completeSpec,
        validationResult
      });
      
      return completeSpec;
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
          layers: ['ui', 'business-logic', 'data']
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
          testingFramework: 'jest'
        }
      },
      utility: {
        architecture: {
          type: 'service',
          layers: ['business-logic', 'data']
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
          layers: ['rendering', 'game-logic', 'input', 'audio']
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