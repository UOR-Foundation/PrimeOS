/**
 * PrimeOS JavaScript Library - Framework
 * Prime Framework four-tier architecture
 * Version 1.0.0
 */

// Import extended Prime
import { Prime } from './coherence.js';

(function(Prime) {
  'use strict';
  
  /**
   * Base 0: Neural Network Specification
   * Abstract mathematical foundation for the entire system
   */
  const Base0 = {
    /**
     * Create an embedding model
     * @param {Object} config - Configuration object
     * @returns {Object} Embedding model
     */
    createEmbeddingModel: function(config = {}) {
      return {
        type: 'embedding',
        dimensions: config.dimensions || 128,
        metric: config.metric || 'euclidean',
        name: config.name || 'EmbeddingModel',
        
        /**
         * Embed data into the vector space
         * @param {*} data - Data to embed
         * @returns {Array} Embedding vector
         */
        embed: function(data) {
          if (config.embedFunction && typeof config.embedFunction === 'function') {
            return config.embedFunction(data);
          }
          
          // Default placeholder embedding function - returns zero vector
          return Array(this.dimensions).fill(0);
        },
        
        /**
         * Calculate distance between embeddings
         * @param {Array} a - First embedding
         * @param {Array} b - Second embedding
         * @returns {number} Distance
         */
        distance: function(a, b) {
          if (!Prime.Utils.isArray(a) || !Prime.Utils.isArray(b)) {
            throw new Prime.ValidationError('Embeddings must be arrays', {
              context: { 
                aType: typeof a,
                bType: typeof b,
                aIsArray: Prime.Utils.isArray(a),
                bIsArray: Prime.Utils.isArray(b)
              }
            });
          }
          
          // Compute distance based on the metric
          if (this.metric === 'euclidean') {
            let sum = 0;
            const maxLength = Math.max(a.length, b.length);
            
            for (let i = 0; i < maxLength; i++) {
              const aVal = i < a.length ? a[i] : 0;
              const bVal = i < b.length ? b[i] : 0;
              sum += Math.pow(aVal - bVal, 2);
            }
            
            return Math.sqrt(sum);
          } else if (this.metric === 'cosine') {
            let dotProduct = 0;
            let normA = 0;
            let normB = 0;
            const maxLength = Math.max(a.length, b.length);
            
            for (let i = 0; i < maxLength; i++) {
              const aVal = i < a.length ? a[i] : 0;
              const bVal = i < b.length ? b[i] : 0;
              
              dotProduct += aVal * bVal;
              normA += aVal * aVal;
              normB += bVal * bVal;
            }
            
            normA = Math.sqrt(normA);
            normB = Math.sqrt(normB);
            
            if (normA === 0 || normB === 0) {
              return 1; // Maximum distance for zero vectors
            }
            
            return 1 - (dotProduct / (normA * normB));
          } else if (this.metric === 'manhattan') {
            let sum = 0;
            const maxLength = Math.max(a.length, b.length);
            
            for (let i = 0; i < maxLength; i++) {
              const aVal = i < a.length ? a[i] : 0;
              const bVal = i < b.length ? b[i] : 0;
              sum += Math.abs(aVal - bVal);
            }
            
            return sum;
          }
          
          throw new Prime.InvalidOperationError(`Metric ${this.metric} not implemented`);
        },
        
        /**
         * Convert to UOR object
         * @param {Object} reference - UOR reference
         * @returns {Object} UOR object
         */
        toUOR: function(reference) {
          if (!Prime.UOR || !Prime.UOR.isReference(reference)) {
            throw new Prime.ValidationError('Invalid UOR reference');
          }
          
          return reference.createObject(this);
        },
        
        /**
         * Connect to other Base 0 components
         * @param {Object} components - Other Base 0 components
         * @returns {Object} Connected embedding model
         */
        connectToComponents: function(components) {
          this._components = components;
          return this;
        }
      };
    },
    
    /**
     * Create a logic model (fiber)
     * @param {Object} config - Configuration object
     * @returns {Object} Logic model
     */
    createLogicModel: function(config = {}) {
      return {
        type: 'logic',
        rules: config.rules || [],
        constraints: config.constraints || [],
        name: config.name || 'LogicModel',
        
        /**
         * Apply logic rules to data
         * @param {*} data - Data to process
         * @returns {*} Processed data
         */
        apply: function(data) {
          let result = data;
          
          // Apply each rule in sequence
          for (const rule of this.rules) {
            if (typeof rule === 'function') {
              result = rule(result);
            } else if (rule && typeof rule.apply === 'function') {
              result = rule.apply(result);
            }
          }
          
          return result;
        },
        
        /**
         * Validate data against constraints
         * @param {*} data - Data to validate
         * @returns {boolean} True if data is valid
         */
        validate: function(data) {
          // Check all constraints
          for (const constraint of this.constraints) {
            if (typeof constraint === 'function') {
              if (!constraint(data)) {
                return false;
              }
            } else if (constraint && typeof constraint.check === 'function') {
              if (!constraint.check(data)) {
                return false;
              }
            }
          }
          
          return true;
        },
        
        /**
         * Add a rule to the model
         * @param {Function|Object} rule - Rule to add
         * @returns {Object} Updated logic model
         */
        addRule: function(rule) {
          this.rules.push(rule);
          return this;
        },
        
        /**
         * Add a constraint to the model
         * @param {Function|Object} constraint - Constraint to add
         * @returns {Object} Updated logic model
         */
        addConstraint: function(constraint) {
          this.constraints.push(constraint);
          return this;
        },
        
        /**
         * Convert to UOR object
         * @param {Object} reference - UOR reference
         * @returns {Object} UOR object
         */
        toUOR: function(reference) {
          if (!Prime.UOR || !Prime.UOR.isReference(reference)) {
            throw new Prime.ValidationError('Invalid UOR reference');
          }
          
          return reference.createObject(this);
        },
        
        /**
         * Connect to other Base 0 components
         * @param {Object} components - Other Base 0 components
         * @returns {Object} Connected logic model
         */
        connectToComponents: function(components) {
          this._components = components;
          return this;
        }
      };
    },
    
    /**
     * Create a representation model (symmetry)
     * @param {Object} config - Configuration object
     * @returns {Object} Representation model
     */
    createRepresentationModel: function(config = {}) {
      return {
        type: 'representation',
        transformations: config.transformations || [],
        formats: config.formats || {},
        name: config.name || 'RepresentationModel',
        
        /**
         * Apply a transformation to data
         * @param {*} data - Data to transform
         * @param {string} transformation - Transformation name
         * @returns {*} Transformed data
         */
        transform: function(data, transformation) {
          const transform = this.transformations.find(t => t.name === transformation);
          
          if (!transform) {
            throw new Prime.InvalidOperationError(`Transformation ${transformation} not found`, {
              context: { 
                availableTransformations: this.transformations.map(t => t.name) 
              }
            });
          }
          
          if (typeof transform.apply === 'function') {
            return transform.apply(data);
          } else if (typeof transform === 'function') {
            return transform(data);
          }
          
          throw new Prime.InvalidOperationError(`Invalid transformation ${transformation}`);
        },
        
        /**
         * Convert data to the specified format
         * @param {*} data - Data to convert
         * @param {string} format - Target format
         * @returns {*} Converted data
         */
        represent: function(data, format) {
          if (!this.formats[format]) {
            throw new Prime.InvalidOperationError(`Format ${format} not found`, {
              context: { availableFormats: Object.keys(this.formats) }
            });
          }
          
          const formatter = this.formats[format];
          
          if (typeof formatter === 'function') {
            return formatter(data);
          } else if (formatter && typeof formatter.format === 'function') {
            return formatter.format(data);
          }
          
          throw new Prime.InvalidOperationError(`Invalid format ${format}`);
        },
        
        /**
         * Add a transformation to the model
         * @param {Object|Function} transformation - Transformation to add
         * @returns {Object} Updated representation model
         */
        addTransformation: function(transformation) {
          if (!transformation.name && typeof transformation !== 'function') {
            throw new Prime.ValidationError('Transformation must have a name property or be a function');
          }
          
          this.transformations.push(transformation);
          return this;
        },
        
        /**
         * Add a format to the model
         * @param {string} name - Format name
         * @param {Function|Object} formatter - Format handler
         * @returns {Object} Updated representation model
         */
        addFormat: function(name, formatter) {
          this.formats[name] = formatter;
          return this;
        },
        
        /**
         * Convert to UOR object
         * @param {Object} reference - UOR reference
         * @returns {Object} UOR object
         */
        toUOR: function(reference) {
          if (!Prime.UOR || !Prime.UOR.isReference(reference)) {
            throw new Prime.ValidationError('Invalid UOR reference');
          }
          
          return reference.createObject(this);
        },
        
        /**
         * Connect to other Base 0 components
         * @param {Object} components - Other Base 0 components
         * @returns {Object} Connected representation model
         */
        connectToComponents: function(components) {
          this._components = components;
          return this;
        }
      };
    },
    
    /**
     * Create a processor (spectral operator)
     * @param {Object} config - Configuration object
     * @returns {Object} Processor
     */
    createProcessor: function(config = {}) {
      return {
        type: 'processor',
        operations: config.operations || [],
        name: config.name || 'Processor',
        
        /**
         * Process data with an operation
         * @param {*} data - Data to process
         * @param {string} operation - Operation name
         * @returns {*} Processed data
         */
        process: function(data, operation) {
          const op = this.operations.find(o => o.name === operation);
          
          if (!op) {
            throw new Prime.InvalidOperationError(`Operation ${operation} not found`, {
              context: { availableOperations: this.operations.map(o => o.name) }
            });
          }
          
          if (typeof op.apply === 'function') {
            return op.apply(data);
          } else if (typeof op === 'function') {
            return op(data);
          }
          
          throw new Prime.InvalidOperationError(`Invalid operation ${operation}`);
        },
        
        /**
         * Compose two operations
         * @param {string} op1 - First operation
         * @param {string} op2 - Second operation
         * @returns {Function} Composed operation
         */
        compose: function(op1, op2) {
          return (data) => this.process(this.process(data, op1), op2);
        },
        
        /**
         * Add an operation to the processor
         * @param {Object|Function} operation - Operation to add
         * @returns {Object} Updated processor
         */
        addOperation: function(operation) {
          if (!operation.name && typeof operation !== 'function') {
            throw new Prime.ValidationError('Operation must have a name property or be a function');
          }
          
          this.operations.push(operation);
          return this;
        },
        
        /**
         * Convert to UOR object
         * @param {Object} reference - UOR reference
         * @returns {Object} UOR object
         */
        toUOR: function(reference) {
          if (!Prime.UOR || !Prime.UOR.isReference(reference)) {
            throw new Prime.ValidationError('Invalid UOR reference');
          }
          
          return reference.createObject(this);
        },
        
        /**
         * Connect to other Base 0 components
         * @param {Object} components - Other Base 0 components
         * @returns {Object} Connected processor
         */
        connectToComponents: function(components) {
          this._components = components;
          return this;
        }
      };
    },
    
    /**
     * Create all Base 0 components
     * @param {Object} config - Configuration object
     * @returns {Object} Base 0 components
     */
    createBase0Components: function(config = {}) {
      // Create components
      const embedding = this.createEmbeddingModel(config.embedding || {});
      const logic = this.createLogicModel(config.logic || {});
      const representation = this.createRepresentationModel(config.representation || {});
      const processor = this.createProcessor(config.processor || {});
      
      // Connect components to each other
      const components = { embedding, logic, representation, processor };
      
      embedding.connectToComponents(components);
      logic.connectToComponents(components);
      representation.connectToComponents(components);
      processor.connectToComponents(components);
      
      return components;
    },
    
    /**
     * Connect to coherence system
     * @param {Object} components - Base 0 components
     * @returns {Object} Connected components
     */
    connectToCoherence: function(components) {
      if (!Prime.coherence) {
        Prime.Logger.warn('Coherence system not available');
        return components;
      }
      
      // Register components with system-wide coherence tracking
      for (const key in components) {
        Prime.coherence.systemCoherence.register(components[key]);
      }
      
      return components;
    }
  };

  /**
   * Base 1: Resource
   * Concrete implementations of Base 0 models
   */
  const Base1 = {
    /**
     * Create a runtime model
     * @param {Object} config - Configuration object
     * @returns {Object} Runtime model
     */
    createRuntimeModel: function(config = {}) {
      return {
        type: 'runtime',
        embedding: config.embedding,
        logic: config.logic,
        representation: config.representation,
        processor: config.processor,
        name: config.name || 'RuntimeModel',
        
        /**
         * Start a model
         * @param {Object} model - Model to start
         * @returns {Object} Started model
         */
        start: function(model) {
          if (!model) {
            throw new Prime.ValidationError('Model is required');
          }
          
          // Initialize the model
          if (typeof model.initialize === 'function') {
            model.initialize();
          }
          
          // Set the model's status to running
          model._running = true;
          
          // Publish event
          Prime.EventBus.publish('model:started', { model });
          
          return model;
        },
        
        /**
         * Run a model with input
         * @param {Object} model - Model to run
         * @param {*} input - Input data
         * @returns {*} Model output
         */
        run: function(model, input) {
          if (!model) {
            throw new Prime.ValidationError('Model is required');
          }
          
          if (!model._running) {
            throw new Prime.InvalidOperationError('Model is not running', {
              context: { model: model.name || 'unnamed' }
            });
          }
          
          // Process input through the model's pipeline
          let data = input;
          
          // 1. Embed the input if embedding is available
          if (this.embedding && model.useEmbedding !== false) {
            data = this.embedding.embed(data);
          }
          
          // 2. Apply logic if available
          if (this.logic && model.useLogic !== false) {
            data = this.logic.apply(data);
          }
          
          // 3. Process with the model's own function
          if (typeof model.process === 'function') {
            data = model.process(data);
          } else if (typeof model === 'function') {
            data = model(data);
          }
          
          // 4. Represent the output if representation is available
          if (this.representation && model.useRepresentation !== false && model.outputFormat) {
            data = this.representation.represent(data, model.outputFormat);
          }
          
          // Publish event
          Prime.EventBus.publish('model:ran', { 
            model, 
            input, 
            output: data 
          });
          
          return data;
        },
        
        /**
         * Stop a model
         * @param {Object} model - Model to stop
         * @returns {boolean} Success
         */
        stop: function(model) {
          if (!model) {
            throw new Prime.ValidationError('Model is required');
          }
          
          // Set the model's status to not running
          model._running = false;
          
          // Clean up resources if necessary
          if (typeof model.cleanup === 'function') {
            model.cleanup();
          }
          
          // Publish event
          Prime.EventBus.publish('model:stopped', { model });
          
          return true;
        },
        
        /**
         * Connect to Base 0 components
         * @param {Object} base0 - Base 0 components
         * @returns {Object} Connected runtime model
         */
        connectToBase0: function(base0) {
          this.embedding = base0.embedding;
          this.logic = base0.logic;
          this.representation = base0.representation;
          this.processor = base0.processor;
          
          return this;
        }
      };
    },
    
    /**
     * Create an observation model
     * @param {Object} config - Configuration object
     * @returns {Object} Observation model
     */
    createObservationModel: function(config = {}) {
      return {
        type: 'observation',
        sources: config.sources || [],
        filters: config.filters || [],
        name: config.name || 'ObservationModel',
        
        /**
         * Resolve a reference to an object
         * @param {Object|string} reference - Reference to resolve
         * @returns {*} Resolved object
         */
        resolve: function(reference) {
          // Handle UOR references
          if (Prime.UOR && Prime.UOR.isReference(reference)) {
            // This is a placeholder - in a real implementation, we would
            // have a way to map references to concrete objects
            return null;
          }
          
          // Handle string identifiers
          if (typeof reference === 'string') {
            // Look for a source with this identifier
            const source = this.sources.find(s => s.id === reference);
            
            if (source) {
              return source.data;
            }
          }
          
          return null;
        },
        
        /**
         * Fetch data matching a query
         * @param {Object} query - Query to execute
         * @returns {Array} Matching data
         */
        fetch: function(query) {
          if (!query) {
            return [];
          }
          
          let results = [];
          
          // Gather data from all sources
          for (const source of this.sources) {
            if (typeof source.query === 'function') {
              const sourceResults = source.query(query);
              
              if (Array.isArray(sourceResults)) {
                results = results.concat(sourceResults);
              }
            } else if (Array.isArray(source.data)) {
              // Simple filtering for array data
              const filtered = source.data.filter(item => {
                if (typeof query === 'function') {
                  return query(item);
                }
                
                // Default: match all properties in query
                for (const key in query) {
                  if (item[key] !== query[key]) {
                    return false;
                  }
                }
                
                return true;
              });
              
              results = results.concat(filtered);
            }
          }
          
          // Apply filters in sequence
          for (const filter of this.filters) {
            if (typeof filter === 'function') {
              results = filter(results, query);
            } else if (filter && typeof filter.apply === 'function') {
              results = filter.apply(results, query);
            }
          }
          
          return results;
        },
        
        /**
         * Observe a data source
         * @param {string} sourceId - Source identifier
         * @param {Object} options - Observation options
         * @returns {Object} Subscription object
         */
        observe: function(sourceId, options = {}) {
          const source = this.sources.find(s => s.id === sourceId);
          
          if (!source) {
            throw new Prime.InvalidOperationError(`Source ${sourceId} not found`, {
              context: { availableSources: this.sources.map(s => s.id) }
            });
          }
          
          if (typeof source.subscribe !== 'function') {
            throw new Prime.InvalidOperationError(`Source ${sourceId} does not support subscription`);
          }
          
          return source.subscribe(options);
        },
        
        /**
         * Add a data source
         * @param {Object} source - Data source to add
         * @returns {Object} Updated observation model
         */
        addSource: function(source) {
          if (!source.id) {
            throw new Prime.ValidationError('Source must have an id property');
          }
          
          this.sources.push(source);
          return this;
        },
        
        /**
         * Add a filter
         * @param {Function|Object} filter - Filter to add
         * @returns {Object} Updated observation model
         */
        addFilter: function(filter) {
          this.filters.push(filter);
          return this;
        },
        
        /**
         * Connect to Base 0 components
         * @param {Object} base0 - Base 0 components
         * @returns {Object} Connected observation model
         */
        connectToBase0: function(base0) {
          this._base0 = base0;
          return this;
        }
      };
    },
    
    /**
     * Create an interaction model
     * @param {Object} config - Configuration object
     * @returns {Object} Interaction model
     */
    createInteractionModel: function(config = {}) {
      return {
        type: 'interaction',
        mutations: config.mutations || [],
        validators: config.validators || [],
        name: config.name || 'InteractionModel',
        
        /**
         * Apply a mutation to an object
         * @param {*} object - Object to mutate
         * @param {string} mutation - Mutation name
         * @param {*} [payload] - Mutation payload
         * @returns {*} Mutated object
         */
        mutate: function(object, mutation, payload) {
          const mutator = this.mutations.find(m => m.name === mutation);
          
          if (!mutator) {
            throw new Prime.InvalidOperationError(`Mutation ${mutation} not found`, {
              context: { availableMutations: this.mutations.map(m => m.name) }
            });
          }
          
          let result;
          
          if (typeof mutator.apply === 'function') {
            result = mutator.apply(object, payload);
          } else if (typeof mutator === 'function') {
            result = mutator(object, payload);
          } else {
            throw new Prime.InvalidOperationError(`Invalid mutation ${mutation}`);
          }
          
          // Validate the result
          this.validate(result);
          
          // Publish event
          Prime.EventBus.publish('object:mutated', { 
            original: object, 
            mutation, 
            payload, 
            result 
          });
          
          return result;
        },
        
        /**
         * Save an object
         * @param {*} object - Object to save
         * @returns {boolean} Success
         */
        save: function(object) {
          // Validate object before saving
          this.validate(object);
          
          // In a real implementation, this would persist the object
          // For now, just publish an event
          Prime.EventBus.publish('object:saved', { object });
          
          return true;
        },
        
        /**
         * Validate an object
         * @param {*} object - Object to validate
         * @returns {boolean} Validation result
         * @throws {ValidationError} If validation fails
         */
        validate: function(object) {
          const failures = [];
          
          for (const validator of this.validators) {
            try {
              let valid = false;
              
              if (typeof validator === 'function') {
                valid = validator(object);
              } else if (validator && typeof validator.validate === 'function') {
                valid = validator.validate(object);
              } else {
                throw new Prime.InvalidOperationError('Invalid validator');
              }
              
              if (!valid) {
                failures.push(validator.name || 'anonymous validator');
              }
            } catch (error) {
              failures.push(`Error in ${validator.name || 'anonymous validator'}: ${error.message}`);
            }
          }
          
          if (failures.length > 0) {
            throw new Prime.ValidationError('Object validation failed', {
              context: { failures }
            });
          }
          
          return true;
        },
        
        /**
         * Add a mutation
         * @param {Object|Function} mutation - Mutation to add
         * @returns {Object} Updated interaction model
         */
        addMutation: function(mutation) {
          if (!mutation.name && typeof mutation !== 'function') {
            throw new Prime.ValidationError('Mutation must have a name property or be a function');
          }
          
          this.mutations.push(mutation);
          return this;
        },
        
        /**
         * Add a validator
         * @param {Object|Function} validator - Validator to add
         * @returns {Object} Updated interaction model
         */
        addValidator: function(validator) {
          this.validators.push(validator);
          return this;
        },
        
        /**
         * Connect to Base 0 components
         * @param {Object} base0 - Base 0 components
         * @returns {Object} Connected interaction model
         */
        connectToBase0: function(base0) {
          this._base0 = base0;
          return this;
        }
      };
    },
    
    /**
     * Create a representation model
     * @param {Object} config - Configuration object
     * @returns {Object} Representation model
     */
    createRepresentationModel: function(config = {}) {
      return {
        type: 'representation',
        renderers: config.renderers || [],
        name: config.name || 'RepresentationModel',
        
        /**
         * Present an object in a specified format
         * @param {*} object - Object to present
         * @param {string} format - Format name
         * @returns {*} Presented object
         */
        present: function(object, format) {
          // Check if this model has a Base 0 representation model
          if (this._base0 && this._base0.representation) {
            // Use the Base 0 representation model if it supports this format
            if (this._base0.representation.formats && this._base0.representation.formats[format]) {
              return this._base0.representation.represent(object, format);
            }
          }
          
          // Otherwise, use a simple conversion
          if (format === 'string') {
            return String(object);
          } else if (format === 'json') {
            return JSON.stringify(object);
          } else if (format === 'html') {
            // Simple HTML representation
            if (typeof object === 'string') {
              return `<div>${object}</div>`;
            } else if (Array.isArray(object)) {
              return `<ul>${object.map(item => `<li>${this.present(item, 'string')}</li>`).join('')}</ul>`;
            } else if (typeof object === 'object' && object !== null) {
              return `<dl>${Object.entries(object).map(([key, value]) => 
                `<dt>${key}</dt><dd>${this.present(value, 'string')}</dd>`
              ).join('')}</dl>`;
            } else {
              return `<div>${String(object)}</div>`;
            }
          }
          
          throw new Prime.InvalidOperationError(`Format ${format} not supported`);
        },
        
        /**
         * Render an object to a target
         * @param {*} object - Object to render
         * @param {*} target - Render target
         * @returns {*} Render result
         */
        render: function(object, target) {
          // Find a suitable renderer
          const renderer = this.renderers.find(r => r.canRender(object, target));
          
          if (!renderer) {
            throw new Prime.InvalidOperationError('No suitable renderer found', {
              context: { 
                objectType: typeof object,
                targetType: typeof target
              }
            });
          }
          
          return renderer.render(object, target);
        },
        
        /**
         * Add a renderer
         * @param {Object} renderer - Renderer to add
         * @returns {Object} Updated representation model
         */
        addRenderer: function(renderer) {
          if (typeof renderer.canRender !== 'function' || typeof renderer.render !== 'function') {
            throw new Prime.ValidationError('Renderer must have canRender and render methods');
          }
          
          this.renderers.push(renderer);
          return this;
        },
        
        /**
         * Connect to Base 0 components
         * @param {Object} base0 - Base 0 components
         * @returns {Object} Connected representation model
         */
        connectToBase0: function(base0) {
          this._base0 = base0;
          return this;
        }
      };
    },
    
    /**
     * Connect to Base 0
     * @param {Object} base0Components - Base 0 components
     * @returns {Object} Connected Base 1 resources
     */
    connectToBase0: function(base0Components) {
      return {
        runtime: this.createRuntimeModel({}).connectToBase0(base0Components),
        observation: this.createObservationModel({}).connectToBase0(base0Components),
        interaction: this.createInteractionModel({}).connectToBase0(base0Components),
        representation: this.createRepresentationModel({}).connectToBase0(base0Components)
      };
    }
  };

  /**
   * Base 2: Kernel
   * Orchestrator of the system
   */
  const Base2 = {
    /**
     * Create a resource client
     * @param {Object} config - Configuration object
     * @returns {Object} Resource client
     */
    createResourceClient: function(config = {}) {
      return {
        type: 'resourceClient',
        runtime: config.runtime,
        observation: config.observation,
        interaction: config.interaction,
        representation: config.representation,
        name: config.name || 'ResourceClient',
        
        /**
         * Get the runtime model
         * @returns {Object} Runtime model
         */
        getRuntime: function() {
          return this.runtime;
        },
        
        /**
         * Get the observation model
         * @returns {Object} Observation model
         */
        getObservation: function() {
          return this.observation;
        },
        
        /**
         * Get the interaction model
         * @returns {Object} Interaction model
         */
        getInteraction: function() {
          return this.interaction;
        },
        
        /**
         * Get the representation model
         * @returns {Object} Representation model
         */
        getRepresentation: function() {
          return this.representation;
        },
        
        /**
         * Start a model
         * @param {Object} model - Model to start
         * @returns {Object} Started model
         */
        startModel: function(model) {
          return this.runtime.start(model);
        },
        
        /**
         * Run a model
         * @param {Object} model - Model to run
         * @param {*} input - Input data
         * @returns {*} Model output
         */
        runModel: function(model, input) {
          return this.runtime.run(model, input);
        },
        
        /**
         * Stop a model
         * @param {Object} model - Model to stop
         * @returns {boolean} Success
         */
        stopModel: function(model) {
          return this.runtime.stop(model);
        },
        
        /**
         * Fetch data
         * @param {Object} query - Query to execute
         * @returns {Array} Matching data
         */
        fetchData: function(query) {
          return this.observation.fetch(query);
        },
        
        /**
         * Mutate an object
         * @param {*} object - Object to mutate
         * @param {string} mutation - Mutation name
         * @param {*} [payload] - Mutation payload
         * @returns {*} Mutated object
         */
        mutateObject: function(object, mutation, payload) {
          return this.interaction.mutate(object, mutation, payload);
        },
        
        /**
         * Save an object
         * @param {*} object - Object to save
         * @returns {boolean} Success
         */
        saveObject: function(object) {
          return this.interaction.save(object);
        },
        
        /**
         * Present an object
         * @param {*} object - Object to present
         * @param {string} format - Format name
         * @returns {*} Presented object
         */
        presentObject: function(object, format) {
          return this.representation.present(object, format);
        },
        
        /**
         * Render an object
         * @param {*} object - Object to render
         * @param {*} target - Render target
         * @returns {*} Render result
         */
        renderObject: function(object, target) {
          return this.representation.render(object, target);
        }
      };
    },
    
    /**
     * Create an application manager
     * @param {Object} config - Configuration object
     * @returns {Object} Application manager
     */
    createApplicationManager: function(config = {}) {
      return {
        type: 'applicationManager',
        bundles: config.bundles || [],
        resourceClient: config.resourceClient,
        name: config.name || 'ApplicationManager',
        _runningApps: {},
        
        /**
         * Load an application bundle
         * @param {Object} bundle - Bundle to load
         * @returns {boolean} Success
         */
        loadBundle: function(bundle) {
          if (!bundle || !bundle.id) {
            throw new Prime.ValidationError('Bundle must have an id property');
          }
          
          // Check if bundle is already loaded
          if (this.bundles.some(b => b.id === bundle.id)) {
            throw new Prime.InvalidOperationError(`Bundle ${bundle.id} is already loaded`);
          }
          
          this.bundles.push(bundle);
          
          // Publish event
          Prime.EventBus.publish('bundle:loaded', { bundle });
          
          return true;
        },
        
        /**
         * Unload an application bundle
         * @param {string} bundleId - Bundle identifier
         * @returns {boolean} Success
         */
        unloadBundle: function(bundleId) {
          const index = this.bundles.findIndex(b => b.id === bundleId);
          
          if (index === -1) {
            throw new Prime.InvalidOperationError(`Bundle ${bundleId} not found`);
          }
          
          // Check if any running applications use this bundle
          for (const appId in this._runningApps) {
            if (this._runningApps[appId].bundle.id === bundleId) {
              throw new Prime.InvalidOperationError(
                `Cannot unload bundle ${bundleId} while application ${appId} is running`
              );
            }
          }
          
          const bundle = this.bundles[index];
          this.bundles.splice(index, 1);
          
          // Publish event
          Prime.EventBus.publish('bundle:unloaded', { bundle });
          
          return true;
        },
        
        /**
         * Get an application bundle
         * @param {string} bundleId - Bundle identifier
         * @returns {Object} Application bundle
         */
        getBundle: function(bundleId) {
          const bundle = this.bundles.find(b => b.id === bundleId);
          
          if (!bundle) {
            throw new Prime.InvalidOperationError(`Bundle ${bundleId} not found`);
          }
          
          return bundle;
        },
        
        /**
         * Start an application
         * @param {string} bundleId - Bundle identifier
         * @param {Object} [options] - Application options
         * @returns {Object} Running application
         */
        startApplication: function(bundleId, options = {}) {
          const bundle = this.getBundle(bundleId);
          
          // Create application instance
          const appId = options.appId || `${bundleId}-${Prime.Utils.uuid().substring(0, 8)}`;
          
          if (this._runningApps[appId]) {
            throw new Prime.InvalidOperationError(`Application ${appId} is already running`);
          }
          
          // Initialize application
          const app = {
            id: appId,
            bundle,
            state: Prime.Utils.deepClone(bundle.initialState || {}),
            options,
            startTime: Date.now()
          };
          
          // Start any models required by the application
          if (this.resourceClient && bundle.models) {
            app.models = {};
            
            for (const modelId in bundle.models) {
              const model = bundle.models[modelId];
              app.models[modelId] = this.resourceClient.startModel(model);
            }
          }
          
          // Register running application
          this._runningApps[appId] = app;
          
          // Publish event
          Prime.EventBus.publish('application:started', { app });
          
          return app;
        },
        
        /**
         * Stop an application
         * @param {string} appId - Application identifier
         * @returns {boolean} Success
         */
        stopApplication: function(appId) {
          const app = this._runningApps[appId];
          
          if (!app) {
            throw new Prime.InvalidOperationError(`Application ${appId} not found`);
          }
          
          // Stop any models used by the application
          if (this.resourceClient && app.models) {
            for (const modelId in app.models) {
              this.resourceClient.stopModel(app.models[modelId]);
            }
          }
          
          // Unregister running application
          delete this._runningApps[appId];
          
          // Publish event
          Prime.EventBus.publish('application:stopped', { app });
          
          return true;
        },
        
        /**
         * Get a running application
         * @param {string} appId - Application identifier
         * @returns {Object} Running application
         */
        getApplication: function(appId) {
          const app = this._runningApps[appId];
          
          if (!app) {
            throw new Prime.InvalidOperationError(`Application ${appId} not found`);
          }
          
          return app;
        },
        
        /**
         * Get all running applications
         * @returns {Object} Map of running applications
         */
        getRunningApplications: function() {
          return { ...this._runningApps };
        }
      };
    },
    
    /**
     * Create a system manager
     * @param {Object} config - Configuration object
     * @returns {Object} System manager
     */
    createSystemManager: function(config = {}) {
      return {
        type: 'systemManager',
        security: config.security || {},
        memory: config.memory || {},
        name: config.name || 'SystemManager',
        _resources: {},
        
        /**
         * Allocate memory
         * @param {number} size - Size to allocate
         * @returns {Object} Allocated memory
         */
        allocateMemory: function(size) {
          if (!Prime.Utils.isNumber(size) || size <= 0) {
            throw new Prime.ValidationError('Size must be a positive number');
          }
          
          // In a real implementation, this would actually allocate memory
          // For now, just log and return a mock allocation
          
          const address = Prime.Utils.uuid();
          
          this._resources[address] = {
            type: 'memory',
            size,
            allocated: Date.now()
          };
          
          return { address, size };
        },
        
        /**
         * Free memory
         * @param {string} address - Memory address
         * @returns {boolean} Success
         */
        freeMemory: function(address) {
          if (!this._resources[address] || this._resources[address].type !== 'memory') {
            throw new Prime.InvalidOperationError(`Invalid memory address: ${address}`);
          }
          
          delete this._resources[address];
          return true;
        },
        
        /**
         * Check if an operation is permitted
         * @param {string} operation - Operation name
         * @param {Object} context - Operation context
         * @returns {boolean} True if operation is permitted
         */
        checkPermission: function(operation, context = {}) {
          // In a real implementation, this would check against a security policy
          // For now, just check if the operation is allowed
          
          if (this.security.policy && this.security.policy[operation]) {
            const policy = this.security.policy[operation];
            
            if (typeof policy === 'function') {
              return policy(context);
            } else if (typeof policy === 'boolean') {
              return policy;
            }
          }
          
          // Default to permissive policy
          return true;
        },
        
        /**
         * Allocate a resource
         * @param {string} type - Resource type
         * @param {Object} config - Resource configuration
         * @returns {Object} Allocated resource
         */
        allocateResource: function(type, config = {}) {
          // Check permission
          if (!this.checkPermission('allocateResource', { type, config })) {
            throw new Prime.InvalidOperationError(`Permission denied: allocateResource ${type}`);
          }
          
          const address = Prime.Utils.uuid();
          
          this._resources[address] = {
            type,
            config,
            allocated: Date.now()
          };
          
          return { address, type, config };
        },
        
        /**
         * Free a resource
         * @param {string} address - Resource address
         * @returns {boolean} Success
         */
        freeResource: function(address) {
          if (!this._resources[address]) {
            throw new Prime.InvalidOperationError(`Invalid resource address: ${address}`);
          }
          
          // Check permission
          if (!this.checkPermission('freeResource', { address, resource: this._resources[address] })) {
            throw new Prime.InvalidOperationError(`Permission denied: freeResource ${address}`);
          }
          
          delete this._resources[address];
          return true;
        },
        
        /**
         * Get resource usage
         * @returns {Object} Resource usage statistics
         */
        getResourceUsage: function() {
          // Check permission
          if (!this.checkPermission('getResourceUsage', {})) {
            throw new Prime.InvalidOperationError('Permission denied: getResourceUsage');
          }
          
          const stats = {
            memory: {
              count: 0,
              totalSize: 0
            },
            byType: {}
          };
          
          for (const address in this._resources) {
            const resource = this._resources[address];
            
            // Count by type
            if (!stats.byType[resource.type]) {
              stats.byType[resource.type] = {
                count: 0
              };
            }
            
            stats.byType[resource.type].count++;
            
            // Special handling for memory
            if (resource.type === 'memory') {
              stats.memory.count++;
              stats.memory.totalSize += resource.size;
            }
          }
          
          return stats;
        }
      };
    },
    
    // Syscall registry
    syscalls: {},
    
    /**
     * Register syscalls
     * @param {Array} syscalls - Syscalls to register
     */
    registerSyscalls: function(syscalls) {
      for (const syscall of syscalls) {
        if (!syscall.name || typeof syscall.handler !== 'function') {
          throw new Prime.ValidationError('Syscall must have a name and handler function');
        }
        
        this.syscalls[syscall.name] = syscall.handler;
      }
    },
    
    /**
     * Execute a syscall
     * @param {string} name - Syscall name
     * @param  {...any} args - Syscall arguments
     * @returns {*} Syscall result
     */
    syscall: function(name, ...args) {
      if (!this.syscalls[name]) {
        throw new Prime.InvalidOperationError(`Syscall ${name} not found`);
      }
      
      return this.syscalls[name](...args);
    },
    
    /**
     * Connect to Base 1
     * @param {Object} base1Resources - Base 1 resources
     * @returns {Object} Connected Base 2 components
     */
    connectToBase1: function(base1Resources) {
      const resourceClient = this.createResourceClient({
        runtime: base1Resources.runtime,
        observation: base1Resources.observation,
        interaction: base1Resources.interaction,
        representation: base1Resources.representation
      });
      
      const applicationManager = this.createApplicationManager({
        resourceClient
      });
      
      const systemManager = this.createSystemManager({});
      
      return {
        resourceClient,
        applicationManager,
        systemManager
      };
    }
  };

  /**
   * Base 3: Application
   * User-space applications
   */
  const Base3 = {
    /**
     * Create an application
     * @param {Object} config - Application configuration
     * @returns {Object} Application
     */
    createApplication: function(config = {}) {
      // Validate configuration
      if (!config.name) {
        throw new Prime.ValidationError('Application must have a name');
      }
      
      if (!config.behavior || !config.behavior.actions) {
        throw new Prime.ValidationError('Application must have behavior.actions defined');
      }
      
      // Create application object
      const app = {
        name: config.name,
        id: config.id || Prime.Utils.uuid(),
        
        // Behavior model (like JavaScript)
        behavior: {
          actions: config.behavior.actions || {},
          initialState: Prime.Utils.deepClone(config.behavior.initialState || {}),
          state: Prime.Utils.deepClone(config.behavior.initialState || {}),
          
          /**
           * Dispatch an action
           * @param {string} action - Action name
           * @param {*} payload - Action payload
           * @returns {Object} Updated state
           */
          dispatch: function(action, payload) {
            if (!this.actions[action]) {
              throw new Prime.InvalidOperationError(`Action ${action} not found`, {
                context: { availableActions: Object.keys(this.actions) }
              });
            }
            
            // Check if this action requires kernel support
            if (this._kernel && this._kernelActions && this._kernelActions[action]) {
              return this._kernelActions[action](payload);
            }
            
            // Execute the action
            let actionFn = this.actions[action];
            
            // Handle actions that are objects with apply method
            if (typeof actionFn !== 'function' && actionFn && typeof actionFn.apply === 'function') {
              actionFn = actionFn.apply.bind(actionFn);
            }
            
            if (typeof actionFn !== 'function') {
              throw new Prime.InvalidOperationError(`Action ${action} is not executable`);
            }
            
            const nextState = actionFn(this.state, payload);
            
            // Validate the next state
            if (nextState === undefined || nextState === null) {
              throw new Prime.InvalidOperationError(`Action ${action} returned invalid state`);
            }
            
            // Check coherence constraints
            if (app.coherenceConstraints && app.coherenceConstraints.length > 0) {
              for (const constraint of app.coherenceConstraints) {
                if (!constraint.check(nextState)) {
                  if (constraint.type === 'hard') {
                    throw new Prime.CoherenceViolationError(
                      `Action ${action} violates coherence constraint "${constraint.name}"`,
                      constraint,
                      1.0,
                      { object: nextState }
                    );
                  }
                  
                  // For soft constraints, just log a warning
                  Prime.Logger.warn(`Action ${action} violates soft constraint "${constraint.name}"`);
                }
              }
            }
            
            // Update state
            this.state = { ...this.state, ...nextState };
            
            // Trigger update
            app.update();
            
            return this.state;
          },
          
          /**
           * Get the current state
           * @returns {Object} Current state
           */
          getState: function() {
            return Prime.Utils.deepClone(this.state);
          },
          
          /**
           * Reset state to initial state
           * @returns {Object} Reset state
           */
          resetState: function() {
            this.state = Prime.Utils.deepClone(this.initialState);
            app.update();
            return this.state;
          }
        },
        
        // Framework model (like CSS)
        framework: {
          layout: config.framework?.layout || 'default',
          styling: config.framework?.styling || {},
          animations: config.framework?.animations || {},
          
          /**
           * Get style for a component
           * @param {string} component - Component name
           * @returns {Object} Component style
           */
          getStyle: function(component) {
            return this.styling[component] || {};
          },
          
          /**
           * Apply layout to a container
           * @param {Object} container - Container to apply layout to
           */
          applyLayout: function(container) {
            if (!container) return;
            
            // Ensure container has a style property
            container.style = container.style || {};
            
            // Apply layout
            if (this.layout === 'flex') {
              container.style.display = 'flex';
            } else if (this.layout === 'grid') {
              container.style.display = 'grid';
            } else {
              container.style.display = 'block';
            }
          },
          
          /**
           * Apply an animation
           * @param {Object} element - Element to animate
           * @param {string} animation - Animation name
           * @returns {boolean} Success
           */
          animate: function(element, animation) {
            const anim = this.animations[animation];
            
            if (!anim) {
              throw new Prime.InvalidOperationError(`Animation ${animation} not found`, {
                context: { availableAnimations: Object.keys(this.animations) }
              });
            }
            
            // Apply animation to element
            if (typeof anim === 'function') {
              return anim(element);
            } else if (anim && typeof anim.apply === 'function') {
              return anim.apply(element);
            }
            
            return false;
          }
        },
        
        // Structure model (like HTML)
        structure: {
          components: config.structure?.components || [],
          
          /**
           * Create a component
           * @param {string} type - Component type
           * @param {Object} props - Component properties
           * @param {Array} [children] - Component children
           * @returns {Object} New component
           */
          createComponent: function(type, props, children) {
            return {
              type,
              props: props || {},
              children: children || []
            };
          },
          
          /**
           * Find a component by ID
           * @param {string} id - Component ID
           * @returns {Object} Found component or null
           */
          findComponent: function(id) {
            const find = (components) => {
              for (const component of components) {
                if (component.props && component.props.id === id) {
                  return component;
                }
                
                if (component.children && component.children.length > 0) {
                  const found = find(component.children);
                  
                  if (found) {
                    return found;
                  }
                }
              }
              
              return null;
            };
            
            return find(this.components);
          },
          
          /**
           * Add a component
           * @param {Object} component - Component to add
           * @param {string} [parentId] - Parent component ID
           * @returns {boolean} Success
           */
          addComponent: function(component, parentId) {
            if (!component.type) {
              throw new Prime.ValidationError('Component must have a type');
            }
            
            if (!parentId) {
              // Add to root
              this.components.push(component);
              return true;
            }
            
            // Find parent component
            const parent = this.findComponent(parentId);
            
            if (!parent) {
              throw new Prime.InvalidOperationError(`Parent component ${parentId} not found`);
            }
            
            // Add to parent
            parent.children = parent.children || [];
            parent.children.push(component);
            
            return true;
          },
          
          /**
           * Remove a component
           * @param {string} id - Component ID
           * @returns {boolean} Success
           */
          removeComponent: function(id) {
            const removeFrom = (components) => {
              for (let i = 0; i < components.length; i++) {
                if (components[i].props && components[i].props.id === id) {
                  components.splice(i, 1);
                  return true;
                }
                
                if (components[i].children && components[i].children.length > 0) {
                  if (removeFrom(components[i].children)) {
                    return true;
                  }
                }
              }
              
              return false;
            };
            
            return removeFrom(this.components);
          }
        },
        
        // Coherence constraints
        coherenceConstraints: config.coherenceConstraints || [],
        
        // Application state
        _isRunning: false,
        _container: null,
        _kernel: null,
        _kernelActions: {},
        
        /**
         * Start the application
         * @returns {boolean} Success
         */
        start: function() {
          this._isRunning = true;
          this.update();
          
          // Publish event
          Prime.EventBus.publish('application:started', { app: this });
          
          return true;
        },
        
        /**
         * Stop the application
         * @returns {boolean} Success
         */
        stop: function() {
          this._isRunning = false;
          
          // Publish event
          Prime.EventBus.publish('application:stopped', { app: this });
          
          return true;
        },
        
        /**
         * Update the application
         * @returns {boolean} Success
         */
        update: function() {
          if (!this._isRunning) {
            return false;
          }
          
          if (!this._container) {
            return false;
          }
          
          // Render application to container
          this._renderComponents();
          
          // Publish event
          Prime.EventBus.publish('application:updated', { app: this });
          
          return true;
        },
        
        /**
         * Mount the application to a container
         * @param {Object} container - Container to mount to
         * @returns {boolean} Success
         */
        mount: function(container) {
          this._container = container;
          this.update();
          
          return true;
        },
        
        /**
         * Unmount the application
         * @returns {boolean} Success
         */
        unmount: function() {
          this._container = null;
          return true;
        },
        
        /**
         * Use a kernel service
         * @param {string} service - Service name
         * @param  {...any} args - Service arguments
         * @returns {*} Service result
         */
        useKernel: function(service, ...args) {
          if (!this._kernel) {
            throw new Prime.InvalidOperationError('No kernel available');
          }
          
          const resourceClient = this._kernel.resourceClient;
          
          if (!resourceClient) {
            throw new Prime.InvalidOperationError('No resource client available');
          }
          
          // Handle common services
          if (service === 'fetchData') {
            return resourceClient.fetchData(...args);
          } else if (service === 'saveObject') {
            return resourceClient.saveObject(...args);
          } else if (service === 'mutateObject') {
            return resourceClient.mutateObject(...args);
          } else if (service === 'startModel') {
            return resourceClient.startModel(...args);
          } else if (service === 'runModel') {
            return resourceClient.runModel(...args);
          } else if (service === 'stopModel') {
            return resourceClient.stopModel(...args);
          } else if (service === 'present') {
            return resourceClient.presentObject(...args);
          } else if (service === 'render') {
            return resourceClient.renderObject(...args);
          }
          
          // Try to execute as syscall
          if (this._kernel.syscall) {
            return this._kernel.syscall(service, ...args);
          }
          
          throw new Prime.InvalidOperationError(`Service ${service} not found`);
        },
        
        /**
         * Connect to kernel components
         * @param {Object} kernelComponents - Kernel components
         * @returns {Object} Connected application
         */
        connectToKernel: function(kernelComponents) {
          this._kernel = kernelComponents;
          
          // Set up kernel-supported actions
          this._kernelActions = {
            fetchData: (query) => {
              const data = this.useKernel('fetchData', query);
              return { fetchedData: data, lastFetchTime: Date.now() };
            },
            saveData: (payload) => {
              const success = this.useKernel('saveObject', payload.data);
              return { saveSuccess: success, lastSaveTime: Date.now() };
            }
          };
          
          return this;
        },
        
        /**
         * Render components to the container
         * @private
         */
        _renderComponents: function() {
          if (!this._container) return;
          
          // Clear container
          this._container.innerHTML = '';
          
          // Apply layout
          this.framework.applyLayout(this._container);
          
          // Safe appendChild function for both real DOM and mock environments
          const safeAppendChild = (parent, element) => {
            if (parent.appendChild && typeof parent.appendChild === 'function') {
              // Real DOM environment
              parent.appendChild(element);
            } else {
              // Mock environment for testing
              if (!parent._children) parent._children = [];
              parent._children.push(element);
              
              // For test visibility, also update innerHTML if available
              if (parent.innerHTML !== undefined) {
                if (element.outerHTML) {
                  parent.innerHTML += element.outerHTML;
                } else {
                  // Simple text representation
                  parent.innerHTML += `<${element.type || 'div'}>${element.textContent || ''}</${element.type || 'div'}>`;
                }
              }
            }
          };
          
          // Render components
          const render = (component, parent) => {
            let element;
            
            // Create DOM element or mock in test environment
            if (typeof document !== 'undefined' && document.createElement) {
              // Browser environment
              element = document.createElement(component.type || 'div');
              
              // Apply props
              for (const [key, value] of Object.entries(component.props || {})) {
                if (key === 'className') {
                  element.className = value;
                } else if (key === 'innerText') {
                  if (Prime.Utils.isFunction(value)) {
                    element.innerText = value(this.behavior.state);
                  } else {
                    element.innerText = value;
                  }
                } else if (key === 'onClick') {
                  element.addEventListener('click', () => {
                    this.behavior.dispatch(value);
                  });
                } else if (key !== 'id') {
                  element.setAttribute(key, value);
                }
              }
              
              // Apply styles
              const styles = this.framework.getStyle(component.props?.className);
              for (const [key, value] of Object.entries(styles || {})) {
                element.style[key] = value;
              }
            } else {
              // Test environment
              element = {
                type: component.type || 'div',
                props: { ...component.props },
                children: [],
                textContent: ''
              };
              
              // Handle innerText
              if (component.props?.innerText) {
                if (Prime.Utils.isFunction(component.props.innerText)) {
                  element.textContent = component.props.innerText(this.behavior.state);
                } else {
                  element.textContent = component.props.innerText;
                }
              }
            }
            
            // Render children
            if (component.children) {
              for (const child of component.children) {
                render(child, element);
              }
            }
            
            // Add to parent
            safeAppendChild(parent, element);
          };
          
          // Render all root components
          for (const component of this.structure.components) {
            render(component, this._container);
          }
        }
      };
      
      return app;
    },
    
    /**
     * Connect to Base 2
     * @param {Object} kernelComponents - Kernel components
     * @returns {Object} Connected Base 3 interface
     */
    connectToBase2: function(kernelComponents) {
      return {
        /**
         * Create an application with kernel integration
         * @param {Object} config - Application configuration
         * @returns {Object} Application with kernel integration
         */
        createApplication: (config) => {
          const app = this.createApplication(config);
          
          // Connect application to kernel
          app.connectToKernel(kernelComponents);
          
          return app;
        }
      };
    }
  };

  /**
   * Create a fully integrated Prime Framework instance
   * @param {Object} config - Framework configuration
   * @returns {Object} Prime Framework instance
   */
  const createPrimeFramework = function(config = {}) {
    // Create and connect all components
    
    // Base 0: Neural Network Specification
    const base0 = Base0.createBase0Components(config.base0 || {});
    
    // Connect Base 0 to coherence
    Base0.connectToCoherence(base0);
    
    // Base 1: Resource - Connect to Base 0
    const base1 = Base1.connectToBase0(base0);
    
    // Base 2: Kernel - Connect to Base 1
    const base2 = Base2.connectToBase1(base1);
    
    // Base 3: Application - Connect to Base 2
    const base3 = Base3.connectToBase2(base2);
    
    // Create framework instance
    return {
      // Base components
      base0,
      base1,
      base2,
      base3,
      
      // Global coherence of the framework
      getCoherence: () => Prime.coherence.systemCoherence.calculateGlobalCoherence(),
      
      /**
       * Optimize global coherence
       * @param {Object} options - Optimization options
       * @returns {number} Optimized coherence norm
       */
      optimizeCoherence: (options = {}) => {
        return Prime.coherence.systemCoherence.optimizeGlobal(options);
      },
      
      /**
       * Create an application
       * @param {Object} config - Application configuration
       * @returns {Object} Application
       */
      createApplication: (config) => {
        const app = base3.createApplication(config);
        
        // Register with coherence system
        Prime.coherence.systemCoherence.register(app);
        
        return app;
      },
      
      /**
       * Start an application from a bundle
       * @param {string} bundleId - Bundle identifier
       * @param {Object} options - Application options
       * @returns {Object} Running application
       */
      startApplicationFromBundle: (bundleId, options = {}) => {
        return base2.applicationManager.startApplication(bundleId, options);
      },
      
      /**
       * Stop an application
       * @param {string} appId - Application identifier
       * @returns {boolean} Success
       */
      stopApplication: (appId) => {
        return base2.applicationManager.stopApplication(appId);
      },
      
      /**
       * Register a syscall
       * @param {Object} syscall - Syscall to register
       * @returns {boolean} Success
       */
      registerSyscall: (syscall) => {
        Base2.registerSyscalls([syscall]);
        return true;
      },
      
      /**
       * Execute a syscall
       * @param {string} name - Syscall name
       * @param  {...any} args - Syscall arguments
       * @returns {*} Syscall result
       */
      syscall: (name, ...args) => {
        return Base2.syscall(name, ...args);
      }
    };
  };

  // Extend Prime with framework capabilities
  Prime.Base0 = Base0;
  Prime.Base1 = Base1;
  Prime.Base2 = Base2;
  Prime.Base3 = Base3;
  Prime.createPrimeFramework = createPrimeFramework;
  
})(Prime);

// Export extended Prime
export { Prime };

// For CommonJS compatibility
if (typeof module !== 'undefined' && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== 'undefined') {
  window.Prime = Prime;
}
