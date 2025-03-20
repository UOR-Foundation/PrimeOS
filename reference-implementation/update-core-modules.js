/**
 * PrimeOS Core Modules Update
 * 
 * This script creates/updates the core visualization modules
 * and context sharing system modules needed for the browser tests
 */

const fs = require('fs');
const path = require('path');

// Ensure directories exist
function ensureDirectoryExists(dirPath) {
  if (!fs.existsSync(dirPath)) {
    fs.mkdirSync(dirPath, { recursive: true });
    console.log(`Created directory: ${dirPath}`);
  }
}

// Create the visualization module
function createVisualizationModule() {
  const dir = path.join(__dirname, 'core', 'visualization');
  const filePath = path.join(dir, 'topology-visualizer.js');
  
  ensureDirectoryExists(dir);
  
  const content = `/**
 * TopologyVisualizer - Visualizes manifold relationships using D3.js
 */

class TopologyVisualizer {
  constructor(options = {}) {
    this.container = options.container;
    this.manifoldRegistry = options.manifoldRegistry;
    this.eventBus = options.eventBus;
    this.options = Object.assign({
      width: 800,
      height: 600,
      nodeRadius: 20,
      linkDistance: 150,
      colors: {
        application: '#0066cc',
        component: '#28a745',
        module: '#fd7e14',
        default: '#6c757d'
      }
    }, options);
    
    this.nodes = [];
    this.links = [];
    this.simulation = null;
    this.svg = null;
    this.subscriptions = [];
  }
  
  async initialize() {
    if (!this.container) {
      throw new Error('Container element is required for TopologyVisualizer');
    }
    
    // Load D3.js if not already loaded
    await this._ensureD3Loaded();
    
    // Create SVG element
    this._createSvg();
    
    // Load initial data
    await this._loadData();
    
    // Set up event listeners
    this._setupEventListeners();
    
    // Start force simulation
    this._startSimulation();
    
    return this;
  }
  
  async _ensureD3Loaded() {
    // Check if D3 is loaded
    if (typeof d3 === 'undefined') {
      // If in browser, dynamically load D3
      if (typeof window !== 'undefined') {
        return new Promise((resolve, reject) => {
          const script = document.createElement('script');
          script.src = 'https://d3js.org/d3.v7.min.js';
          script.onload = resolve;
          script.onerror = reject;
          document.head.appendChild(script);
        });
      } else {
        // In Node.js, require D3
        throw new Error('D3.js is required but not loaded');
      }
    }
  }
  
  _createSvg() {
    // Create SVG element
    this.svg = d3.select(this.container)
      .append('svg')
      .attr('width', '100%')
      .attr('height', '100%')
      .attr('viewBox', \`0 0 \${this.options.width} \${this.options.height}\`)
      .attr('preserveAspectRatio', 'xMidYMid meet')
      .call(d3.zoom().on('zoom', (event) => {
        this.svg.select('g').attr('transform', event.transform);
      }));
    
    // Add arrow marker definition
    this.svg.append('defs').append('marker')
      .attr('id', 'arrowhead')
      .attr('viewBox', '0 -5 10 10')
      .attr('refX', 20)
      .attr('refY', 0)
      .attr('orient', 'auto')
      .attr('markerWidth', 6)
      .attr('markerHeight', 6)
      .append('path')
      .attr('d', 'M0,-5L10,0L0,5')
      .attr('fill', '#999');
    
    // Create container group for all elements
    this.svg.append('g');
  }
  
  async _loadData() {
    if (!this.manifoldRegistry) {
      console.warn('ManifoldRegistry not provided, using sample data');
      this._loadSampleData();
      return;
    }
    
    try {
      // Load manifolds
      const manifolds = await this.manifoldRegistry.getManifolds();
      
      // Create nodes from manifolds
      this.nodes = manifolds.map(manifold => {
        const meta = manifold.getMeta();
        const invariant = manifold.getInvariant();
        
        return {
          id: manifold.getId(),
          name: invariant.name || 'Unnamed',
          type: meta.type || 'default',
          meta: meta,
          invariant: invariant
        };
      });
      
      // Load relationships
      const relationships = await this.manifoldRegistry.getRelationships();
      
      // Create links from relationships
      this.links = relationships.map(rel => ({
        source: rel.sourceId,
        target: rel.targetId,
        type: rel.type,
        value: 1
      }));
    } catch (error) {
      console.error('Error loading data:', error);
      this._loadSampleData();
    }
  }
  
  _loadSampleData() {
    // Sample nodes
    this.nodes = [
      { id: 'app1', name: 'Application 1', type: 'application' },
      { id: 'app2', name: 'Application 2', type: 'application' },
      { id: 'component1', name: 'Component 1', type: 'component' },
      { id: 'component2', name: 'Component 2', type: 'component' },
      { id: 'module1', name: 'Module 1', type: 'module' }
    ];
    
    // Sample links
    this.links = [
      { source: 'app1', target: 'component1', type: 'uses', value: 1 },
      { source: 'app1', target: 'module1', type: 'imports', value: 1 },
      { source: 'app2', target: 'component2', type: 'uses', value: 1 },
      { source: 'component1', target: 'module1', type: 'uses', value: 1 }
    ];
  }
  
  _setupEventListeners() {
    if (this.eventBus) {
      // Subscribe to manifold created event
      this.subscriptions.push(
        this.eventBus.subscribe('manifold:created', (data) => {
          this._addNode(data.manifold);
          this._updateVisualization();
        })
      );
      
      // Subscribe to manifold deleted event
      this.subscriptions.push(
        this.eventBus.subscribe('manifold:deleted', (data) => {
          this._removeNode(data.manifoldId);
          this._updateVisualization();
        })
      );
      
      // Subscribe to relationship created event
      this.subscriptions.push(
        this.eventBus.subscribe('relationship:created', (data) => {
          this._addLink(data.relationship);
          this._updateVisualization();
        })
      );
      
      // Subscribe to relationship deleted event
      this.subscriptions.push(
        this.eventBus.subscribe('relationship:deleted', (data) => {
          this._removeLink(data.sourceId, data.targetId);
          this._updateVisualization();
        })
      );
    }
  }
  
  _startSimulation() {
    // Create force simulation
    this.simulation = d3.forceSimulation(this.nodes)
      .force('link', d3.forceLink(this.links).id(d => d.id).distance(this.options.linkDistance))
      .force('charge', d3.forceManyBody().strength(-300))
      .force('center', d3.forceCenter(this.options.width / 2, this.options.height / 2))
      .on('tick', () => this._tick());
    
    // Render initial visualization
    this._updateVisualization();
  }
  
  _updateVisualization() {
    const svg = this.svg.select('g');
    
    // Update links
    const link = svg.selectAll('.link')
      .data(this.links, d => \`\${d.source.id || d.source}-\${d.target.id || d.target}\`);
    
    // Remove old links
    link.exit().remove();
    
    // Add new links
    const linkEnter = link.enter().append('line')
      .attr('class', 'link')
      .attr('stroke', '#999')
      .attr('stroke-opacity', 0.6)
      .attr('marker-end', 'url(#arrowhead)');
    
    // Update nodes
    const node = svg.selectAll('.node')
      .data(this.nodes, d => d.id);
    
    // Remove old nodes
    node.exit().remove();
    
    // Add new nodes
    const nodeEnter = node.enter().append('g')
      .attr('class', 'node')
      .call(d3.drag()
        .on('start', (event, d) => this._dragStarted(event, d))
        .on('drag', (event, d) => this._dragged(event, d))
        .on('end', (event, d) => this._dragEnded(event, d)))
      .on('click', (event, d) => this._nodeClicked(event, d));
    
    // Add circle to nodes
    nodeEnter.append('circle')
      .attr('r', this.options.nodeRadius)
      .attr('fill', d => this.options.colors[d.type] || this.options.colors.default)
      .attr('stroke', '#fff')
      .attr('stroke-width', 1.5);
    
    // Add text to nodes
    nodeEnter.append('text')
      .attr('dy', '.35em')
      .attr('text-anchor', 'middle')
      .attr('fill', '#fff')
      .text(d => d.name);
    
    // Merge links
    this.linkElements = linkEnter.merge(link);
    
    // Merge nodes
    this.nodeElements = nodeEnter.merge(node);
    
    // Update simulation
    this.simulation.nodes(this.nodes);
    this.simulation.force('link').links(this.links);
    this.simulation.alpha(1).restart();
  }
  
  _tick() {
    // Update link positions
    if (this.linkElements) {
      this.linkElements
        .attr('x1', d => d.source.x)
        .attr('y1', d => d.source.y)
        .attr('x2', d => d.target.x)
        .attr('y2', d => d.target.y);
    }
    
    // Update node positions
    if (this.nodeElements) {
      this.nodeElements.attr('transform', d => \`translate(\${d.x},\${d.y})\`);
    }
  }
  
  _dragStarted(event, d) {
    if (!event.active) this.simulation.alphaTarget(0.3).restart();
    d.fx = d.x;
    d.fy = d.y;
  }
  
  _dragged(event, d) {
    d.fx = event.x;
    d.fy = event.y;
  }
  
  _dragEnded(event, d) {
    if (!event.active) this.simulation.alphaTarget(0);
    d.fx = null;
    d.fy = null;
  }
  
  _nodeClicked(event, d) {
    // Select/deselect node
    const isSelected = d3.select(event.currentTarget).classed('selected');
    
    // Clear previous selection
    this.svg.selectAll('.node').classed('selected', false);
    
    if (!isSelected) {
      // Select this node
      d3.select(event.currentTarget).classed('selected', true);
      
      // Publish node selected event
      if (this.eventBus) {
        this.eventBus.publish('topology:node-selected', { node: d });
      }
    } else {
      // Publish node deselected event
      if (this.eventBus) {
        this.eventBus.publish('topology:node-deselected', { node: d });
      }
    }
  }
  
  _addNode(manifold) {
    // Extract manifold data
    const id = manifold.id;
    const type = manifold.type || 'default';
    const name = manifold.name || 'Unnamed';
    
    // Check if node already exists
    if (this.nodes.find(n => n.id === id)) {
      return;
    }
    
    // Add new node
    this.nodes.push({ id, name, type, manifold });
  }
  
  _removeNode(id) {
    // Find node index
    const index = this.nodes.findIndex(n => n.id === id);
    
    if (index !== -1) {
      // Remove node
      this.nodes.splice(index, 1);
      
      // Remove related links
      this.links = this.links.filter(
        l => (l.source.id !== id && l.target.id !== id)
      );
    }
  }
  
  _addLink(relationship) {
    // Extract relationship data
    const sourceId = relationship.source;
    const targetId = relationship.target;
    const type = relationship.type || 'default';
    
    // Check if link already exists
    if (this.links.find(l => 
      (l.source.id === sourceId && l.target.id === targetId)
    )) {
      return;
    }
    
    // Add new link
    this.links.push({ 
      source: sourceId,
      target: targetId, 
      type,
      value: 1
    });
  }
  
  _removeLink(sourceId, targetId) {
    // Remove link
    this.links = this.links.filter(l => 
      !(l.source.id === sourceId && l.target.id === targetId)
    );
  }
  
  destroy() {
    // Unsubscribe from events
    if (this.eventBus) {
      this.subscriptions.forEach(unsubscribe => unsubscribe());
      this.subscriptions = [];
    }
    
    // Stop simulation
    if (this.simulation) {
      this.simulation.stop();
      this.simulation = null;
    }
    
    // Remove SVG
    if (this.svg) {
      this.svg.remove();
      this.svg = null;
    }
    
    // Clear data
    this.nodes = [];
    this.links = [];
  }
}

// CommonJS export
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { TopologyVisualizer };
} 

// ES module export
export { TopologyVisualizer };
`;
  
  fs.writeFileSync(filePath, content);
  console.log(`Created/updated: ${filePath}`);
}

// Create the context sharing module
function createContextSharingModule() {
  const dir = path.join(__dirname, 'core', 'context');
  const filePath = path.join(dir, 'context-sharing.js');
  const indexPath = path.join(dir, 'index.js');
  
  ensureDirectoryExists(dir);
  
  const content = `/**
 * Context Sharing System
 * 
 * Provides a mechanism for components to share context data with schema validation.
 */

class ContextHub {
  constructor(options = {}) {
    this.manifoldRegistry = options.manifoldRegistry;
    this.eventBus = options.eventBus;
    this.providers = new Map();
    this.consumers = new Map();
    this.connections = [];
    this.initialized = false;
  }
  
  async initialize() {
    if (this.initialized) return this;
    
    // Set up event listeners if event bus is provided
    if (this.eventBus) {
      this.eventBus.subscribe('context:provider-registered', (data) => {
        this._connectCompatibleConsumers(data.id, data.contextType);
      });
      
      this.eventBus.subscribe('context:consumer-registered', (data) => {
        this._connectCompatibleProviders(data.id, data.contextTypes);
      });
    }
    
    this.initialized = true;
    return this;
  }
  
  /**
   * Register a context provider
   */
  async registerProvider(options) {
    if (!options.id || !options.contextType) {
      throw new Error('Provider ID and context type are required');
    }
    
    // Create provider
    const provider = new ContextProvider({
      id: options.id,
      contextType: options.contextType, 
      description: options.description,
      schema: options.schema,
      contextHub: this,
      eventBus: this.eventBus
    });
    
    // Store provider
    this.providers.set(options.id, provider);
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('context:provider-registered', {
        id: options.id,
        contextType: options.contextType
      });
    }
    
    return provider;
  }
  
  /**
   * Register a context consumer
   */
  async registerConsumer(options) {
    if (!options.id || !options.contextTypes || !options.contextTypes.length) {
      throw new Error('Consumer ID and context types are required');
    }
    
    // Create consumer
    const consumer = new ContextConsumer({
      id: options.id,
      contextTypes: options.contextTypes,
      description: options.description,
      contextHub: this,
      eventBus: this.eventBus
    });
    
    // Store consumer
    this.consumers.set(options.id, consumer);
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('context:consumer-registered', {
        id: options.id,
        contextTypes: options.contextTypes
      });
    }
    
    return consumer;
  }
  
  /**
   * Create a connection between provider and consumer
   */
  _createConnection(providerId, consumerId, contextType) {
    // Check if connection already exists
    const existingConnection = this.connections.find(
      conn => conn.providerId === providerId && 
              conn.consumerId === consumerId &&
              conn.contextType === contextType
    );
    
    if (existingConnection) {
      return existingConnection;
    }
    
    // Create new connection
    const connection = {
      providerId,
      consumerId,
      contextType,
      created: new Date().toISOString()
    };
    
    this.connections.push(connection);
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('context:connection-created', connection);
    }
    
    return connection;
  }
  
  /**
   * Connect compatible providers to a consumer
   */
  _connectCompatibleProviders(consumerId, contextTypes) {
    const consumer = this.consumers.get(consumerId);
    if (!consumer) return;
    
    // For each provider
    for (const [providerId, provider] of this.providers.entries()) {
      // If provider offers a context type the consumer wants
      if (contextTypes.includes(provider.contextType)) {
        // Create connection
        this._createConnection(providerId, consumerId, provider.contextType);
        
        // If provider has current context data, deliver it to the consumer
        if (provider.currentContext !== undefined) {
          consumer._receiveContext(provider.contextType, provider.currentContext, providerId);
        }
      }
    }
  }
  
  /**
   * Connect compatible consumers to a provider
   */
  _connectCompatibleConsumers(providerId, contextType) {
    const provider = this.providers.get(providerId);
    if (!provider) return;
    
    // For each consumer
    for (const [consumerId, consumer] of this.consumers.entries()) {
      // If consumer wants the context type the provider offers
      if (consumer.contextTypes.includes(contextType)) {
        // Create connection
        this._createConnection(providerId, consumerId, contextType);
        
        // If provider has current context data, deliver it to the consumer
        if (provider.currentContext !== undefined) {
          consumer._receiveContext(contextType, provider.currentContext, providerId);
        }
      }
    }
  }
  
  /**
   * Get all connections
   */
  getConnectionInfo() {
    return [...this.connections];
  }
  
  /**
   * Update context from provider to connected consumers
   */
  _updateContext(providerId, contextType, data) {
    // Find connections for this provider and context type
    const connections = this.connections.filter(
      conn => conn.providerId === providerId && conn.contextType === contextType
    );
    
    // For each connection, update the consumer
    for (const connection of connections) {
      const consumer = this.consumers.get(connection.consumerId);
      if (consumer) {
        consumer._receiveContext(contextType, data, providerId);
      }
    }
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('context:updated', {
        providerId,
        contextType,
        timestamp: new Date().toISOString()
      });
    }
  }
  
  /**
   * Get a provider by ID
   */
  getProvider(id) {
    return this.providers.get(id);
  }
  
  /**
   * Get a consumer by ID
   */
  getConsumer(id) {
    return this.consumers.get(id);
  }
}

class ContextProvider {
  constructor(options) {
    this.id = options.id;
    this.contextType = options.contextType;
    this.description = options.description || '';
    this.schema = options.schema;
    this.contextHub = options.contextHub;
    this.eventBus = options.eventBus;
    this.currentContext = undefined;
  }
  
  /**
   * Update the context data
   */
  async updateContext(data) {
    // Validate data against schema if schema is provided
    if (this.schema) {
      this._validateAgainstSchema(data);
    }
    
    // Store current context
    this.currentContext = data;
    
    // Propagate update to context hub
    if (this.contextHub) {
      this.contextHub._updateContext(this.id, this.contextType, data);
    }
    
    return true;
  }
  
  /**
   * Validate data against schema
   */
  _validateAgainstSchema(data) {
    // Simple schema validation
    if (!data || typeof data !== 'object') {
      throw new Error('Context data must be an object');
    }
    
    if (!this.schema) return true;
    
    // Check required properties
    if (this.schema.required) {
      for (const prop of this.schema.required) {
        if (!(prop in data)) {
          throw new Error(\`Required property '\${prop}' is missing\`);
        }
      }
    }
    
    // Check property types
    if (this.schema.properties) {
      for (const [prop, propSchema] of Object.entries(this.schema.properties)) {
        if (prop in data) {
          if (propSchema.type === 'string' && typeof data[prop] !== 'string') {
            throw new Error(\`Property '\${prop}' should be a string\`);
          } else if (propSchema.type === 'number' && typeof data[prop] !== 'number') {
            throw new Error(\`Property '\${prop}' should be a number\`);
          } else if (propSchema.type === 'boolean' && typeof data[prop] !== 'boolean') {
            throw new Error(\`Property '\${prop}' should be a boolean\`);
          } else if (propSchema.type === 'object' && (typeof data[prop] !== 'object' || data[prop] === null)) {
            throw new Error(\`Property '\${prop}' should be an object\`);
          } else if (propSchema.type === 'array' && !Array.isArray(data[prop])) {
            throw new Error(\`Property '\${prop}' should be an array\`);
          }
        }
      }
    }
    
    return true;
  }
}

class ContextConsumer {
  constructor(options) {
    this.id = options.id;
    this.contextTypes = options.contextTypes;
    this.description = options.description || '';
    this.contextHub = options.contextHub;
    this.eventBus = options.eventBus;
    this.contextHandlers = new Map();
    this.receivedContexts = new Map();
  }
  
  /**
   * Subscribe to context updates for a specific type
   */
  onContext(contextType, handler) {
    if (!this.contextTypes.includes(contextType)) {
      throw new Error(\`This consumer does not subscribe to context type '\${contextType}'\`);
    }
    
    if (!this.contextHandlers.has(contextType)) {
      this.contextHandlers.set(contextType, []);
    }
    
    this.contextHandlers.get(contextType).push(handler);
    
    // If we already have this context type, call the handler immediately
    if (this.receivedContexts.has(contextType)) {
      const contextData = this.receivedContexts.get(contextType);
      handler(contextData.data, contextData.providerId);
    }
    
    // Return unsubscribe function
    return () => {
      const handlers = this.contextHandlers.get(contextType) || [];
      const index = handlers.indexOf(handler);
      if (index !== -1) {
        handlers.splice(index, 1);
      }
    };
  }
  
  /**
   * Receive context update from provider (internal use)
   */
  _receiveContext(contextType, data, providerId) {
    // Store received context
    this.receivedContexts.set(contextType, { data, providerId });
    
    // Call handlers
    const handlers = this.contextHandlers.get(contextType) || [];
    for (const handler of handlers) {
      try {
        handler(data, providerId);
      } catch (error) {
        console.error(\`Error in context handler for \${contextType}: \${error.message}\`);
      }
    }
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('context:consumer-updated', {
        consumerId: this.id,
        contextType,
        providerId,
        timestamp: new Date().toISOString()
      });
    }
  }
  
  /**
   * Get all received contexts
   */
  getReceivedContexts() {
    return Object.fromEntries(this.receivedContexts);
  }
  
  /**
   * Get specific context type
   */
  getContext(contextType) {
    return this.receivedContexts.has(contextType) 
      ? this.receivedContexts.get(contextType).data 
      : undefined;
  }
}

// CommonJS export
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { ContextHub, ContextProvider, ContextConsumer };
}

// ES module export
export { ContextHub, ContextProvider, ContextConsumer };
`;
  
  fs.writeFileSync(filePath, content);
  console.log(`Created/updated: ${filePath}`);
  
  // Create index.js file
  const indexContent = `/**
 * Context Sharing - Index
 */

import { ContextHub, ContextProvider, ContextConsumer } from './context-sharing.js';

export { ContextHub, ContextProvider, ContextConsumer };
`;
  
  fs.writeFileSync(indexPath, indexContent);
  console.log(`Created/updated: ${indexPath}`);
}

// Create the extension system module
function createExtensionSystemModule() {
  const dir = path.join(__dirname, 'core', 'extensions');
  const filePath = path.join(dir, 'extension-system.js');
  const indexPath = path.join(dir, 'index.js');
  
  ensureDirectoryExists(dir);
  
  const content = `/**
 * Extension System
 * 
 * Provides a framework for extending PrimeOS through standardized extension points.
 */

class ExtensionManager {
  constructor(options = {}) {
    this.eventBus = options.eventBus;
    this.manifoldRegistry = options.manifoldRegistry;
    this.secureVault = options.secureVault;
    
    this.extensionPoints = new Map();
    this.extensions = new Map();
    this.subscriptions = new Map();
    this.initialized = false;
  }
  
  async initialize() {
    if (this.initialized) return this;
    
    // Set up event listeners if event bus is provided
    if (this.eventBus) {
      this.eventBus.subscribe('extension:installed', (data) => {
        this._processExtensionPoints(data.extension);
      });
      
      this.eventBus.subscribe('extension:uninstalled', (data) => {
        this._removeExtensionContent(data.extension);
      });
      
      this.eventBus.subscribe('extension:enabled', (data) => {
        this._processExtensionPoints(data.extension);
      });
      
      this.eventBus.subscribe('extension:disabled', (data) => {
        this._removeExtensionContent(data.extension);
      });
    }
    
    this.initialized = true;
    return this;
  }
  
  /**
   * Register a new extension point
   */
  async registerExtensionPoint(options) {
    if (!options.id) {
      throw new Error('Extension point ID is required');
    }
    
    if (this.extensionPoints.has(options.id)) {
      throw new Error(\`Extension point with ID '\${options.id}' already exists\`);
    }
    
    // Create extension point
    const extensionPoint = new ExtensionPoint({
      id: options.id,
      name: options.name || options.id,
      description: options.description || '',
      schema: options.schema
    });
    
    // Store extension point
    this.extensionPoints.set(options.id, extensionPoint);
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('extension-point:registered', {
        id: options.id,
        name: extensionPoint.name
      });
    }
    
    // Process existing extensions for this point
    for (const extension of this.extensions.values()) {
      if (extension.enabled && extension.extensionPoints && extension.extensionPoints[options.id]) {
        this._addExtensionContent(extension, options.id);
      }
    }
    
    return extensionPoint;
  }
  
  /**
   * Install a new extension
   */
  async installExtension(manifest) {
    if (!manifest.id) {
      throw new Error('Extension ID is required');
    }
    
    if (this.extensions.has(manifest.id)) {
      throw new Error(\`Extension with ID '\${manifest.id}' already exists\`);
    }
    
    // Validate manifest
    this._validateExtensionManifest(manifest);
    
    // Create extension
    const extension = new Extension({
      id: manifest.id,
      name: manifest.name || manifest.id,
      version: manifest.version || '1.0.0',
      description: manifest.description || '',
      extensionPoints: manifest.extensionPoints || {},
      enabled: true
    });
    
    // Store extension
    this.extensions.set(manifest.id, extension);
    
    // Store extension data securely if secure vault is available
    if (this.secureVault) {
      await this.secureVault.setSecret(\`extension:\${manifest.id}\`, JSON.stringify(extension));
    }
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('extension:installed', {
        id: extension.id,
        name: extension.name,
        extension
      });
    }
    
    return extension;
  }
  
  /**
   * Uninstall an extension
   */
  async uninstallExtension(id) {
    const extension = this.extensions.get(id);
    if (!extension) {
      throw new Error(\`Extension with ID '\${id}' not found\`);
    }
    
    // Remove extension points content
    this._removeExtensionContent(extension);
    
    // Remove extension
    this.extensions.delete(id);
    
    // Remove from secure vault if available
    if (this.secureVault) {
      await this.secureVault.removeSecret(\`extension:\${id}\`);
    }
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('extension:uninstalled', {
        id,
        extension
      });
    }
    
    return true;
  }
  
  /**
   * Enable or disable an extension
   */
  async setExtensionEnabled(id, enabled) {
    const extension = this.extensions.get(id);
    if (!extension) {
      throw new Error(\`Extension with ID '\${id}' not found\`);
    }
    
    if (extension.enabled === enabled) {
      return extension;
    }
    
    // Update extension
    extension.enabled = enabled;
    
    // Update in secure vault if available
    if (this.secureVault) {
      await this.secureVault.setSecret(\`extension:\${id}\`, JSON.stringify(extension));
    }
    
    // Process extension points
    if (enabled) {
      this._processExtensionPoints(extension);
      
      // Emit event
      if (this.eventBus) {
        this.eventBus.publish('extension:enabled', {
          id,
          extension
        });
      }
    } else {
      this._removeExtensionContent(extension);
      
      // Emit event
      if (this.eventBus) {
        this.eventBus.publish('extension:disabled', {
          id,
          extension
        });
      }
    }
    
    return extension;
  }
  
  /**
   * Get all extension points
   */
  getAllExtensionPoints() {
    return Array.from(this.extensionPoints.values());
  }
  
  /**
   * Get all extensions
   */
  getAllExtensions() {
    return Array.from(this.extensions.values());
  }
  
  /**
   * Get extension point content
   */
  getExtensionPointContent(extensionPointId) {
    const extensionPoint = this.extensionPoints.get(extensionPointId);
    if (!extensionPoint) {
      return [];
    }
    
    return extensionPoint.getContent();
  }
  
  /**
   * Subscribe to extension point changes
   */
  subscribeToExtensionPoint(extensionPointId, handler) {
    const extensionPoint = this.extensionPoints.get(extensionPointId);
    if (!extensionPoint) {
      throw new Error(\`Extension point '\${extensionPointId}' not found\`);
    }
    
    if (!this.subscriptions.has(extensionPointId)) {
      this.subscriptions.set(extensionPointId, []);
    }
    
    this.subscriptions.get(extensionPointId).push(handler);
    
    // Initial call with current content
    handler(extensionPoint.getContent());
    
    // Return unsubscribe function
    return () => {
      const handlers = this.subscriptions.get(extensionPointId) || [];
      const index = handlers.indexOf(handler);
      if (index !== -1) {
        handlers.splice(index, 1);
      }
    };
  }
  
  /**
   * Process extension points for an extension
   */
  _processExtensionPoints(extension) {
    if (!extension.extensionPoints) return;
    
    for (const [pointId, items] of Object.entries(extension.extensionPoints)) {
      this._addExtensionContent(extension, pointId, items);
    }
  }
  
  /**
   * Add extension content to an extension point
   */
  _addExtensionContent(extension, extensionPointId, items) {
    const extensionPoint = this.extensionPoints.get(extensionPointId);
    if (!extensionPoint) return;
    
    // Use provided items or get from extension
    const contentItems = items || extension.extensionPoints[extensionPointId];
    if (!contentItems || !Array.isArray(contentItems)) return;
    
    // Add each item
    for (const item of contentItems) {
      // Add extension metadata
      const enrichedItem = {
        ...item,
        extensionId: extension.id,
        extensionName: extension.name
      };
      
      // Add to extension point
      extensionPoint.addContent(enrichedItem);
    }
    
    // Notify subscribers
    this._notifyExtensionPointSubscribers(extensionPointId);
  }
  
  /**
   * Remove extension content from all extension points
   */
  _removeExtensionContent(extension) {
    if (!extension.extensionPoints) return;
    
    for (const pointId of Object.keys(extension.extensionPoints)) {
      const extensionPoint = this.extensionPoints.get(pointId);
      if (extensionPoint) {
        // Remove all content from this extension
        extensionPoint.removeContentByExtension(extension.id);
        
        // Notify subscribers
        this._notifyExtensionPointSubscribers(pointId);
      }
    }
  }
  
  /**
   * Notify extension point subscribers about changes
   */
  _notifyExtensionPointSubscribers(extensionPointId) {
    const extensionPoint = this.extensionPoints.get(extensionPointId);
    if (!extensionPoint) return;
    
    const handlers = this.subscriptions.get(extensionPointId) || [];
    const content = extensionPoint.getContent();
    
    for (const handler of handlers) {
      try {
        handler(content);
      } catch (error) {
        console.error(\`Error in extension point handler: \${error.message}\`);
      }
    }
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('extension-point:content-changed', {
        id: extensionPointId,
        name: extensionPoint.name
      });
    }
  }
  
  /**
   * Validate extension manifest
   */
  _validateExtensionManifest(manifest) {
    // Basic validation
    if (!manifest.id) {
      throw new Error('Extension ID is required');
    }
    
    if (!manifest.name) {
      throw new Error('Extension name is required');
    }
    
    if (!manifest.version) {
      throw new Error('Extension version is required');
    }
    
    // Check extension points
    if (manifest.extensionPoints) {
      for (const [pointId, items] of Object.entries(manifest.extensionPoints)) {
        const extensionPoint = this.extensionPoints.get(pointId);
        
        // Warn if extension point doesn't exist
        if (!extensionPoint) {
          console.warn(\`Extension point '\${pointId}' is not registered\`);
          continue;
        }
        
        // Validate schema if available
        if (extensionPoint.schema && Array.isArray(items)) {
          for (const item of items) {
            this._validateItemAgainstSchema(item, extensionPoint.schema, pointId);
          }
        }
      }
    }
    
    return true;
  }
  
  /**
   * Validate an item against schema
   */
  _validateItemAgainstSchema(item, schema, pointId) {
    // Check if item is an object
    if (!item || typeof item !== 'object') {
      throw new Error(\`Extension point '\${pointId}' items must be objects\`);
    }
    
    // Check required properties
    if (schema.required) {
      for (const prop of schema.required) {
        if (!(prop in item)) {
          throw new Error(\`Required property '\${prop}' is missing in extension point '\${pointId}'\`);
        }
      }
    }
    
    // Check property types
    if (schema.properties) {
      for (const [prop, propSchema] of Object.entries(schema.properties)) {
        if (prop in item) {
          if (propSchema.type === 'string' && typeof item[prop] !== 'string') {
            throw new Error(\`Property '\${prop}' should be a string in extension point '\${pointId}'\`);
          } else if (propSchema.type === 'number' && typeof item[prop] !== 'number') {
            throw new Error(\`Property '\${prop}' should be a number in extension point '\${pointId}'\`);
          } else if (propSchema.type === 'boolean' && typeof item[prop] !== 'boolean') {
            throw new Error(\`Property '\${prop}' should be a boolean in extension point '\${pointId}'\`);
          } else if (propSchema.type === 'object' && (typeof item[prop] !== 'object' || item[prop] === null)) {
            throw new Error(\`Property '\${prop}' should be an object in extension point '\${pointId}'\`);
          } else if (propSchema.type === 'array' && !Array.isArray(item[prop])) {
            throw new Error(\`Property '\${prop}' should be an array in extension point '\${pointId}'\`);
          }
        }
      }
    }
    
    return true;
  }
}

class ExtensionPoint {
  constructor(options) {
    this.id = options.id;
    this.name = options.name || options.id;
    this.description = options.description || '';
    this.schema = options.schema;
    this.content = [];
  }
  
  /**
   * Add content to this extension point
   */
  addContent(item) {
    // Check if item already exists
    const existingIndex = this.content.findIndex(i => 
      i.id === item.id && i.extensionId === item.extensionId
    );
    
    if (existingIndex !== -1) {
      // Update existing item
      this.content[existingIndex] = item;
    } else {
      // Add new item
      this.content.push(item);
    }
    
    return true;
  }
  
  /**
   * Remove content by ID
   */
  removeContent(id) {
    this.content = this.content.filter(item => item.id !== id);
    return true;
  }
  
  /**
   * Remove all content from a specific extension
   */
  removeContentByExtension(extensionId) {
    this.content = this.content.filter(item => item.extensionId !== extensionId);
    return true;
  }
  
  /**
   * Get all content
   */
  getContent() {
    return [...this.content];
  }
}

class Extension {
  constructor(options) {
    this.id = options.id;
    this.name = options.name || options.id;
    this.version = options.version || '1.0.0';
    this.description = options.description || '';
    this.extensionPoints = options.extensionPoints || {};
    this.enabled = options.enabled !== false;
  }
  
  /**
   * Convert to JSON
   */
  toJSON() {
    return {
      id: this.id,
      name: this.name,
      version: this.version,
      description: this.description,
      extensionPoints: this.extensionPoints,
      enabled: this.enabled
    };
  }
}

// CommonJS export
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { ExtensionManager, ExtensionPoint, Extension };
}

// ES module export
export { ExtensionManager, ExtensionPoint, Extension };
`;
  
  fs.writeFileSync(filePath, content);
  console.log(`Created/updated: ${filePath}`);
  
  // Create index.js file
  const indexContent = `/**
 * Extension System - Index
 */

import { ExtensionManager, ExtensionPoint, Extension } from './extension-system.js';

export { ExtensionManager, ExtensionPoint, Extension };
`;
  
  fs.writeFileSync(indexPath, indexContent);
  console.log(`Created/updated: ${indexPath}`);
}

// Create the manifold import/export module
function createManifoldImportExportModule() {
  const dir = path.join(__dirname, 'core', 'manifold');
  const filePath = path.join(dir, 'manifold-import-export.js');
  const networkPath = path.join(dir, 'network-adapter.js');
  const indexPath = path.join(dir, 'index.js');
  
  ensureDirectoryExists(dir);
  
  const content = `/**
 * Manifold Import/Export
 * 
 * Provides functionality for importing and exporting manifolds between PrimeOS instances.
 */

import { NetworkAdapter } from './network-adapter.js';

class ManifoldImportExport {
  constructor(options = {}) {
    this.manifoldRegistry = options.manifoldRegistry;
    this.secureVault = options.secureVault;
    this.eventBus = options.eventBus;
    this.networkAdapter = options.networkAdapter || new NetworkAdapter();
    this.endpoints = new Map();
    this.initialized = false;
  }
  
  async initialize() {
    if (this.initialized) return this;
    
    // Load endpoints from secure vault if available
    if (this.secureVault) {
      const endpointsJson = await this.secureVault.getSecret('manifold:endpoints');
      if (endpointsJson) {
        try {
          const endpoints = JSON.parse(endpointsJson);
          endpoints.forEach(endpoint => {
            this.endpoints.set(endpoint.name, endpoint);
          });
        } catch (error) {
          console.error('Error loading endpoints from secure vault:', error);
        }
      }
    }
    
    this.initialized = true;
    return this;
  }
  
  /**
   * Add a remote endpoint
   */
  async addRemoteEndpoint(endpoint) {
    if (!endpoint.name || !endpoint.url) {
      throw new Error('Endpoint name and URL are required');
    }
    
    if (this.endpoints.has(endpoint.name)) {
      throw new Error(\`Endpoint with name "\${endpoint.name}" already exists\`);
    }
    
    // Store endpoint
    this.endpoints.set(endpoint.name, {
      name: endpoint.name,
      url: endpoint.url,
      token: endpoint.token || null,
      added: new Date().toISOString()
    });
    
    // Store endpoints in secure vault if available
    await this._saveEndpoints();
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('remote-endpoint:added', {
        name: endpoint.name,
        url: endpoint.url
      });
    }
    
    return endpoint;
  }
  
  /**
   * Remove a remote endpoint
   */
  async removeRemoteEndpoint(name) {
    if (!this.endpoints.has(name)) {
      throw new Error(\`Endpoint with name "\${name}" not found\`);
    }
    
    // Remove endpoint
    this.endpoints.delete(name);
    
    // Store endpoints in secure vault if available
    await this._saveEndpoints();
    
    // Emit event
    if (this.eventBus) {
      this.eventBus.publish('remote-endpoint:removed', {
        name
      });
    }
    
    return true;
  }
  
  /**
   * Get all remote endpoints
   */
  async getRemoteEndpoints() {
    return Array.from(this.endpoints.values());
  }
  
  /**
   * Export a manifold to a remote endpoint
   */
  async exportManifold(options) {
    if (!options.manifoldId) {
      throw new Error('Manifold ID is required');
    }
    
    if (!options.endpointUrl) {
      throw new Error('Endpoint URL is required');
    }
    
    // Find endpoint by URL
    const endpoint = Array.from(this.endpoints.values()).find(e => e.url === options.endpointUrl);
    if (!endpoint) {
      throw new Error(\`Endpoint with URL "\${options.endpointUrl}" not found\`);
    }
    
    try {
      // Get manifold
      const manifold = await this.manifoldRegistry.getManifold(options.manifoldId);
      if (!manifold) {
        throw new Error(\`Manifold with ID "\${options.manifoldId}" not found\`);
      }
      
      // Create export morphology
      const morphology = {
        manifold: manifold.toJSON(),
        relatedManifolds: [],
        relationships: []
      };
      
      // Include related manifolds if requested
      if (options.includeRelated) {
        const related = manifold.getRelatedManifolds();
        
        for (const relatedManifold of related) {
          // Get related manifold
          const relatedId = relatedManifold.manifold.getId();
          const fullManifold = await this.manifoldRegistry.getManifold(relatedId);
          
          if (fullManifold) {
            // Add to morphology
            morphology.relatedManifolds.push(fullManifold.toJSON());
            
            // Add relationship
            morphology.relationships.push({
              sourceId: options.manifoldId,
              targetId: relatedId,
              type: relatedManifold.type,
              metadata: relatedManifold.metadata || {}
            });
          }
        }
      }
      
      // Set auth token if available
      if (endpoint.token) {
        this.networkAdapter.setAuthToken(endpoint.token);
      }
      
      // Export to remote endpoint
      const result = await this.networkAdapter.post(
        \`\${endpoint.url}/api/manifolds/import\`,
        morphology
      );
      
      if (!result.data || !result.data.success) {
        throw new Error(\`Export failed: \${result.data?.error || 'Unknown error'}\`);
      }
      
      // Emit event
      if (this.eventBus) {
        this.eventBus.publish('remote-manifold:exported', {
          sourceId: options.manifoldId,
          remoteId: result.data.manifestId,
          endpoint: endpoint.name
        });
      }
      
      return {
        success: true,
        remoteId: result.data.manifestId,
        relatedIds: result.data.relatedManifoldIds || {}
      };
    } catch (error) {
      // Emit error event
      if (this.eventBus) {
        this.eventBus.publish('remote-manifold:export-error', {
          manifoldId: options.manifoldId,
          endpoint: endpoint.name,
          error
        });
      }
      
      throw error;
    }
  }
  
  /**
   * Import a manifold from a remote endpoint
   */
  async importManifold(options) {
    if (!options.remoteId) {
      throw new Error('Remote manifold ID is required');
    }
    
    if (!options.endpointUrl) {
      throw new Error('Endpoint URL is required');
    }
    
    // Find endpoint by URL
    const endpoint = Array.from(this.endpoints.values()).find(e => e.url === options.endpointUrl);
    if (!endpoint) {
      throw new Error(\`Endpoint with URL "\${options.endpointUrl}" not found\`);
    }
    
    try {
      // Set auth token if available
      if (endpoint.token) {
        this.networkAdapter.setAuthToken(endpoint.token);
      }
      
      // Get manifold from remote endpoint
      const result = await this.networkAdapter.get(
        \`\${endpoint.url}/api/manifolds/export/\${options.remoteId}\`
      );
      
      if (!result.data || !result.data.manifold) {
        throw new Error(\`Import failed: \${result.data?.error || 'Unknown error'}\`);
      }
      
      // Extract morphology
      const morphology = result.data;
      
      // Register manifold
      const manifoldData = morphology.manifold;
      
      // Ensure the manifold has an invariant with a name
      if (!manifoldData.invariant) {
        manifoldData.invariant = {};
      }
      
      if (!manifoldData.invariant.name) {
        manifoldData.invariant.name = \`Imported \${manifoldData.meta?.type || 'Manifold'}\`;
      }
      
      // Add source information
      manifoldData.invariant.importedFrom = options.endpointUrl;
      manifoldData.invariant.originalId = options.remoteId;
      manifoldData.invariant.importedAt = new Date().toISOString();
      
      // Register main manifold
      let localId;
      
      // Try to find existing manifold with the same original ID
      const existingManifolds = await this.manifoldRegistry.findManifolds(
        'invariant',
        'originalId',
        options.remoteId
      );
      
      if (existingManifolds && existingManifolds.length > 0) {
        // Update existing manifold
        localId = existingManifolds[0].getId();
        await this.manifoldRegistry.updateManifold(localId, {
          updateSource: 'import',
          lastImportedAt: new Date().toISOString()
        });
      } else {
        // Register new manifold
        const manifold = await this.manifoldRegistry.registerApp(manifoldData.invariant);
        localId = manifold.getId();
      }
      
      // Import related manifolds and relationships if requested
      if (options.includeRelated && morphology.relatedManifolds) {
        const relatedIds = {};
        
        // Register related manifolds
        for (const relatedManifold of morphology.relatedManifolds) {
          // Ensure the manifold has an invariant with a name
          if (!relatedManifold.invariant) {
            relatedManifold.invariant = {};
          }
          
          if (!relatedManifold.invariant.name) {
            relatedManifold.invariant.name = \`Imported \${relatedManifold.meta?.type || 'Manifold'}\`;
          }
          
          // Add source information
          relatedManifold.invariant.importedFrom = options.endpointUrl;
          relatedManifold.invariant.originalId = relatedManifold.meta.id;
          relatedManifold.invariant.importedAt = new Date().toISOString();
          
          // Try to find existing manifold with the same original ID
          const existingRelated = await this.manifoldRegistry.findManifolds(
            'invariant',
            'originalId',
            relatedManifold.meta.id
          );
          
          if (existingRelated && existingRelated.length > 0) {
            // Use existing related manifold
            relatedIds[relatedManifold.meta.id] = existingRelated[0].getId();
            
            // Update it
            await this.manifoldRegistry.updateManifold(relatedIds[relatedManifold.meta.id], {
              updateSource: 'import',
              lastImportedAt: new Date().toISOString()
            });
          } else {
            // Register new related manifold
            const related = await this.manifoldRegistry.registerApp(relatedManifold.invariant);
            relatedIds[relatedManifold.meta.id] = related.getId();
          }
        }
        
        // Create relationships
        if (morphology.relationships) {
          for (const relationship of morphology.relationships) {
            // Map remote IDs to local IDs
            const sourceId = relationship.sourceId === options.remoteId
              ? localId
              : relatedIds[relationship.sourceId];
              
            const targetId = relationship.targetId === options.remoteId
              ? localId
              : relatedIds[relationship.targetId];
            
            if (sourceId && targetId) {
              // Create relationship
              await this.manifoldRegistry.createRelation(
                sourceId,
                targetId,
                relationship.type,
                relationship.metadata
              );
            }
          }
        }
      }
      
      // Emit event
      if (this.eventBus) {
        this.eventBus.publish('remote-manifold:imported', {
          remoteId: options.remoteId,
          localId,
          endpoint: endpoint.name
        });
      }
      
      return {
        success: true,
        localId
      };
    } catch (error) {
      // Emit error event
      if (this.eventBus) {
        this.eventBus.publish('remote-manifold:import-error', {
          remoteId: options.remoteId,
          endpoint: endpoint.name,
          error
        });
      }
      
      throw error;
    }
  }
  
  /**
   * Save endpoints to secure vault
   */
  async _saveEndpoints() {
    if (this.secureVault) {
      await this.secureVault.setSecret(
        'manifold:endpoints',
        JSON.stringify(Array.from(this.endpoints.values()))
      );
    }
  }
}

// CommonJS export
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { ManifoldImportExport };
}

// ES module export
export { ManifoldImportExport };
`;
  
  fs.writeFileSync(filePath, content);
  console.log(`Created/updated: ${filePath}`);
  
  // Create network adapter
  const networkContent = `/**
 * Network Adapter
 * 
 * Provides HTTP communication for the Manifold Import/Export system.
 */

class NetworkAdapter {
  constructor() {
    this.authToken = null;
  }
  
  /**
   * Set authentication token
   */
  setAuthToken(token) {
    this.authToken = token;
  }
  
  /**
   * Make a GET request
   */
  async get(url) {
    try {
      const headers = {
        'Content-Type': 'application/json'
      };
      
      if (this.authToken) {
        headers['Authorization'] = \`Bearer \${this.authToken}\`;
      }
      
      const response = await fetch(url, {
        method: 'GET',
        headers
      });
      
      const data = await response.json();
      
      return { data };
    } catch (error) {
      throw new Error(\`Network error: \${error.message}\`);
    }
  }
  
  /**
   * Make a POST request
   */
  async post(url, data) {
    try {
      const headers = {
        'Content-Type': 'application/json'
      };
      
      if (this.authToken) {
        headers['Authorization'] = \`Bearer \${this.authToken}\`;
      }
      
      const response = await fetch(url, {
        method: 'POST',
        headers,
        body: JSON.stringify(data)
      });
      
      const responseData = await response.json();
      
      return { data: responseData };
    } catch (error) {
      throw new Error(\`Network error: \${error.message}\`);
    }
  }
}

// CommonJS export
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { NetworkAdapter };
}

// ES module export
export { NetworkAdapter };
`;
  
  fs.writeFileSync(networkPath, networkContent);
  console.log(`Created/updated: ${networkPath}`);
  
  // Create index.js file
  const indexContent = `/**
 * Manifold Import/Export - Index
 */

import { ManifoldImportExport } from './manifold-import-export.js';
import { NetworkAdapter } from './network-adapter.js';

export { ManifoldImportExport, NetworkAdapter };
`;
  
  fs.writeFileSync(indexPath, indexContent);
  console.log(`Created/updated: ${indexPath}`);
}

// Run all module creation functions
createVisualizationModule();
createContextSharingModule();
createExtensionSystemModule();
createManifoldImportExportModule();

console.log('All core modules updated successfully!');