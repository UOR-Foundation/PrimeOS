/**
 * PrimeOS Reference Implementation - Topology Visualizer
 * 
 * Provides advanced visualization of manifold relationships using a force-directed graph.
 * This visualizer shows topological properties of manifolds, their connections,
 * and allows for interactive exploration of the manifold space.
 */

// Import core dependencies (with resilient imports)
let d3;
let ManifoldRegistry;

/**
 * Attempt to load dependencies
 * @returns {Promise<boolean>} Success flag
 */
async function loadDependencies() {
  try {
    // Try to load D3.js - first check if it's already loaded
    if (typeof window !== 'undefined' && window.d3) {
      d3 = window.d3;
    } else {
      // Try to load from CDN
      const d3Script = document.createElement('script');
      d3Script.src = 'https://d3js.org/d3.v7.min.js';
      
      // Load D3 asynchronously
      await new Promise((resolve, reject) => {
        d3Script.onload = () => {
          d3 = window.d3;
          resolve();
        };
        d3Script.onerror = reject;
        document.head.appendChild(d3Script);
      });
    }
    
    // Try to get ManifoldRegistry from global context
    if (typeof window !== 'undefined' && window.PrimeOS && window.PrimeOS.ManifoldRegistry) {
      ManifoldRegistry = window.PrimeOS.ManifoldRegistry;
    } else {
      // Try to import from relative path
      try {
        const registryModule = await import('../app-factory/manifold-registry.js');
        ManifoldRegistry = registryModule.ManifoldRegistry || registryModule.default;
      } catch (error) {
        console.warn('Failed to load ManifoldRegistry from relative path:', error);
        
        // Try alternate paths
        try {
          const registryModule = await import('/core/app-factory/manifold-registry.js');
          ManifoldRegistry = registryModule.ManifoldRegistry || registryModule.default;
        } catch (altError) {
          console.error('Failed to load ManifoldRegistry:', altError);
          // Create placeholder
          ManifoldRegistry = class {
            constructor() {
              this.manifolds = new Map();
              this.relationships = new Map();
            }
            
            getManifolds() { return []; }
            getRelationships() { return []; }
          };
        }
      }
    }
    
    return true;
  } catch (error) {
    console.error('Failed to load dependencies:', error);
    return false;
  }
}

/**
 * Topology Visualizer for manifold relationships
 */
class TopologyVisualizer {
  /**
   * Create a new TopologyVisualizer
   * @param {Object} options - Configuration options
   * @param {HTMLElement} options.container - Container element
   * @param {Object} options.manifoldRegistry - ManifoldRegistry instance
   * @param {Object} options.eventBus - Event bus for pub/sub
   */
  constructor(options = {}) {
    this.options = options;
    this.container = options.container || document.createElement('div');
    this.manifoldRegistry = options.manifoldRegistry || null;
    this.eventBus = options.eventBus || { publish: () => {}, subscribe: () => {} };
    
    // Initialize state
    this.initialized = false;
    this.simulation = null;
    this.svg = null;
    this.width = 0;
    this.height = 0;
    this.nodes = [];
    this.links = [];
    this.nodeElements = null;
    this.linkElements = null;
    this.selectedNode = null;
    
    // Visualization settings
    this.settings = {
      nodeSizeScale: d3 ? d3.scaleLinear().domain([0, 10]).range([5, 15]) : null,
      nodeColorScale: d3 ? d3.scaleOrdinal(d3.schemeCategory10) : null,
      linkStrengthScale: d3 ? d3.scaleLinear().domain([0, 1]).range([0.1, 1]) : null,
      chargeStrength: -150,
      linkDistance: 100,
      collisionRadius: 30,
      zoomExtent: [0.1, 10]
    };
  }
  
  /**
   * Initialize the visualizer
   * @returns {Promise<boolean>} Success flag
   */
  async initialize() {
    try {
      if (this.initialized) {
        return true;
      }
      
      // Load dependencies if needed
      if (!d3 || !ManifoldRegistry) {
        const success = await loadDependencies();
        if (!success) {
          throw new Error('Failed to load required dependencies');
        }
      }
      
      // Get ManifoldRegistry if not provided
      if (!this.manifoldRegistry) {
        if (typeof window !== 'undefined' && window.PrimeOS && window.PrimeOS.ManifoldRegistry) {
          this.manifoldRegistry = window.PrimeOS.ManifoldRegistry;
        } else {
          throw new Error('ManifoldRegistry not available');
        }
      }
      
      // Create container if it doesn't exist
      if (!this.container.isConnected) {
        const parent = document.getElementById('prime-shell') || document.body;
        parent.appendChild(this.container);
      }
      
      // Set dimensions
      this._updateDimensions();
      
      // Add resize listener
      window.addEventListener('resize', this._handleResize.bind(this));
      
      // Set up container
      this.container.classList.add('topology-visualizer');
      this.container.style.position = 'relative';
      this.container.style.overflow = 'hidden';
      
      // Add toolbar
      this._createToolbar();
      
      // Set up SVG
      this._setupSVG();
      
      // Load initial data
      await this.loadData();
      
      // Subscribe to manifold events
      this.eventBus.subscribe('manifold:created', this._handleManifoldCreated.bind(this));
      this.eventBus.subscribe('manifold:updated', this._handleManifoldUpdated.bind(this));
      this.eventBus.subscribe('manifold:deleted', this._handleManifoldDeleted.bind(this));
      this.eventBus.subscribe('relationship:created', this._handleRelationshipCreated.bind(this));
      this.eventBus.subscribe('relationship:deleted', this._handleRelationshipDeleted.bind(this));
      
      this.initialized = true;
      return true;
    } catch (error) {
      console.error('Failed to initialize TopologyVisualizer:', error);
      this._renderError(error);
      return false;
    }
  }
  
  /**
   * Load data from ManifoldRegistry
   * @returns {Promise<boolean>} Success flag
   */
  async loadData() {
    try {
      // Get manifolds and relationships
      const manifolds = await this.manifoldRegistry.getManifolds();
      const relationships = await this.manifoldRegistry.getRelationships();
      
      // Transform to nodes and links for D3
      this.nodes = manifolds.map(manifold => ({
        id: manifold.id,
        name: manifold.name || manifold.id,
        type: manifold.type || 'default',
        depth: manifold.depth || 0,
        x: Math.random() * this.width,
        y: Math.random() * this.height,
        manifold // Keep reference to original manifold
      }));
      
      this.links = relationships.map(rel => ({
        source: rel.source,
        target: rel.target,
        strength: rel.strength || 0.5,
        type: rel.type || 'default',
        relationship: rel // Keep reference to original relationship
      }));
      
      // Update visualization
      this._updateVisualization();
      
      return true;
    } catch (error) {
      console.error('Failed to load data:', error);
      return false;
    }
  }
  
  /**
   * Start the force simulation
   */
  startSimulation() {
    if (!this.simulation) {
      this._createSimulation();
    } else {
      this.simulation.restart();
    }
  }
  
  /**
   * Stop the force simulation
   */
  stopSimulation() {
    if (this.simulation) {
      this.simulation.stop();
    }
  }
  
  /**
   * Select a node
   * @param {Object} node - Node to select
   */
  selectNode(node) {
    // Deselect current node
    if (this.selectedNode) {
      this._deselectNode(this.selectedNode);
    }
    
    // Select new node
    this.selectedNode = node;
    
    // Highlight node
    d3.select(`#node-${node.id}`)
      .classed('selected', true)
      .attr('r', d => this.settings.nodeSizeScale(d.depth) * 1.5);
    
    // Highlight connected links and nodes
    const connectedLinks = this.links.filter(link => 
      link.source.id === node.id || link.target.id === node.id
    );
    
    const connectedNodeIds = new Set();
    connectedLinks.forEach(link => {
      connectedNodeIds.add(link.source.id);
      connectedNodeIds.add(link.target.id);
    });
    
    // Highlight connected links
    this.linkElements
      .filter(link => link.source.id === node.id || link.target.id === node.id)
      .classed('connected', true)
      .attr('stroke-width', 2);
    
    // Highlight connected nodes
    this.nodeElements
      .filter(n => n.id !== node.id && connectedNodeIds.has(n.id))
      .classed('connected', true);
    
    // Show node details
    this._showNodeDetails(node);
    
    // Notify listeners
    this.eventBus.publish('topology:node-selected', { node });
  }
  
  /**
   * Deselect a node
   * @param {Object} node - Node to deselect
   */
  _deselectNode(node) {
    // Remove highlight from node
    d3.select(`#node-${node.id}`)
      .classed('selected', false)
      .attr('r', d => this.settings.nodeSizeScale(d.depth));
    
    // Remove highlight from all links
    this.linkElements
      .classed('connected', false)
      .attr('stroke-width', 1);
    
    // Remove highlight from all nodes
    this.nodeElements
      .classed('connected', false);
    
    // Hide node details
    this._hideNodeDetails();
    
    // Clear selected node
    this.selectedNode = null;
    
    // Notify listeners
    this.eventBus.publish('topology:node-deselected', { node });
  }
  
  /**
   * Show node details
   * @param {Object} node - Node to show details for
   */
  _showNodeDetails(node) {
    // Create or update details panel
    let detailsPanel = this.container.querySelector('.node-details');
    
    if (!detailsPanel) {
      detailsPanel = document.createElement('div');
      detailsPanel.className = 'node-details';
      detailsPanel.style.position = 'absolute';
      detailsPanel.style.right = '10px';
      detailsPanel.style.top = '10px';
      detailsPanel.style.width = '300px';
      detailsPanel.style.backgroundColor = 'rgba(255, 255, 255, 0.9)';
      detailsPanel.style.borderRadius = '8px';
      detailsPanel.style.boxShadow = '0 2px 10px rgba(0, 0, 0, 0.1)';
      detailsPanel.style.padding = '15px';
      detailsPanel.style.zIndex = '100';
      detailsPanel.style.maxHeight = '80%';
      detailsPanel.style.overflowY = 'auto';
      
      this.container.appendChild(detailsPanel);
    }
    
    // Clear existing content
    detailsPanel.innerHTML = '';
    
    // Create close button
    const closeButton = document.createElement('button');
    closeButton.textContent = '×';
    closeButton.style.position = 'absolute';
    closeButton.style.right = '10px';
    closeButton.style.top = '10px';
    closeButton.style.backgroundColor = 'transparent';
    closeButton.style.border = 'none';
    closeButton.style.fontSize = '20px';
    closeButton.style.cursor = 'pointer';
    closeButton.addEventListener('click', () => this._deselectNode(node));
    
    detailsPanel.appendChild(closeButton);
    
    // Add node details
    const title = document.createElement('h3');
    title.textContent = node.name;
    title.style.marginTop = '0';
    title.style.marginBottom = '15px';
    
    detailsPanel.appendChild(title);
    
    // Display manifold properties
    const properties = document.createElement('div');
    properties.className = 'manifold-properties';
    
    // Add common properties
    properties.innerHTML = `
      <div class="property">
        <div class="property-label">ID:</div>
        <div class="property-value">${node.id}</div>
      </div>
      <div class="property">
        <div class="property-label">Type:</div>
        <div class="property-value">${node.type}</div>
      </div>
      <div class="property">
        <div class="property-label">Depth:</div>
        <div class="property-value">${node.depth}</div>
      </div>
    `;
    
    // Add manifold-specific properties
    if (node.manifold) {
      // Add invariant properties
      if (node.manifold.invariant) {
        const invariantDiv = document.createElement('div');
        invariantDiv.className = 'section';
        invariantDiv.innerHTML = '<h4>Invariant</h4>';
        
        for (const [key, value] of Object.entries(node.manifold.invariant)) {
          const propDiv = document.createElement('div');
          propDiv.className = 'property';
          propDiv.innerHTML = `
            <div class="property-label">${key}:</div>
            <div class="property-value">${this._formatValue(value)}</div>
          `;
          invariantDiv.appendChild(propDiv);
        }
        
        properties.appendChild(invariantDiv);
      }
      
      // Add variant properties
      if (node.manifold.variant) {
        const variantDiv = document.createElement('div');
        variantDiv.className = 'section';
        variantDiv.innerHTML = '<h4>Variant</h4>';
        
        for (const [key, value] of Object.entries(node.manifold.variant)) {
          const propDiv = document.createElement('div');
          propDiv.className = 'property';
          propDiv.innerHTML = `
            <div class="property-label">${key}:</div>
            <div class="property-value">${this._formatValue(value)}</div>
          `;
          variantDiv.appendChild(propDiv);
        }
        
        properties.appendChild(variantDiv);
      }
    }
    
    detailsPanel.appendChild(properties);
    
    // Add styles
    const style = document.createElement('style');
    style.textContent = `
      .property {
        display: flex;
        margin-bottom: 8px;
        font-size: 14px;
      }
      
      .property-label {
        font-weight: 500;
        width: 120px;
        color: #666;
      }
      
      .property-value {
        flex: 1;
      }
      
      .section {
        margin-top: 16px;
      }
      
      .section h4 {
        margin-top: 0;
        margin-bottom: 8px;
        color: #444;
        font-size: 16px;
      }
    `;
    
    detailsPanel.appendChild(style);
  }
  
  /**
   * Hide node details
   */
  _hideNodeDetails() {
    const detailsPanel = this.container.querySelector('.node-details');
    if (detailsPanel) {
      detailsPanel.remove();
    }
  }
  
  /**
   * Format a value for display
   * @param {*} value - Value to format
   * @returns {string} Formatted value
   */
  _formatValue(value) {
    if (value === null || value === undefined) {
      return '<em>null</em>';
    } else if (typeof value === 'object') {
      return `<details><summary>${Object.keys(value).length} properties</summary><pre>${JSON.stringify(value, null, 2)}</pre></details>`;
    } else if (typeof value === 'boolean') {
      return value ? 'true' : 'false';
    } else {
      return String(value);
    }
  }
  
  /**
   * Create the toolbar
   */
  _createToolbar() {
    const toolbar = document.createElement('div');
    toolbar.className = 'topology-toolbar';
    toolbar.style.position = 'absolute';
    toolbar.style.top = '10px';
    toolbar.style.left = '10px';
    toolbar.style.zIndex = '100';
    toolbar.style.display = 'flex';
    toolbar.style.gap = '8px';
    
    // Zoom controls
    const zoomInButton = document.createElement('button');
    zoomInButton.textContent = '+';
    zoomInButton.title = 'Zoom In';
    zoomInButton.className = 'toolbar-button';
    zoomInButton.addEventListener('click', this._handleZoomIn.bind(this));
    
    const zoomOutButton = document.createElement('button');
    zoomOutButton.textContent = '−';
    zoomOutButton.title = 'Zoom Out';
    zoomOutButton.className = 'toolbar-button';
    zoomOutButton.addEventListener('click', this._handleZoomOut.bind(this));
    
    const resetZoomButton = document.createElement('button');
    resetZoomButton.textContent = '⟲';
    resetZoomButton.title = 'Reset Zoom';
    resetZoomButton.className = 'toolbar-button';
    resetZoomButton.addEventListener('click', this._handleResetZoom.bind(this));
    
    // Layout controls
    const startButton = document.createElement('button');
    startButton.textContent = '▶';
    startButton.title = 'Start Simulation';
    startButton.className = 'toolbar-button';
    startButton.addEventListener('click', () => this.startSimulation());
    
    const stopButton = document.createElement('button');
    stopButton.textContent = '⏸';
    stopButton.title = 'Stop Simulation';
    stopButton.className = 'toolbar-button';
    stopButton.addEventListener('click', () => this.stopSimulation());
    
    const resetButton = document.createElement('button');
    resetButton.textContent = '↺';
    resetButton.title = 'Reset Layout';
    resetButton.className = 'toolbar-button';
    resetButton.addEventListener('click', this._handleResetLayout.bind(this));
    
    // Add buttons to toolbar
    toolbar.appendChild(zoomInButton);
    toolbar.appendChild(zoomOutButton);
    toolbar.appendChild(resetZoomButton);
    toolbar.appendChild(document.createElement('hr'));
    toolbar.appendChild(startButton);
    toolbar.appendChild(stopButton);
    toolbar.appendChild(resetButton);
    
    // Add styles
    const style = document.createElement('style');
    style.textContent = `
      .toolbar-button {
        width: 32px;
        height: 32px;
        border-radius: 4px;
        border: 1px solid #ddd;
        background-color: white;
        cursor: pointer;
        font-size: 16px;
        display: flex;
        align-items: center;
        justify-content: center;
        box-shadow: 0 1px 3px rgba(0, 0, 0, 0.1);
      }
      
      .toolbar-button:hover {
        background-color: #f5f5f5;
      }
      
      hr {
        width: 1px;
        height: 24px;
        background-color: #ddd;
        border: none;
        margin: 0 4px;
      }
    `;
    
    this.container.appendChild(style);
    this.container.appendChild(toolbar);
  }
  
  /**
   * Set up SVG container
   */
  _setupSVG() {
    // Create svg element
    this.svg = d3.select(this.container)
      .append('svg')
      .attr('width', this.width)
      .attr('height', this.height)
      .attr('class', 'topology-svg');
    
    // Create zoom behavior
    const zoom = d3.zoom()
      .scaleExtent(this.settings.zoomExtent)
      .on('zoom', this._handleZoom.bind(this));
    
    // Add zoom to svg
    this.svg.call(zoom);
    
    // Create container for zoom
    this.zoomContainer = this.svg.append('g');
    
    // Add main groups
    this.linksGroup = this.zoomContainer.append('g').attr('class', 'links');
    this.nodesGroup = this.zoomContainer.append('g').attr('class', 'nodes');
    
    // Add styles
    const style = document.createElement('style');
    style.textContent = `
      .topology-svg {
        width: 100%;
        height: 100%;
      }
      
      .nodes circle {
        stroke: white;
        stroke-width: 1.5;
      }
      
      .nodes circle.selected {
        stroke: #f8c41b;
        stroke-width: 2.5;
      }
      
      .nodes circle.connected {
        stroke: #f8c41b;
        stroke-width: 2;
      }
      
      .links line {
        stroke: #999;
        stroke-opacity: 0.6;
      }
      
      .links line.connected {
        stroke: #f8c41b;
        stroke-opacity: 0.8;
      }
    `;
    
    this.container.appendChild(style);
  }
  
  /**
   * Create force simulation
   */
  _createSimulation() {
    // Create force simulation
    this.simulation = d3.forceSimulation(this.nodes)
      .force('link', d3.forceLink(this.links)
        .id(d => d.id)
        .distance(this.settings.linkDistance)
        .strength(d => this.settings.linkStrengthScale(d.strength)))
      .force('charge', d3.forceManyBody().strength(this.settings.chargeStrength))
      .force('center', d3.forceCenter(this.width / 2, this.height / 2))
      .force('collision', d3.forceCollide().radius(this.settings.collisionRadius))
      .on('tick', this._handleTick.bind(this));
  }
  
  /**
   * Update the visualization
   */
  _updateVisualization() {
    // Update link elements
    this.linkElements = this.linksGroup
      .selectAll('line')
      .data(this.links, d => `${d.source.id || d.source}-${d.target.id || d.target}`)
      .join(
        enter => enter.append('line')
          .attr('stroke-width', 1)
          .attr('stroke', '#999'),
        update => update,
        exit => exit.remove()
      );
    
    // Update node elements
    this.nodeElements = this.nodesGroup
      .selectAll('circle')
      .data(this.nodes, d => d.id)
      .join(
        enter => enter.append('circle')
          .attr('id', d => `node-${d.id}`)
          .attr('r', d => this.settings.nodeSizeScale(d.depth))
          .attr('fill', d => this.settings.nodeColorScale(d.type))
          .call(this._setupDrag())
          .on('mouseover', this._handleNodeMouseOver.bind(this))
          .on('mouseout', this._handleNodeMouseOut.bind(this))
          .on('click', this._handleNodeClick.bind(this)),
        update => update,
        exit => exit.remove()
      );
    
    // Add tooltips
    this.nodeElements
      .append('title')
      .text(d => d.name);
    
    // Create or update simulation
    if (!this.simulation) {
      this._createSimulation();
    } else {
      this.simulation.nodes(this.nodes);
      this.simulation.force('link').links(this.links);
      this.simulation.alpha(1).restart();
    }
  }
  
  /**
   * Set up drag behavior
   * @returns {d3.drag} Drag behavior
   */
  _setupDrag() {
    return d3.drag()
      .on('start', this._handleDragStart.bind(this))
      .on('drag', this._handleDrag.bind(this))
      .on('end', this._handleDragEnd.bind(this));
  }
  
  /**
   * Update dimensions from container
   */
  _updateDimensions() {
    const rect = this.container.getBoundingClientRect();
    this.width = rect.width;
    this.height = rect.height;
    
    if (this.svg) {
      this.svg
        .attr('width', this.width)
        .attr('height', this.height);
      
      if (this.simulation) {
        this.simulation.force('center', d3.forceCenter(this.width / 2, this.height / 2));
        this.simulation.alpha(0.3).restart();
      }
    }
  }
  
  /**
   * Handle window resize
   */
  _handleResize() {
    this._updateDimensions();
  }
  
  /**
   * Handle simulation tick
   */
  _handleTick() {
    // Update link positions
    this.linkElements
      .attr('x1', d => d.source.x)
      .attr('y1', d => d.source.y)
      .attr('x2', d => d.target.x)
      .attr('y2', d => d.target.y);
    
    // Update node positions
    this.nodeElements
      .attr('cx', d => d.x)
      .attr('cy', d => d.y);
  }
  
  /**
   * Handle drag start
   * @param {Event} event - Drag event
   */
  _handleDragStart(event) {
    if (!event.active) this.simulation.alphaTarget(0.3).restart();
    event.subject.fx = event.subject.x;
    event.subject.fy = event.subject.y;
  }
  
  /**
   * Handle drag
   * @param {Event} event - Drag event
   */
  _handleDrag(event) {
    event.subject.fx = event.x;
    event.subject.fy = event.y;
  }
  
  /**
   * Handle drag end
   * @param {Event} event - Drag event
   */
  _handleDragEnd(event) {
    if (!event.active) this.simulation.alphaTarget(0);
    event.subject.fx = null;
    event.subject.fy = null;
  }
  
  /**
   * Handle node mouse over
   * @param {Event} event - Mouse event
   * @param {Object} d - Node data
   */
  _handleNodeMouseOver(event, d) {
    d3.select(event.target)
      .transition()
      .duration(200)
      .attr('r', this.settings.nodeSizeScale(d.depth) * 1.2);
  }
  
  /**
   * Handle node mouse out
   * @param {Event} event - Mouse event
   * @param {Object} d - Node data
   */
  _handleNodeMouseOut(event, d) {
    if (this.selectedNode && this.selectedNode.id === d.id) {
      return; // Don't shrink selected node
    }
    
    d3.select(event.target)
      .transition()
      .duration(200)
      .attr('r', this.settings.nodeSizeScale(d.depth));
  }
  
  /**
   * Handle node click
   * @param {Event} event - Mouse event
   * @param {Object} d - Node data
   */
  _handleNodeClick(event, d) {
    if (this.selectedNode && this.selectedNode.id === d.id) {
      this._deselectNode(d);
    } else {
      this.selectNode(d);
    }
  }
  
  /**
   * Handle zoom
   * @param {Event} event - Zoom event
   */
  _handleZoom(event) {
    this.zoomContainer.attr('transform', event.transform);
  }
  
  /**
   * Handle zoom in button click
   */
  _handleZoomIn() {
    const transform = d3.zoomTransform(this.svg.node());
    const newScale = transform.k * 1.3;
    
    this.svg.transition().duration(300)
      .call(d3.zoom().transform, 
        d3.zoomIdentity
          .translate(transform.x, transform.y)
          .scale(newScale)
      );
  }
  
  /**
   * Handle zoom out button click
   */
  _handleZoomOut() {
    const transform = d3.zoomTransform(this.svg.node());
    const newScale = transform.k / 1.3;
    
    this.svg.transition().duration(300)
      .call(d3.zoom().transform, 
        d3.zoomIdentity
          .translate(transform.x, transform.y)
          .scale(newScale)
      );
  }
  
  /**
   * Handle reset zoom button click
   */
  _handleResetZoom() {
    this.svg.transition().duration(300)
      .call(d3.zoom().transform, d3.zoomIdentity);
  }
  
  /**
   * Handle reset layout button click
   */
  _handleResetLayout() {
    // Reset node positions
    this.nodes.forEach(node => {
      node.x = Math.random() * this.width;
      node.y = Math.random() * this.height;
      node.vx = 0;
      node.vy = 0;
      node.fx = null;
      node.fy = null;
    });
    
    // Restart simulation from high alpha
    if (this.simulation) {
      this.simulation.alpha(1).restart();
    }
  }
  
  /**
   * Handle manifold created event
   * @param {Object} event - Manifold event
   */
  _handleManifoldCreated(event) {
    if (event && event.manifold) {
      // Add new node
      const newNode = {
        id: event.manifold.id,
        name: event.manifold.name || event.manifold.id,
        type: event.manifold.type || 'default',
        depth: event.manifold.depth || 0,
        x: this.width / 2,
        y: this.height / 2,
        manifold: event.manifold // Keep reference to original manifold
      };
      
      this.nodes.push(newNode);
      
      // Update visualization
      this._updateVisualization();
    }
  }
  
  /**
   * Handle manifold updated event
   * @param {Object} event - Manifold event
   */
  _handleManifoldUpdated(event) {
    if (event && event.manifold) {
      // Find node
      const nodeIndex = this.nodes.findIndex(node => node.id === event.manifold.id);
      
      if (nodeIndex !== -1) {
        // Update node
        this.nodes[nodeIndex] = {
          ...this.nodes[nodeIndex],
          name: event.manifold.name || event.manifold.id,
          type: event.manifold.type || 'default',
          depth: event.manifold.depth || 0,
          manifold: event.manifold // Keep reference to original manifold
        };
        
        // Update visualization
        this._updateVisualization();
      }
    }
  }
  
  /**
   * Handle manifold deleted event
   * @param {Object} event - Manifold event
   */
  _handleManifoldDeleted(event) {
    if (event && event.manifoldId) {
      // Remove node
      this.nodes = this.nodes.filter(node => node.id !== event.manifoldId);
      
      // Remove related links
      this.links = this.links.filter(link => 
        (link.source.id || link.source) !== event.manifoldId && 
        (link.target.id || link.target) !== event.manifoldId
      );
      
      // Update visualization
      this._updateVisualization();
    }
  }
  
  /**
   * Handle relationship created event
   * @param {Object} event - Relationship event
   */
  _handleRelationshipCreated(event) {
    if (event && event.relationship) {
      // Add new link
      const newLink = {
        source: event.relationship.source,
        target: event.relationship.target,
        strength: event.relationship.strength || 0.5,
        type: event.relationship.type || 'default',
        relationship: event.relationship // Keep reference to original relationship
      };
      
      this.links.push(newLink);
      
      // Update visualization
      this._updateVisualization();
    }
  }
  
  /**
   * Handle relationship deleted event
   * @param {Object} event - Relationship event
   */
  _handleRelationshipDeleted(event) {
    if (event && event.source && event.target) {
      // Remove link
      this.links = this.links.filter(link => 
        !((link.source.id || link.source) === event.source && 
          (link.target.id || link.target) === event.target)
      );
      
      // Update visualization
      this._updateVisualization();
    }
  }
  
  /**
   * Render error message
   * @param {Error} error - Error object
   */
  _renderError(error) {
    this.container.innerHTML = `
      <div class="topology-error">
        <h3>Visualization Error</h3>
        <p>${error.message || 'Failed to initialize topology visualizer'}</p>
        <button class="retry-button">Retry</button>
      </div>
      <style>
        .topology-error {
          display: flex;
          flex-direction: column;
          align-items: center;
          justify-content: center;
          height: 100%;
          text-align: center;
          color: #721c24;
          background-color: #f8d7da;
          padding: 20px;
        }
        
        .topology-error h3 {
          margin-top: 0;
        }
        
        .retry-button {
          margin-top: 16px;
          padding: 8px 16px;
          background-color: #0066cc;
          color: white;
          border: none;
          border-radius: 4px;
          cursor: pointer;
        }
        
        .retry-button:hover {
          background-color: #0055aa;
        }
      </style>
    `;
    
    // Add retry button handler
    const retryButton = this.container.querySelector('.retry-button');
    if (retryButton) {
      retryButton.addEventListener('click', () => {
        this.container.innerHTML = '';
        this.initialize();
      });
    }
  }
}

// Export for ES modules
export { TopologyVisualizer };
export default { TopologyVisualizer };