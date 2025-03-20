/**
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
      .attr('viewBox', `0 0 ${this.options.width} ${this.options.height}`)
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
      .data(this.links, d => `${d.source.id || d.source}-${d.target.id || d.target}`);
    
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
      this.nodeElements.attr('transform', d => `translate(${d.x},${d.y})`);
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
