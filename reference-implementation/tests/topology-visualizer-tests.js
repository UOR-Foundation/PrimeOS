/**
 * PrimeOS Reference Implementation - TopologyVisualizer Tests
 * 
 * Tests for the topology visualization of manifold relationships.
 */

// Mock D3.js
const mockD3Selection = {
  append: jest.fn().mockReturnThis(),
  attr: jest.fn().mockReturnThis(),
  style: jest.fn().mockReturnThis(),
  text: jest.fn().mockReturnThis(),
  classed: jest.fn().mockReturnThis(),
  call: jest.fn().mockReturnThis(),
  on: jest.fn().mockReturnThis(),
  selectAll: jest.fn().mockReturnThis(),
  data: jest.fn().mockReturnThis(),
  join: jest.fn().mockReturnThis(),
  transition: jest.fn().mockReturnThis(),
  duration: jest.fn().mockReturnThis()
};

const mockD3 = {
  select: jest.fn().mockReturnValue(mockD3Selection),
  forceSimulation: jest.fn().mockReturnValue({
    force: jest.fn().mockReturnThis(),
    nodes: jest.fn().mockReturnThis(),
    on: jest.fn().mockReturnThis(),
    alpha: jest.fn().mockReturnThis(),
    restart: jest.fn().mockReturnThis(),
    stop: jest.fn()
  }),
  forceLink: jest.fn().mockReturnValue({
    id: jest.fn().mockReturnThis(),
    distance: jest.fn().mockReturnThis(),
    strength: jest.fn().mockReturnThis(),
    links: jest.fn().mockReturnThis()
  }),
  forceManyBody: jest.fn().mockReturnValue({
    strength: jest.fn().mockReturnThis()
  }),
  forceCenter: jest.fn(),
  forceCollide: jest.fn().mockReturnValue({
    radius: jest.fn().mockReturnThis()
  }),
  scaleLinear: jest.fn().mockReturnValue({
    domain: jest.fn().mockReturnValue({
      range: jest.fn().mockReturnThis()
    })
  }),
  scaleOrdinal: jest.fn().mockReturnValue({}),
  schemeCategory10: ['#1f77b4', '#ff7f0e', '#2ca02c', '#d62728', '#9467bd'],
  zoom: jest.fn().mockReturnValue({
    scaleExtent: jest.fn().mockReturnValue({
      on: jest.fn().mockReturnThis()
    })
  }),
  zoomIdentity: {
    scale: jest.fn().mockReturnThis(),
    translate: jest.fn().mockReturnThis()
  },
  drag: jest.fn().mockReturnValue({
    on: jest.fn().mockReturnThis()
  })
};

// Mock event bus
const mockEventBus = {
  publish: jest.fn(),
  subscribe: jest.fn().mockImplementation((event, handler) => {
    return () => {}; // Return unsubscribe function
  })
};

// Mock ManifoldRegistry
const mockManifoldRegistry = {
  getManifolds: jest.fn().mockResolvedValue([]),
  getRelationships: jest.fn().mockResolvedValue([]),
  findManifolds: jest.fn().mockResolvedValue([]),
  getManifold: jest.fn().mockResolvedValue(null)
};

// Mock container
class MockContainer {
  constructor() {
    this.isConnected = true;
    this.children = [];
    this.innerHTML = '';
    this.style = {};
    this.classList = {
      add: jest.fn(),
      remove: jest.fn(),
      contains: jest.fn().mockReturnValue(false)
    };
    this.getBoundingClientRect = jest.fn().mockReturnValue({
      width: 800,
      height: 600
    });
  }
  
  appendChild(element) {
    this.children.push(element);
    return element;
  }
  
  querySelector(selector) {
    return null;
  }
  
  querySelectorAll(selector) {
    return [];
  }
  
  remove() {
    this.isConnected = false;
  }
}

// Mock Element
class MockElement {
  constructor(tagName) {
    this.tagName = tagName;
    this.className = '';
    this.textContent = '';
    this.style = {};
    this.attributes = {};
    this.children = [];
    this.innerText = '';
    this.innerHTML = '';
    this.isConnected = true;
    this.listeners = {};
  }
  
  getAttribute(name) {
    return this.attributes[name] || null;
  }
  
  setAttribute(name, value) {
    this.attributes[name] = value;
  }
  
  addEventListener(event, handler) {
    if (!this.listeners[event]) {
      this.listeners[event] = [];
    }
    this.listeners[event].push(handler);
  }
  
  appendChild(child) {
    this.children.push(child);
    return child;
  }
  
  remove() {
    this.isConnected = false;
  }
}

// Mock document
document.createElement = jest.fn().mockImplementation((tagName) => {
  return new MockElement(tagName);
});

document.getElementById = jest.fn().mockReturnValue(new MockContainer());
document.body = new MockContainer();
document.head = new MockContainer();

// Import the system under test with proper mocks
jest.mock('d3', () => mockD3);
jest.mock('../core/app-factory/manifold-registry.js', () => ({
  ManifoldRegistry: mockManifoldRegistry
}));

// Import the TopologyVisualizer class
const { TopologyVisualizer } = require('../core/visualization/topology-visualizer');

describe('TopologyVisualizer', () => {
  let visualizer;
  let container;
  
  beforeEach(() => {
    // Create a new container for each test
    container = new MockContainer();
    
    // Reset mocks
    jest.clearAllMocks();
    
    // Create visualizer instance
    visualizer = new TopologyVisualizer({
      container,
      manifoldRegistry: mockManifoldRegistry,
      eventBus: mockEventBus
    });
  });
  
  describe('Initialization', () => {
    it('should create SVG elements during initialization', async () => {
      await visualizer.initialize();
      
      // Should create SVG element
      expect(mockD3.select).toHaveBeenCalledWith(container);
      
      // Should create zoom behavior
      expect(mockD3.zoom).toHaveBeenCalled();
      
      // Should create nodes and links groups
      expect(mockD3Selection.append).toHaveBeenCalledWith('g');
      
      // Should load data from registry
      expect(mockManifoldRegistry.getManifolds).toHaveBeenCalled();
      expect(mockManifoldRegistry.getRelationships).toHaveBeenCalled();
      
      // Should subscribe to events
      expect(mockEventBus.subscribe).toHaveBeenCalledWith('manifold:created', expect.any(Function));
      expect(mockEventBus.subscribe).toHaveBeenCalledWith('manifold:updated', expect.any(Function));
      expect(mockEventBus.subscribe).toHaveBeenCalledWith('manifold:deleted', expect.any(Function));
      expect(mockEventBus.subscribe).toHaveBeenCalledWith('relationship:created', expect.any(Function));
      expect(mockEventBus.subscribe).toHaveBeenCalledWith('relationship:deleted', expect.any(Function));
    });
    
    it('should set initial dimensions from container', async () => {
      await visualizer.initialize();
      expect(visualizer.width).toBe(800);
      expect(visualizer.height).toBe(600);
    });

    it('should create toolbar controls during initialization', async () => {
      await visualizer.initialize();
      
      // Should create toolbar elements
      expect(document.createElement).toHaveBeenCalledWith('div');
      
      // Container should have toolbar child
      expect(container.children.length).toBeGreaterThan(0);
      
      // Should create buttons
      expect(document.createElement).toHaveBeenCalledWith('button');
    });
  });
  
  describe('Data Loading', () => {
    beforeEach(() => {
      // Setup mock manifolds and relationships
      const mockManifolds = [
        {
          id: 'app1',
          name: 'TestApp',
          type: 'application',
          depth: 1
        },
        {
          id: 'component1',
          name: 'TestComponent',
          type: 'component',
          depth: 2
        }
      ];
      
      const mockRelationships = [
        {
          source: 'app1',
          target: 'component1',
          type: 'uses',
          strength: 0.8
        }
      ];
      
      mockManifoldRegistry.getManifolds.mockResolvedValue(mockManifolds);
      mockManifoldRegistry.getRelationships.mockResolvedValue(mockRelationships);
    });
    
    it('should transform manifolds to nodes and relationships to links', async () => {
      await visualizer.initialize();
      
      // Should transform data correctly
      expect(visualizer.nodes.length).toBe(2);
      expect(visualizer.nodes[0].id).toBe('app1');
      expect(visualizer.nodes[0].type).toBe('application');
      
      expect(visualizer.links.length).toBe(1);
      expect(visualizer.links[0].source).toBe('app1');
      expect(visualizer.links[0].target).toBe('component1');
    });
    
    it('should create force simulation with nodes and links', async () => {
      await visualizer.initialize();
      
      // Should create simulation
      expect(mockD3.forceSimulation).toHaveBeenCalledWith(visualizer.nodes);
      expect(mockD3.forceLink).toHaveBeenCalledWith(visualizer.links);
    });
    
    it('should update visualization when data changes', async () => {
      await visualizer.initialize();
      
      // Verify visualization was updated
      expect(mockD3Selection.selectAll).toHaveBeenCalledWith('line');
      expect(mockD3Selection.selectAll).toHaveBeenCalledWith('circle');
      expect(mockD3Selection.data).toHaveBeenCalled();
    });
  });
  
  describe('Interactivity', () => {
    beforeEach(async () => {
      // Setup mock nodes and initialize
      visualizer.nodes = [
        {
          id: 'app1',
          name: 'TestApp',
          type: 'application',
          depth: 1,
          x: 100,
          y: 100
        }
      ];
      
      visualizer.links = [];
      
      await visualizer.initialize();
    });
    
    it('should select a node and show details', () => {
      const node = visualizer.nodes[0];
      
      // Mock selection
      mockD3.select.mockReturnValueOnce(mockD3Selection);
      
      // Select node
      visualizer.selectNode(node);
      
      // Should highlight node
      expect(mockD3.select).toHaveBeenCalledWith(expect.stringContaining(`#node-${node.id}`));
      expect(mockD3Selection.classed).toHaveBeenCalledWith('selected', true);
      
      // Should show node details
      expect(container.innerHTML).not.toBe('');
      
      // Should notify listeners
      expect(mockEventBus.publish).toHaveBeenCalledWith('topology:node-selected', { node });
    });
    
    it('should deselect a node and hide details', () => {
      const node = visualizer.nodes[0];
      
      // First select, then deselect
      visualizer.selectNode(node);
      visualizer.selectedNode = node;
      
      // Mock selection for deselection
      mockD3.select.mockReturnValueOnce(mockD3Selection);
      
      // Deselect node
      visualizer._deselectNode(node);
      
      // Should remove highlight
      expect(mockD3.select).toHaveBeenCalledWith(expect.stringContaining(`#node-${node.id}`));
      expect(mockD3Selection.classed).toHaveBeenCalledWith('selected', false);
      
      // Should notify listeners
      expect(mockEventBus.publish).toHaveBeenCalledWith('topology:node-deselected', { node });
      
      // Should clear selected node
      expect(visualizer.selectedNode).toBeNull();
    });
    
    it('should support zoom operations', () => {
      // Mock transform
      const mockTransform = { k: 1, x: 0, y: 0 };
      mockD3.zoomTransform = jest.fn().mockReturnValue(mockTransform);
      mockD3Selection.node = jest.fn().mockReturnValue({});
      
      // Call zoom handlers
      visualizer._handleZoomIn();
      
      // Should perform zoom transformation
      expect(mockD3Selection.transition).toHaveBeenCalled();
      expect(mockD3Selection.call).toHaveBeenCalled();
      expect(mockD3.zoom).toHaveBeenCalled();
      
      // Similarly for zoom out
      visualizer._handleZoomOut();
      expect(mockD3Selection.transition).toHaveBeenCalled();
      
      // And for reset zoom
      visualizer._handleResetZoom();
      expect(mockD3Selection.transition).toHaveBeenCalled();
    });
    
    it('should handle simulation start and stop', () => {
      // Create mock simulation
      visualizer.simulation = {
        restart: jest.fn(),
        stop: jest.fn(),
        alpha: jest.fn().mockReturnThis()
      };
      
      // Start simulation
      visualizer.startSimulation();
      expect(visualizer.simulation.restart).toHaveBeenCalled();
      
      // Stop simulation
      visualizer.stopSimulation();
      expect(visualizer.simulation.stop).toHaveBeenCalled();
    });
    
    it('should handle reset layout', () => {
      // Create mock simulation
      visualizer.simulation = {
        restart: jest.fn(),
        alpha: jest.fn().mockReturnThis()
      };
      
      // Reset layout
      visualizer._handleResetLayout();
      
      // Should reset node positions
      expect(visualizer.nodes[0].fx).toBeNull();
      expect(visualizer.nodes[0].fy).toBeNull();
      
      // Should restart simulation
      expect(visualizer.simulation.alpha).toHaveBeenCalledWith(1);
      expect(visualizer.simulation.restart).toHaveBeenCalled();
    });
  });
  
  describe('Event Handling', () => {
    beforeEach(async () => {
      await visualizer.initialize();
    });
    
    it('should handle manifold created event', () => {
      // Mock event handler subscription
      const eventHandler = mockEventBus.subscribe.mock.calls.find(
        call => call[0] === 'manifold:created'
      )[1];
      
      // Create mock manifold event
      const manifoldEvent = {
        manifold: {
          id: 'new-app',
          name: 'NewApp',
          type: 'application',
          depth: 1
        }
      };
      
      // Call handler
      eventHandler(manifoldEvent);
      
      // Should add new node
      expect(visualizer.nodes.length).toBe(1);
      expect(visualizer.nodes[0].id).toBe('new-app');
    });
    
    it('should handle manifold updated event', () => {
      // Add a node first
      visualizer.nodes = [
        {
          id: 'app1',
          name: 'TestApp',
          type: 'application',
          depth: 1
        }
      ];
      
      // Mock event handler subscription
      const eventHandler = mockEventBus.subscribe.mock.calls.find(
        call => call[0] === 'manifold:updated'
      )[1];
      
      // Create mock update event
      const updateEvent = {
        manifold: {
          id: 'app1',
          name: 'UpdatedApp',
          type: 'application',
          depth: 2
        }
      };
      
      // Call handler
      eventHandler(updateEvent);
      
      // Should update node
      expect(visualizer.nodes[0].name).toBe('UpdatedApp');
      expect(visualizer.nodes[0].depth).toBe(2);
    });
    
    it('should handle manifold deleted event', () => {
      // Add a node first
      visualizer.nodes = [
        {
          id: 'app1',
          name: 'TestApp',
          type: 'application',
          depth: 1
        }
      ];
      
      // Mock event handler subscription
      const eventHandler = mockEventBus.subscribe.mock.calls.find(
        call => call[0] === 'manifold:deleted'
      )[1];
      
      // Create mock delete event
      const deleteEvent = {
        manifoldId: 'app1'
      };
      
      // Call handler
      eventHandler(deleteEvent);
      
      // Should remove node
      expect(visualizer.nodes.length).toBe(0);
    });
    
    it('should handle relationship created event', () => {
      // Add nodes first
      visualizer.nodes = [
        { id: 'app1', name: 'TestApp' },
        { id: 'component1', name: 'TestComponent' }
      ];
      
      // Mock event handler subscription
      const eventHandler = mockEventBus.subscribe.mock.calls.find(
        call => call[0] === 'relationship:created'
      )[1];
      
      // Create mock relationship event
      const relationshipEvent = {
        relationship: {
          source: 'app1',
          target: 'component1',
          type: 'uses',
          strength: 0.7
        }
      };
      
      // Call handler
      eventHandler(relationshipEvent);
      
      // Should add new link
      expect(visualizer.links.length).toBe(1);
      expect(visualizer.links[0].source).toBe('app1');
      expect(visualizer.links[0].target).toBe('component1');
    });
    
    it('should handle relationship deleted event', () => {
      // Add nodes and link first
      visualizer.nodes = [
        { id: 'app1', name: 'TestApp' },
        { id: 'component1', name: 'TestComponent' }
      ];
      
      visualizer.links = [
        {
          source: { id: 'app1' },
          target: { id: 'component1' },
          type: 'uses'
        }
      ];
      
      // Mock event handler subscription
      const eventHandler = mockEventBus.subscribe.mock.calls.find(
        call => call[0] === 'relationship:deleted'
      )[1];
      
      // Create mock delete event
      const deleteEvent = {
        source: 'app1',
        target: 'component1'
      };
      
      // Call handler
      eventHandler(deleteEvent);
      
      // Should remove link
      expect(visualizer.links.length).toBe(0);
    });
  });
  
  describe('Error Handling', () => {
    it('should render error message when initialization fails', async () => {
      // Mock failure
      mockManifoldRegistry.getManifolds.mockRejectedValueOnce(new Error('Test error'));
      
      // Try to initialize
      await visualizer.initialize();
      
      // Should display error UI
      expect(container.innerHTML).toContain('Visualization Error');
      expect(container.innerHTML).toContain('Test error');
    });
    
    it('should retry initialization when retry button is clicked', async () => {
      // Mock failure and container
      mockManifoldRegistry.getManifolds.mockRejectedValueOnce(new Error('Test error'));
      
      // Create retry button handler
      const retryButton = new MockElement('button');
      retryButton.className = 'retry-button';
      
      // Mock container.querySelector to return our retry button
      container.querySelector = jest.fn().mockReturnValue(retryButton);
      
      // Try to initialize
      await visualizer.initialize();
      
      // Reset mock for second try
      mockManifoldRegistry.getManifolds.mockResolvedValueOnce([]);
      mockManifoldRegistry.getRelationships.mockResolvedValueOnce([]);
      
      // Find the click handler and simulate click
      const clickHandler = retryButton.listeners.click[0];
      clickHandler();
      
      // Should try to initialize again
      expect(mockManifoldRegistry.getManifolds).toHaveBeenCalledTimes(2);
    });
  });
});