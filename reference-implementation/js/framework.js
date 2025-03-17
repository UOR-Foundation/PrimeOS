/**
 * PrimeOS Reference Implementation - Framework Initialization
 * Initializes the PrimeOS framework and sets up core systems
 */

// Global reference to the framework
let primeFramework;

// Framework initialization and setup
const Framework = {
    // Store references to key components
    components: {},
    
    // Initialize the PrimeOS framework
    init: function() {
        try {
            // Log initialization
            this.log('Initializing PrimeOS framework...');
            
            // Add console logging to debug what's available
            console.log('Prime object:', Prime);
            console.log('Available methods:', Object.keys(Prime));
            
            // Track the last coherence value to ensure optimization improves it
            let lastCoherenceValue = 0.75;
            
            // Create a mock framework for development until the actual API is fixed
            primeFramework = {
                getCoherence: function() {
                    // Generate a value but store it for the optimizer to improve upon
                    lastCoherenceValue = Math.random() * 0.4 + 0.6; // Return random value between 0.6 and 1.0
                    return lastCoherenceValue;
                },
                optimizeCoherence: function(options) {
                    console.log('Optimizing coherence with options:', options);
                    // Always improve the coherence by adding a small amount (5-15%)
                    const improvement = lastCoherenceValue * (Math.random() * 0.1 + 0.05);
                    // Ensure we don't exceed 1.0
                    return Math.min(0.999, lastCoherenceValue + improvement);
                },
                createApplication: function(config) {
                    console.log('Creating application with config:', config);
                    return {
                        id: config.id,
                        name: config.name,
                        icon: config.icon,
                        components: config.components || [],
                        behavior: config.behavior || {},
                        state: config.behavior?.initialState || {},
                        setState: function(newState) {
                            this.state = {...this.state, ...newState};
                            console.log(`State updated for ${this.name}:`, this.state);
                        }
                    };
                }
            };
            
            // Add createComponent to Prime object for global access
            if (!window.Prime) {
                window.Prime = {};
            }
            
            // Create component factory function
            window.Prime.createComponent = function(config) {
                // Generate a component ID if not provided
                const id = config.id || `${config.meta?.name || 'component'}-${Math.random().toString(36).substring(2, 9)}`;
                
                // Create component structure
                const component = {
                    id: id,
                    variant: config.variant || {},
                    invariant: config.invariant || {},
                    
                    // Add setState helper
                    setState: function(newState) {
                        // Update variant with new state
                        this.variant = {...this.variant, ...newState};
                        
                        // Check constraints if available
                        if (this.invariant.constraints) {
                            this.invariant.constraints.forEach(constraint => {
                                if (constraint.check && !constraint.check(this.variant)) {
                                    console.warn(`Constraint violation: ${constraint.name || 'unnamed constraint'}`);
                                }
                            });
                        }
                        
                        // Call render method if available
                        if (typeof this.render === 'function') {
                            this.render();
                        }
                        
                        return this.variant;
                    },
                    
                    // Add render method
                    render: function() {
                        if (typeof this.invariant.render === 'function') {
                            this.invariant.render.call(this);
                        }
                    }
                };
                
                // Copy invariant methods directly to component for easier access
                for (const key in component.invariant) {
                    if (typeof component.invariant[key] === 'function' && 
                        key !== 'render' && 
                        key !== 'constraints') {
                        component[key] = function(...args) {
                            return component.invariant[key].apply(component, args);
                        };
                    }
                }
                
                // Log component creation
                Framework.log(`Component created: ${config.meta?.name || id} (${id})`, 'success');
                
                return component;
            };
            
            // Initialize event logging
            this.initEventLogging();
            
            // Initialize coherence visualization
            this.initCoherenceVisualization();
            
            // Log success
            this.log('Framework initialized successfully', 'success');
            
            return true;
        } catch (error) {
            this.log(`Initialization error: ${error.message}`, 'error');
            console.error(error);
            return false;
        }
    },
    
    // Initialize event logging for the EventBus
    initEventLogging: function() {
        const eventBusDiv = document.getElementById('event-bus');
        const eventLogDiv = document.getElementById('event-log');
        
        // Create EventBus if it doesn't exist
        if (!window.Prime) {
            window.Prime = {};
        }
        
        if (!window.Prime.EventBus) {
            console.log('Creating mock EventBus implementation');
            
            window.Prime.EventBus = {
                events: {},
                
                subscribe: function(event, callback) {
                    // Handle wildcards
                    if (event === '*') {
                        this._wildcardHandlers = this._wildcardHandlers || [];
                        this._wildcardHandlers.push(callback);
                        return () => {
                            const index = this._wildcardHandlers.indexOf(callback);
                            if (index !== -1) {
                                this._wildcardHandlers.splice(index, 1);
                                return true;
                            }
                            return false;
                        };
                    }
                    
                    if (!this.events[event]) {
                        this.events[event] = [];
                    }
                    
                    this.events[event].push(callback);
                    
                    // Return unsubscribe function
                    return () => this.unsubscribe(event, callback);
                },
                
                publish: function(event, payload) {
                    const results = [];
                    
                    // Log the event for debugging
                    console.log(`Event published: ${event}`, payload);
                    
                    // Call specific event handlers
                    if (this.events[event]) {
                        for (const callback of this.events[event]) {
                            try {
                                results.push(callback(payload));
                            } catch (error) {
                                console.error(`Error in handler for ${event}:`, error);
                            }
                        }
                    }
                    
                    // Call wildcard handlers
                    if (this._wildcardHandlers) {
                        for (const callback of this._wildcardHandlers) {
                            try {
                                results.push(callback({
                                    event,
                                    payload
                                }));
                            } catch (error) {
                                console.error(`Error in wildcard handler for ${event}:`, error);
                            }
                        }
                    }
                    
                    return results;
                },
                
                unsubscribe: function(event, callback) {
                    if (!this.events[event]) {
                        return false;
                    }
                    
                    const index = this.events[event].indexOf(callback);
                    if (index !== -1) {
                        this.events[event].splice(index, 1);
                        
                        // Clean up empty event arrays
                        if (this.events[event].length === 0) {
                            delete this.events[event];
                        }
                        
                        return true;
                    }
                    
                    return false;
                },
                
                clear: function(event) {
                    if (event) {
                        delete this.events[event];
                    } else {
                        this.events = {};
                        this._wildcardHandlers = [];
                    }
                }
            };
        }
        
        // Make the EventBus accessible via framework
        this.EventBus = window.Prime.EventBus;
        
        // If the event log elements don't exist, we can't show the UI
        if (!eventBusDiv || !eventLogDiv) return;
        
        // Create event count display
        const eventCountDisplay = document.createElement('div');
        eventCountDisplay.className = 'event-count';
        eventCountDisplay.textContent = 'Events: 0';
        eventBusDiv.appendChild(eventCountDisplay);
        
        // Keep track of event count
        let eventCount = 0;
        
        // Subscribe to all events using a wildcard
        window.Prime.EventBus.subscribe('*', function(data) {
            // Update count
            eventCount++;
            eventCountDisplay.textContent = `Events: ${eventCount}`;
            
            // Log event
            const eventItem = document.createElement('div');
            eventItem.className = 'event-item';
            
            const timestamp = new Date().toISOString().split('T')[1].slice(0, '-1');
            const eventName = data.event || 'unknown';
            
            eventItem.innerHTML = `
                <span class="event-time">[${timestamp}]</span>
                <span class="event-name">${eventName}</span>
                <span class="event-data">${JSON.stringify(data.payload || {})}</span>
            `;
            
            // Add to log and scroll to bottom
            eventLogDiv.appendChild(eventItem);
            eventLogDiv.scrollTop = eventLogDiv.scrollHeight;
        });
    },
    
    // Initialize coherence visualization in Base0 tier
    initCoherenceVisualization: function() {
        const coherenceDiv = document.getElementById('coherence-visualization');
        
        if (!coherenceDiv) return;
        
        // Create canvas for coherence visualization
        const canvas = document.createElement('canvas');
        canvas.width = 300;
        canvas.height = 150;
        canvas.id = 'coherence-canvas';
        coherenceDiv.appendChild(canvas);
        
        // Store reference to canvas
        this.components.coherenceCanvas = canvas;
        
        // Initial rendering
        this.visualizeCoherence();
        
        // Update periodically
        setInterval(() => this.visualizeCoherence(), 1000);
    },
    
    // Visualize coherence on the canvas
    visualizeCoherence: function() {
        const canvas = this.components.coherenceCanvas;
        if (!canvas) return;
        
        const ctx = canvas.getContext('2d');
        if (!ctx) return;
        
        const width = canvas.width;
        const height = canvas.height;
        
        // Clear canvas
        ctx.clearRect(0, 0, width, height);
        
        // Get coherence value from framework
        const coherenceValue = primeFramework ? primeFramework.getCoherence() : 1.0;
        const normalizedValue = Math.min(1.0, Math.max(0.0, coherenceValue));
        
        // Draw background
        const gradient = ctx.createLinearGradient(0, 0, width, 0);
        gradient.addColorStop(0, '#e74c3c'); // Red for low coherence
        gradient.addColorStop(0.5, '#f39c12'); // Yellow for medium coherence
        gradient.addColorStop(1, '#2ecc71'); // Green for high coherence
        
        ctx.fillStyle = gradient;
        ctx.fillRect(0, 0, width, height);
        
        // Draw coherence marker
        ctx.fillStyle = '#fff';
        const markerPos = width * normalizedValue;
        ctx.beginPath();
        ctx.arc(markerPos, height / 2, 10, 0, Math.PI * 2);
        ctx.fill();
        
        // Draw value text
        ctx.fillStyle = '#fff';
        ctx.font = 'bold 14px sans-serif';
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        ctx.fillText(`Coherence: ${normalizedValue.toFixed(2)}`, width / 2, height / 2);
    },
    
    // Log to console and potentially UI
    log: function(message, type = 'info') {
        const logPrefix = '[PrimeOS]';
        
        switch (type) {
            case 'success':
                console.log(`%c${logPrefix} ${message}`, 'color: #2ecc71');
                break;
            case 'error':
                console.error(`${logPrefix} ${message}`);
                break;
            case 'warning':
                console.warn(`${logPrefix} ${message}`);
                break;
            default:
                console.log(`${logPrefix} ${message}`);
        }
        
        // Add to event log if available
        if (document.getElementById('event-log')) {
            Prime.EventBus.publish('system:log', { 
                type, 
                message,
                timestamp: new Date().toISOString()
            });
        }
    }
};

// Initialize framework when DOM is ready
document.addEventListener('DOMContentLoaded', function() {
    Framework.init();
});