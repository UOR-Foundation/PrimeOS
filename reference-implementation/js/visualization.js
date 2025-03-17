/**
 * PrimeOS Reference Implementation - Visualizations
 * Advanced visualizations for PrimeOS concepts
 */

// Visualization system
const Visualization = {
    // Active visualizations
    visualizations: {},
    
    // Initialize visualizations
    init: function() {
        // Initialize event controls
        this.initEventControls();
        
        // Initialize coherence controls
        this.initCoherenceControls();
        
        // Initialize application layer visualization
        this.initApplicationLayer();
    },
    
    // Initialize event controls
    initEventControls: function() {
        // Initialize publish event button
        const publishBtn = document.getElementById('publish-event');
        if (publishBtn) {
            publishBtn.addEventListener('click', () => this.publishRandomEvent());
        }
        
        // Initialize subscribe event button
        const subscribeBtn = document.getElementById('subscribe-event');
        if (subscribeBtn) {
            subscribeBtn.addEventListener('click', () => this.subscribeToRandomEvent());
        }
    },
    
    // Initialize coherence controls
    initCoherenceControls: function() {
        // Initialize check coherence button
        const checkBtn = document.getElementById('check-coherence');
        if (checkBtn) {
            checkBtn.addEventListener('click', () => this.checkSystemCoherence());
        }
        
        // Initialize optimize coherence button
        const optimizeBtn = document.getElementById('optimize-coherence');
        if (optimizeBtn) {
            optimizeBtn.addEventListener('click', () => this.optimizeSystemCoherence());
        }
    },
    
    // Initialize application layer visualization
    initApplicationLayer: function() {
        const appComponentsDiv = document.getElementById('app-components');
        if (!appComponentsDiv) return;
        
        // Create application visualization
        const appHeader = document.createElement('div');
        appHeader.className = 'app-header';
        appHeader.innerHTML = `
            <h4>Application Components</h4>
            <button id="create-app-btn">Create Application</button>
        `;
        
        const appList = document.createElement('div');
        appList.className = 'app-list';
        appList.id = 'app-list';
        
        appComponentsDiv.appendChild(appHeader);
        appComponentsDiv.appendChild(appList);
        
        // Add handler for create application button
        const createAppBtn = document.getElementById('create-app-btn');
        if (createAppBtn) {
            createAppBtn.addEventListener('click', () => this.createRandomApplication());
        }
    },
    
    // Publish a random event
    publishRandomEvent: function() {
        // Define possible event types
        const eventTypes = [
            'user:action',
            'system:notification',
            'component:interaction',
            'data:update',
            'resource:request'
        ];
        
        // Generate random event data
        const eventType = eventTypes[Math.floor(Math.random() * eventTypes.length)];
        const timestamp = new Date().toISOString();
        const eventId = `evt-${Math.floor(Math.random() * 10000)}`;
        
        // Generate payload based on event type
        let payload = {};
        
        switch (eventType) {
            case 'user:action':
                payload = {
                    action: ['click', 'swipe', 'hover', 'drag'][Math.floor(Math.random() * 4)],
                    target: `element-${Math.floor(Math.random() * 100)}`,
                    coordinates: {
                        x: Math.floor(Math.random() * 1000),
                        y: Math.floor(Math.random() * 500)
                    }
                };
                break;
                
            case 'system:notification':
                payload = {
                    level: ['info', 'warning', 'error', 'success'][Math.floor(Math.random() * 4)],
                    message: `System notification ${eventId}`,
                    code: Math.floor(Math.random() * 1000)
                };
                break;
                
            case 'component:interaction':
                payload = {
                    sourceId: `comp-${Math.floor(Math.random() * 100)}`,
                    targetId: `comp-${Math.floor(Math.random() * 100)}`,
                    interaction: ['update', 'sync', 'initialize', 'connect'][Math.floor(Math.random() * 4)]
                };
                break;
                
            case 'data:update':
                payload = {
                    dataType: ['user', 'config', 'resource', 'application'][Math.floor(Math.random() * 4)],
                    operation: ['create', 'update', 'delete', 'read'][Math.floor(Math.random() * 4)],
                    path: `/data/${Math.floor(Math.random() * 10)}/${Math.floor(Math.random() * 100)}`
                };
                break;
                
            case 'resource:request':
                payload = {
                    resourceType: ['memory', 'cpu', 'network', 'storage'][Math.floor(Math.random() * 4)],
                    amount: Math.floor(Math.random() * 1000),
                    priority: Math.floor(Math.random() * 10)
                };
                break;
        }
        
        // Add common fields
        payload.timestamp = timestamp;
        payload.eventId = eventId;
        
        // Publish the event
        try {
            Prime.EventBus.publish(eventType, payload);
            
            // Log success
            Framework.log(`Event published: ${eventType}`, 'success');
        } catch (error) {
            Framework.log(`Failed to publish event: ${error.message}`, 'error');
            console.error(error);
        }
    },
    
    // Subscribe to a random event
    subscribeToRandomEvent: function() {
        // Define possible event topics to subscribe to
        const eventTopics = [
            'user:*',
            'system:*',
            'component:*',
            'data:*',
            'resource:*',
            '*'
        ];
        
        // Select a random topic
        const topic = eventTopics[Math.floor(Math.random() * eventTopics.length)];
        
        // Generate a handler ID for tracking
        const handlerId = `handler-${Math.floor(Math.random() * 10000)}`;
        
        // Create event handler
        const handler = function(data) {
            // Handler logic - this will be shown in the event log via the EventBus monitor
            return {
                received: true,
                handlerId,
                topic,
                timestamp: new Date().toISOString()
            };
        };
        
        // Store handler reference
        handler.id = handlerId;
        
        try {
            // Subscribe to the event
            Prime.EventBus.subscribe(topic, handler);
            
            // Log success
            Framework.log(`Subscribed to ${topic} with handler ${handlerId}`, 'success');
            
            // Publish a notification about the subscription
            Prime.EventBus.publish('system:subscription', {
                topic,
                handlerId,
                timestamp: new Date().toISOString()
            });
        } catch (error) {
            Framework.log(`Failed to subscribe to event: ${error.message}`, 'error');
            console.error(error);
        }
    },
    
    // Check system coherence
    checkSystemCoherence: function() {
        try {
            // Get coherence value from framework
            const coherenceValue = primeFramework.getCoherence();
            
            // Determine coherence status
            let status;
            if (coherenceValue >= 0.8) {
                status = 'Excellent';
            } else if (coherenceValue >= 0.6) {
                status = 'Good';
            } else if (coherenceValue >= 0.4) {
                status = 'Fair';
            } else if (coherenceValue >= 0.2) {
                status = 'Poor';
            } else {
                status = 'Critical';
            }
            
            // Log coherence status
            Framework.log(`System coherence: ${coherenceValue.toFixed(4)} (${status})`, 
                coherenceValue >= 0.6 ? 'success' : (coherenceValue >= 0.4 ? 'warning' : 'error'));
            
            // Publish coherence check event
            Prime.EventBus.publish('system:coherence:check', {
                value: coherenceValue,
                status,
                timestamp: new Date().toISOString()
            });
            
            return coherenceValue;
        } catch (error) {
            Framework.log(`Failed to check coherence: ${error.message}`, 'error');
            console.error(error);
            return null;
        }
    },
    
    // Optimize system coherence
    optimizeSystemCoherence: function() {
        try {
            // Get initial coherence
            const initialCoherence = primeFramework.getCoherence();
            
            // Optimize coherence
            const options = {
                maxIterations: 10,
                tolerance: 1e-6,
                learningRate: 0.1
            };
            
            const optimizedCoherence = primeFramework.optimizeCoherence(options);
            
            // Calculate improvement
            const improvement = optimizedCoherence - initialCoherence;
            const percentImprovement = (improvement / Math.max(0.0001, initialCoherence)) * 100;
            
            // Log optimization result
            if (improvement >= 0) {
                Framework.log(`Coherence optimized: ${initialCoherence.toFixed(4)} → ${optimizedCoherence.toFixed(4)} (${percentImprovement.toFixed(2)}% improvement)`, 'success');
            } else {
                Framework.log(`Coherence optimization failed: ${initialCoherence.toFixed(4)} → ${optimizedCoherence.toFixed(4)} (${Math.abs(percentImprovement).toFixed(2)}% degradation)`, 'warning');
            }
            
            // Publish optimization event
            Prime.EventBus.publish('system:coherence:optimize', {
                initialValue: initialCoherence,
                finalValue: optimizedCoherence,
                improvement,
                percentImprovement,
                timestamp: new Date().toISOString()
            });
            
            // Trigger visualization update
            Framework.visualizeCoherence();
            
            return optimizedCoherence;
        } catch (error) {
            Framework.log(`Failed to optimize coherence: ${error.message}`, 'error');
            console.error(error);
            return null;
        }
    },
    
    // Create a random application
    createRandomApplication: function() {
        // Define possible application types
        const appTypes = [
            {
                name: 'Calculator',
                components: ['NumberPad', 'Display', 'MemoryStore'],
                icon: '🧮'
            },
            {
                name: 'Notes',
                components: ['Editor', 'FileList', 'Toolbar'],
                icon: '📝'
            },
            {
                name: 'Weather',
                components: ['Forecast', 'Map', 'Settings'],
                icon: '🌦️'
            },
            {
                name: 'Clock',
                components: ['AnalogFace', 'DigitalDisplay', 'Alarms'],
                icon: '⏰'
            },
            {
                name: 'Gallery',
                components: ['ImageGrid', 'Viewer', 'Filter'],
                icon: '🖼️'
            }
        ];
        
        // Select a random application type
        const appType = appTypes[Math.floor(Math.random() * appTypes.length)];
        
        // Generate a unique app ID
        const appId = `app-${appType.name.toLowerCase()}-${Math.floor(Math.random() * 1000)}`;
        
        try {
            // Create the application
            const app = primeFramework.createApplication({
                id: appId,
                name: `${appType.name} App`,
                icon: appType.icon,
                components: appType.components.map(name => ({
                    name,
                    id: `${name.toLowerCase()}-${Math.floor(Math.random() * 1000)}`
                })),
                behavior: {
                    initialState: {
                        running: true,
                        theme: 'light'
                    },
                    actions: {
                        start: function() {
                            this.setState({ running: true });
                        },
                        stop: function() {
                            this.setState({ running: false });
                        },
                        toggleTheme: function() {
                            this.setState({ 
                                theme: this.state.theme === 'light' ? 'dark' : 'light' 
                            });
                        }
                    }
                }
            });
            
            // Add to display
            this.addApplicationToDisplay(app);
            
            // Log creation
            Framework.log(`Application created: ${app.name} (${app.id})`, 'success');
            
            // Publish app creation event
            Prime.EventBus.publish('application:created', {
                id: app.id,
                name: app.name,
                components: app.components.length
            });
            
            return app;
        } catch (error) {
            Framework.log(`Failed to create application: ${error.message}`, 'error');
            console.error(error);
            return null;
        }
    },
    
    // Add application to the display
    addApplicationToDisplay: function(app) {
        const appList = document.getElementById('app-list');
        if (!appList) return;
        
        // Create app entry
        const appEntry = document.createElement('div');
        appEntry.className = 'app-entry';
        appEntry.dataset.id = app.id;
        
        // Create app content
        appEntry.innerHTML = `
            <div class="app-icon">${app.icon || '📱'}</div>
            <div class="app-info">
                <div class="app-name">${app.name}</div>
                <div class="app-id">${app.id}</div>
                <div class="app-components">Components: ${app.components ? app.components.length : 0}</div>
            </div>
            <div class="app-actions">
                <button class="app-start">${app.state && app.state.running ? 'Restart' : 'Start'}</button>
                <button class="app-stop">Stop</button>
            </div>
        `;
        
        // Add event handlers
        const startBtn = appEntry.querySelector('.app-start');
        if (startBtn) {
            startBtn.addEventListener('click', () => {
                try {
                    app.behavior.actions.start.call(app);
                    startBtn.textContent = 'Restart';
                    Framework.log(`Application ${app.name} started`);
                    
                    // Publish app start event
                    Prime.EventBus.publish('application:started', {
                        id: app.id,
                        name: app.name
                    });
                } catch (error) {
                    Framework.log(`Failed to start application: ${error.message}`, 'error');
                }
            });
        }
        
        const stopBtn = appEntry.querySelector('.app-stop');
        if (stopBtn) {
            stopBtn.addEventListener('click', () => {
                try {
                    app.behavior.actions.stop.call(app);
                    if (startBtn) startBtn.textContent = 'Start';
                    Framework.log(`Application ${app.name} stopped`);
                    
                    // Publish app stop event
                    Prime.EventBus.publish('application:stopped', {
                        id: app.id,
                        name: app.name
                    });
                } catch (error) {
                    Framework.log(`Failed to stop application: ${error.message}`, 'error');
                }
            });
        }
        
        // Add to display
        appList.appendChild(appEntry);
    }
};

// Initialize visualization system when DOM is ready
document.addEventListener('DOMContentLoaded', function() {
    Visualization.init();
});