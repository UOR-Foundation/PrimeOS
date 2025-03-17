/**
 * PrimeOS Reference Implementation - Component System
 * Demonstrates the PrimeOS component system with variant/invariant properties
 */

// Component management system
const ComponentSystem = {
    // Currently active components
    activeComponents: [],
    
    // Initialize the component registry display
    init: function() {
        // Initialize component registry display
        this.initRegistryDisplay();
        
        // Initialize component creation controls
        this.initComponentControls();
        
        // Create a few sample components to demonstrate the system
        this.createSampleComponents();
    },
    
    // Initialize the component registry display
    initRegistryDisplay: function() {
        const registryDiv = document.getElementById('component-registry');
        
        if (!registryDiv) return;
        
        // Create registry display elements
        const registryHeader = document.createElement('div');
        registryHeader.className = 'registry-header';
        registryHeader.innerHTML = `
            <h4>Component Registry</h4>
            <span class="component-count">Components: 0</span>
        `;
        
        const registryList = document.createElement('div');
        registryList.className = 'registry-list';
        registryList.id = 'registry-list';
        
        registryDiv.appendChild(registryHeader);
        registryDiv.appendChild(registryList);
        
        // Store references
        this.registryList = registryList;
        this.componentCountDisplay = registryHeader.querySelector('.component-count');
    },
    
    // Initialize component control buttons
    initComponentControls: function() {
        // Create component button
        const createBtn = document.getElementById('create-component');
        if (createBtn) {
            createBtn.addEventListener('click', () => this.createRandomComponent());
        }
        
        // Update component button
        const updateBtn = document.getElementById('update-component');
        if (updateBtn) {
            updateBtn.addEventListener('click', () => this.updateRandomComponent());
        }
        
        // Delete component button
        const deleteBtn = document.getElementById('delete-component');
        if (deleteBtn) {
            deleteBtn.addEventListener('click', () => this.deleteRandomComponent());
        }
    },
    
    // Create sample components to demonstrate the system
    createSampleComponents: function() {
        // Create a counter component
        this.createComponent({
            meta: {
                name: 'Counter',
                description: 'A simple counter component'
            },
            variant: {
                count: 0,
                color: '#3498db'
            },
            invariant: {
                increment: function() {
                    this.setState({ count: this.variant.count + 1 });
                    return this.variant.count;
                },
                decrement: function() {
                    this.setState({ count: Math.max(0, this.variant.count - 1) });
                    return this.variant.count;
                },
                constraints: [
                    {
                        check: state => state.count >= 0,
                        weight: 2,
                        name: 'NonNegativeCount'
                    }
                ]
            }
        });
        
        // Create a text component
        this.createComponent({
            meta: {
                name: 'TextDisplay',
                description: 'A text display component'
            },
            variant: {
                text: 'Hello PrimeOS!',
                fontSize: 16,
                fontWeight: 'normal'
            },
            invariant: {
                setBold: function() {
                    this.setState({ fontWeight: 'bold' });
                },
                setNormal: function() {
                    this.setState({ fontWeight: 'normal' });
                },
                constraints: [
                    {
                        check: state => state.fontSize >= 8 && state.fontSize <= 36,
                        weight: 1,
                        name: 'ValidFontSize'
                    }
                ]
            }
        });
    },
    
    // Create a new component with the given configuration
    createComponent: function(config) {
        try {
            // Create a custom component implementation since Prime.createComponent isn't available
            const componentId = config.meta?.id || `${config.meta?.name || 'component'}-${Math.random().toString(36).substring(2, 9)}`;
            
            const component = {
                // Meta: contextual information and metadata
                meta: {
                    id: componentId,
                    name: config.meta?.name || 'UnnamedComponent',
                    description: config.meta?.description || '',
                    initialized: false,
                    mounted: false
                },
                
                // Invariant: static assets and code
                invariant: config.invariant || {},
                
                // Variant: dynamic data and state
                variant: config.variant || {},
                
                // Set state helper function
                setState: function(newState) {
                    // Store previous state for comparison
                    const prevState = {...this.variant};
                    
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
                    
                    // Call update method if available
                    if (this.invariant.update && typeof this.invariant.update === 'function') {
                        this.invariant.update.call(this, newState, prevState);
                    }
                    
                    // Publish update event
                    if (Prime.EventBus && Prime.EventBus.publish) {
                        Prime.EventBus.publish('component:updated', {
                            id: this.meta.id,
                            name: this.meta.name,
                            changes: newState
                        });
                    }
                    
                    return this.variant;
                },
                
                // Lifecycle management
                lifecycle: {
                    initialize: function() {
                        // Initialize the component
                        if (component.invariant.initialize && typeof component.invariant.initialize === 'function') {
                            component.invariant.initialize.call(component);
                        }
                        
                        component.meta.initialized = true;
                        return true;
                    },
                    
                    mount: function(parent) {
                        if (!component.meta.initialized) {
                            this.initialize();
                        }
                        
                        component.meta.mounted = true;
                        
                        if (component.invariant.mount && typeof component.invariant.mount === 'function') {
                            component.invariant.mount.call(component, parent);
                        }
                        
                        return true;
                    },
                    
                    unmount: function() {
                        if (!component.meta.mounted) {
                            return false;
                        }
                        
                        component.meta.mounted = false;
                        
                        if (component.invariant.unmount && typeof component.invariant.unmount === 'function') {
                            component.invariant.unmount.call(component);
                        }
                        
                        return true;
                    }
                }
            };
            
            // Add any method from invariant as a direct method on the component
            for (const key in component.invariant) {
                if (typeof component.invariant[key] === 'function' && 
                    key !== 'initialize' && key !== 'mount' && key !== 'unmount' && 
                    key !== 'update' && key !== 'constraints') {
                    // Properly bind the method to the component to ensure 'this' context
                    component[key] = component.invariant[key].bind(component);
                }
            }
            
            // Initialize the component
            component.lifecycle.initialize();
            
            // Add to active components
            this.activeComponents.push(component);
            
            // Update registry display
            this.updateRegistryDisplay();
            
            // Publish event if EventBus is available
            if (Prime.EventBus && Prime.EventBus.publish) {
                Prime.EventBus.publish('component:created', {
                    id: component.meta.id,
                    name: component.meta.name
                });
            }
            
            // Log creation
            Framework.log(`Component created: ${component.meta.name} (${component.meta.id})`, 'success');
            
            return component;
        } catch (error) {
            Framework.log(`Failed to create component: ${error.message}`, 'error');
            console.error(error);
            return null;
        }
    },
    
    // Create a random component for demo purposes
    createRandomComponent: function() {
        // Component types for random generation
        const componentTypes = [
            {
                name: 'Vector',
                variantGenerator: () => ({
                    values: Array.from({ length: 3 }, () => Math.floor(Math.random() * 100)),
                    color: `#${Math.floor(Math.random() * 16777215).toString(16).padStart(6, '0')}`
                }),
                invariantGenerator: () => ({
                    normalize: function() {
                        const values = this.variant.values;
                        const magnitude = Math.sqrt(values.reduce((sum, val) => sum + val * val, 0));
                        
                        if (magnitude === 0) return values;
                        
                        const normalized = values.map(val => val / magnitude);
                        this.setState({ values: normalized });
                        
                        return normalized;
                    },
                    add: function(otherVector) {
                        if (!otherVector || !otherVector.length) return this.variant.values;
                        
                        const result = this.variant.values.map(
                            (val, idx) => val + (otherVector[idx] || 0)
                        );
                        
                        this.setState({ values: result });
                        return result;
                    },
                    constraints: [
                        {
                            check: state => state.values && state.values.every(val => !isNaN(val)),
                            weight: 2,
                            name: 'ValidVectorValues'
                        }
                    ]
                })
            },
            {
                name: 'ColorPalette',
                variantGenerator: () => ({
                    primary: `#${Math.floor(Math.random() * 16777215).toString(16).padStart(6, '0')}`,
                    secondary: `#${Math.floor(Math.random() * 16777215).toString(16).padStart(6, '0')}`,
                    accent: `#${Math.floor(Math.random() * 16777215).toString(16).padStart(6, '0')}`
                }),
                invariantGenerator: () => ({
                    invertColors: function() {
                        const invertHex = hex => {
                            const rgb = parseInt(hex.slice(1), 16);
                            const r = 255 - ((rgb >> 16) & 0xff);
                            const g = 255 - ((rgb >> 8) & 0xff);
                            const b = 255 - (rgb & 0xff);
                            return `#${(r << 16 | g << 8 | b).toString(16).padStart(6, '0')}`;
                        };
                        
                        this.setState({
                            primary: invertHex(this.variant.primary),
                            secondary: invertHex(this.variant.secondary),
                            accent: invertHex(this.variant.accent)
                        });
                    },
                    constraints: [
                        {
                            check: state => /^#[0-9A-F]{6}$/i.test(state.primary),
                            weight: 1,
                            name: 'ValidPrimaryColor'
                        },
                        {
                            check: state => /^#[0-9A-F]{6}$/i.test(state.secondary),
                            weight: 1,
                            name: 'ValidSecondaryColor'
                        }
                    ]
                })
            },
            {
                name: 'DataPoint',
                variantGenerator: () => ({
                    x: Math.random() * 100,
                    y: Math.random() * 100,
                    label: `Point-${Math.floor(Math.random() * 1000)}`
                }),
                invariantGenerator: () => ({
                    distanceFromOrigin: function() {
                        return Math.sqrt(
                            this.variant.x * this.variant.x + 
                            this.variant.y * this.variant.y
                        );
                    },
                    constraints: [
                        {
                            check: state => !isNaN(state.x) && !isNaN(state.y),
                            weight: 2,
                            name: 'ValidCoordinates'
                        }
                    ]
                })
            }
        ];
        
        // Select a random component type
        const componentType = componentTypes[Math.floor(Math.random() * componentTypes.length)];
        
        // Generate a unique name
        const name = `${componentType.name}-${Math.floor(Math.random() * 1000)}`;
        
        // Create the component
        return this.createComponent({
            meta: {
                name,
                description: `A randomly generated ${componentType.name} component`
            },
            variant: componentType.variantGenerator(),
            invariant: componentType.invariantGenerator()
        });
    },
    
    // Update a random component
    updateRandomComponent: function() {
        if (this.activeComponents.length === 0) {
            Framework.log('No components to update', 'warning');
            return;
        }
        
        // Select a random component
        const component = this.activeComponents[
            Math.floor(Math.random() * this.activeComponents.length)
        ];
        
        try {
            // Update based on component type
            if (component.meta.name.startsWith('Counter')) {
                // Increment counter
                if (typeof component.increment === 'function') {
                    component.increment();
                } else if (component.variant.count !== undefined) {
                    // Fallback if method is missing
                    component.setState({ count: component.variant.count + 1 });
                } else {
                    // Warn if expected property is missing
                    console.warn(`Counter component ${component.meta.id} missing 'count' property`);
                }
            } else if (component.meta.name.startsWith('TextDisplay')) {
                // Toggle between bold and normal
                if (component.variant.fontWeight === 'bold') {
                    if (typeof component.setNormal === 'function') {
                        component.setNormal();
                    } else {
                        component.setState({ fontWeight: 'normal' });
                    }
                } else {
                    if (typeof component.setBold === 'function') {
                        component.setBold();
                    } else {
                        component.setState({ fontWeight: 'bold' });
                    }
                }
            } else if (component.meta.name.startsWith('Vector')) {
                // Add random values
                if (Array.isArray(component.variant.values)) {
                    const randomValues = Array.from({ length: component.variant.values.length }, 
                        () => Math.floor(Math.random() * 10) - 5);
                    
                    if (typeof component.add === 'function') {
                        component.add(randomValues);
                    } else {
                        // Fallback if method is missing
                        const newValues = component.variant.values.map(
                            (val, idx) => val + (randomValues[idx] || 0)
                        );
                        component.setState({ values: newValues });
                    }
                }
            } else if (component.meta.name.startsWith('ColorPalette')) {
                // Invert colors
                if (typeof component.invertColors === 'function') {
                    component.invertColors();
                } else if (component.variant.primary) {
                    // Fallback implementation
                    const invertHex = hex => {
                        const rgb = parseInt(hex.slice(1), 16);
                        const r = 255 - ((rgb >> 16) & 0xff);
                        const g = 255 - ((rgb >> 8) & 0xff);
                        const b = 255 - (rgb & 0xff);
                        return `#${(r << 16 | g << 8 | b).toString(16).padStart(6, '0')}`;
                    };
                    
                    const newState = {};
                    if (component.variant.primary) newState.primary = invertHex(component.variant.primary);
                    if (component.variant.secondary) newState.secondary = invertHex(component.variant.secondary);
                    if (component.variant.accent) newState.accent = invertHex(component.variant.accent);
                    
                    component.setState(newState);
                }
            } else if (component.meta.name.startsWith('DataPoint')) {
                // Move the point
                if (component.variant.x !== undefined && component.variant.y !== undefined) {
                    component.setState({
                        x: component.variant.x + (Math.random() * 10 - 5),
                        y: component.variant.y + (Math.random() * 10 - 5)
                    });
                }
            } else {
                // Generic update with random properties
                const variantKeys = Object.keys(component.variant);
                if (variantKeys.length > 0) {
                    const keyToUpdate = variantKeys[Math.floor(Math.random() * variantKeys.length)];
                    const currentValue = component.variant[keyToUpdate];
                    
                    // Update based on value type
                    if (typeof currentValue === 'number') {
                        // Add random offset to number
                        const newValue = currentValue + (Math.random() * 10 - 5);
                        component.setState({ [keyToUpdate]: newValue });
                    } else if (typeof currentValue === 'string') {
                        // Append random string
                        const newValue = `${currentValue}-${Math.floor(Math.random() * 100)}`;
                        component.setState({ [keyToUpdate]: newValue });
                    } else if (Array.isArray(currentValue)) {
                        // Modify array elements
                        const newArray = currentValue.map(v => 
                            typeof v === 'number' ? v + (Math.random() * 2 - 1) : v
                        );
                        component.setState({ [keyToUpdate]: newArray });
                    }
                }
            }
            
            // Update registry display
            this.updateRegistryDisplay();
            
            // Publish event
            Prime.EventBus.publish('component:updated', {
                id: component.meta.id,
                name: component.meta.name
            });
            
            // Log update
            Framework.log(`Component updated: ${component.meta.name} (${component.meta.id})`);
            
        } catch (error) {
            Framework.log(`Failed to update component: ${error.message}`, 'error');
            console.error(error);
        }
    },
    
    // Delete a random component
    deleteRandomComponent: function() {
        if (this.activeComponents.length === 0) {
            Framework.log('No components to delete', 'warning');
            return;
        }
        
        // Select a random component
        const index = Math.floor(Math.random() * this.activeComponents.length);
        const component = this.activeComponents[index];
        
        try {
            // Remove component from the active list
            this.activeComponents.splice(index, 1);
            
            // Update registry display
            this.updateRegistryDisplay();
            
            // Publish event
            Prime.EventBus.publish('component:deleted', {
                id: component.meta.id,
                name: component.meta.name
            });
            
            // Log deletion
            Framework.log(`Component deleted: ${component.meta.name} (${component.meta.id})`);
            
        } catch (error) {
            Framework.log(`Failed to delete component: ${error.message}`, 'error');
            console.error(error);
        }
    },
    
    // Update the component registry display
    updateRegistryDisplay: function() {
        if (!this.registryList || !this.componentCountDisplay) return;
        
        // Update component count
        this.componentCountDisplay.textContent = `Components: ${this.activeComponents.length}`;
        
        // Clear registry list
        this.registryList.innerHTML = '';
        
        // Add component entries
        this.activeComponents.forEach(component => {
            const componentEntry = document.createElement('div');
            componentEntry.className = 'component-entry';
            componentEntry.dataset.id = component.meta.id;
            
            // Format variant data for display
            const variantData = Object.entries(component.variant)
                .map(([key, value]) => {
                    // Format value based on type
                    let displayValue = value;
                    if (typeof value === 'object' && value !== null) {
                        displayValue = JSON.stringify(value).slice(0, 20) + '...';
                    } else if (typeof value === 'string') {
                        displayValue = value.length > 20 ? value.slice(0, 17) + '...' : value;
                    }
                    return `<span class="prop-name">${key}:</span> <span class="prop-value">${displayValue}</span>`;
                })
                .join(', ');
            
            componentEntry.innerHTML = `
                <div class="component-header">
                    <strong>${component.meta.name}</strong>
                    <span class="component-id">${component.meta.id}</span>
                </div>
                <div class="component-variant">${variantData}</div>
            `;
            
            this.registryList.appendChild(componentEntry);
        });
        
        // Update component view
        this.updateComponentView();
    },
    
    // Update the component visualization
    updateComponentView: function() {
        const componentView = document.getElementById('component-view');
        if (!componentView) return;
        
        // Clear existing content
        componentView.innerHTML = '';
        
        if (this.activeComponents.length === 0) {
            componentView.innerHTML = '<div class="no-components">No components to display</div>';
            return;
        }
        
        // Create component visualization
        const componentCanvas = document.createElement('canvas');
        componentCanvas.width = componentView.clientWidth || 400;
        componentCanvas.height = componentView.clientHeight || 200;
        componentView.appendChild(componentCanvas);
        
        const ctx = componentCanvas.getContext('2d');
        if (!ctx) return;
        
        // Clear canvas
        ctx.clearRect(0, 0, componentCanvas.width, componentCanvas.height);
        
        // Draw background
        ctx.fillStyle = '#f8f9fa';
        ctx.fillRect(0, 0, componentCanvas.width, componentCanvas.height);
        
        // Draw components
        const componentRadius = 30;
        const padding = componentRadius * 2;
        const availableWidth = componentCanvas.width - padding * 2;
        const centerY = componentCanvas.height / 2;
        
        // Position components evenly across canvas
        const spacing = this.activeComponents.length <= 1 ? 
            0 : availableWidth / (this.activeComponents.length - 1);
        
        this.activeComponents.forEach((component, index) => {
            const x = this.activeComponents.length <= 1 ? 
                componentCanvas.width / 2 : padding + spacing * index;
            
            // Determine component color
            let color = '#3498db';
            if (component.variant.color) {
                color = component.variant.color;
            } else if (component.meta.name.toLowerCase().includes('vector')) {
                color = '#e74c3c';
            } else if (component.meta.name.toLowerCase().includes('text')) {
                color = '#2ecc71';
            } else if (component.meta.name.toLowerCase().includes('counter')) {
                color = '#f39c12';
            } else if (component.meta.name.toLowerCase().includes('color')) {
                color = component.variant.primary || '#9b59b6';
            } else if (component.meta.name.toLowerCase().includes('data')) {
                color = '#1abc9c';
            }
            
            // Draw component circle
            ctx.fillStyle = color;
            ctx.beginPath();
            ctx.arc(x, centerY, componentRadius, 0, Math.PI * 2);
            ctx.fill();
            
            // Draw component name
            ctx.fillStyle = '#fff';
            ctx.font = 'bold 12px sans-serif';
            ctx.textAlign = 'center';
            ctx.textBaseline = 'middle';
            
            // Format name to fit
            const name = component.meta.name.length > 10 ? 
                component.meta.name.slice(0, 7) + '...' : component.meta.name;
            ctx.fillText(name, x, centerY);
            
            // Draw connections between components
            if (index > 0) {
                const prevX = padding + spacing * (index - 1);
                
                ctx.strokeStyle = 'rgba(52, 152, 219, 0.4)';
                ctx.lineWidth = 2;
                ctx.beginPath();
                ctx.moveTo(prevX + componentRadius, centerY);
                ctx.lineTo(x - componentRadius, centerY);
                ctx.stroke();
            }
        });
    }
};

// Initialize component system when DOM is ready
document.addEventListener('DOMContentLoaded', function() {
    ComponentSystem.init();
});