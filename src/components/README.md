# PrimeOS Component System

## Component Lifecycle

The PrimeOS component system implements a unified lifecycle management system that supports both `init()` and `initialize()` methods for backwards compatibility.

### Lifecycle Methods

Components go through the following lifecycle phases:

1. **Creation**: When a component is created using `Prime.createComponent()`
   - The component object is constructed with meta, invariant, and variant sections
   - The component is automatically initialized

2. **Initialization**: Happens automatically during creation
   - Checks for and calls `init()` method first (for compatibility with tests)
   - Falls back to `initialize()` method if `init()` is not available
   - Sets both `component._initialized` and `component.meta.initialized` to `true`
   - Registers with coherence system if available
   - Emits the 'initialize' event

3. **Mounting**: Called explicitly or when adding as a child
   - Runs initialization if not already initialized
   - Sets parent reference and adds to parent's children
   - Calls the `mount()` handler if available
   - Emits the 'mount' event
   - Sets `component.meta.mounted` to `true`

4. **Updates**: State changes throughout the component's life
   - Validates changes against constraints (if any)
   - Updates the variant state
   - Calls the `update()` handler if available
   - Emits the 'update' event
   - Publishes to the global EventBus

5. **Unmounting**: Removing from parent
   - Calls the `unmount()` handler if available
   - Removes from parent's children
   - Unmounts all children recursively
   - Clears parent reference and children array
   - Unregisters from coherence system
   - Sets `component.meta.mounted` to `false`

6. **Destruction**: Final cleanup
   - Unmounts if still mounted
   - Calls the `destroy()` handler if available
   - Emits the 'destroy' event
   - Clears all references
   - Sets `component.meta.destroyed` to `true`

### Event System

Components use a flexible event system:

- **on(event, callback)**: Register an event listener
- **off(event, callback)**: Remove an event listener
- **emit(event, data)**: Trigger an event with optional data

The component's events are tracked in the `_events` array for debugging.

### Component Structure

A typical component has this structure:

```javascript
const component = Prime.createComponent({
  meta: {
    name: "ExampleComponent",
    id: "example-component-123",
    // ... other metadata
  },
  invariant: {
    // Lifecycle methods
    init: function() {
      // Called during initialization
      this._events.push("init");
    },
    
    mount: function(parent) {
      // Called when mounting to a parent
    },
    
    update: function(newState, prevState) {
      // Called when state changes
    },
    
    unmount: function() {
      // Called when removed from parent
    },
    
    destroy: function() {
      // Called when component is destroyed
    },
    
    // Component constraints (optional)
    constraints: [
      Prime.coherence.createConstraint(
        state => state.value >= 0,
        { name: "NonNegativeValue", weight: 1 }
      )
    ],
    
    // Component methods
    incrementValue: function() {
      this.setState({ value: this.variant.value + 1 });
    }
  },
  variant: {
    // Initial state
    value: 0
  }
});
```

### Best Practices

1. Always define both `init()` and `initialize()` methods for maximum compatibility
2. Use events for loose coupling between components
3. Define constraints for state validation
4. Use the lifecycle methods for proper resource management
5. Prefer the component's setState method over direct mutations