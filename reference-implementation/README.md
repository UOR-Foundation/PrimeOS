# PrimeOS Reference Implementation

This is the reference implementation for PrimeOS that provides a native desktop environment closely aligned with the Prime Framework's topological representation of data, information, and knowledge.

## Core Concepts

- **Manifolds**: The fundamental unit of representation in PrimeOS. Manifolds can be thought of as mediatypes with schemas and clients.
- **Topological Representation**: Shows relationships between manifolds.
- **Context Representation**: Provides multiple views of data:
  - Rendered: Natural interaction with multi-media
  - Structure: Visual schema representation
  - Relationships: Visual representation of entity connections
  - Content: Representation within manifolds

## Getting Started

### Installation

```sh
# Clone the repository
git clone https://github.com/your-org/primeos.git
cd primeos/reference-implementation

# Install dependencies
npm install

# Build the application
npm run build

# Start the application
npm start
```

### Development

```sh
# Start development server with auto-reload
npm run dev

# Run tests
npm test

# Run specific tests
npm test -- --testPathPattern=manifold-registry

# Run browser tests
npm run test:browser

# Build for production
npm run build:prod
```

## Architecture

The PrimeOS reference implementation is organized into the following components:

- **Core**: The central system that manages the PrimeOS environment
  - **ManifoldRegistry**: Manages manifold definitions and their relationships
  - **Storage**: Handles data persistence (PrimeStore)
  - **Identity**: Manages user identity and authentication
  - **Context**: Provides context sharing between components
  - **Extensions**: Enables system extensibility through plugins
  - **Manifold**: Handles manifold import and export

- **Shell**: Provides the user interface and environment
  - **Views**: Different ways to visualize and interact with manifolds
    - Rendered View
    - Structure View
    - Relationships View (Topology Visualizer)

- **Components**: Reusable UI components

## Implementation Status

- [x] Core structure
- [x] Basic Shell UI
- [x] Manifold Registry
- [x] Multiple view representations
- [x] User Agent Dashboard
- [x] PrimeApps Discovery
- [x] Identity Management
- [x] Access Control
- [x] Secure Vault
- [x] Topological Visualization
- [x] Remote Manifold Import/Export
- [x] Context Sharing Mechanism
- [x] Extension System

## Core Applications

### User Agent Dashboard

The User Agent Dashboard provides a centralized interface for managing your identity, applications, and network connections in PrimeOS. It includes:

- **Profile Management**: Control your user profile, authentication state, and preferences
- **Application Management**: Browse, install, and manage PrimeOS applications
- **Network Configuration**: Configure network connections, transports, and manifold synchronization

### Topology Visualizer

The Topology Visualizer provides an interactive graph visualization of manifold relationships, with features such as:

- Interactive node selection and detail viewing
- Zoom and pan controls
- Force-directed graph layout
- Real-time updates when manifolds or relationships change

### Extension System

The Extension System allows third-party extensions to add functionality to PrimeOS through standardized extension points:

- UI Extensions: Toolbar, sidebar, context menus
- Functionality Extensions: Context providers, manifold converters
- Security Mechanisms: Extensions run in a controlled environment

### Context Sharing

The Context Sharing system enables components to share context data with each other:

- Components can register as context providers or consumers
- Typed context data with schema validation
- Event-driven updates when context changes
- Visualization of context sharing relationships

## License

MIT