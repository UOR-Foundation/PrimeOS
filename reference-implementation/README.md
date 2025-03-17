# PrimeOS Reference Implementation

The PrimeOS Reference Implementation is a fully-functional, web-based operating system powered by the Prime Framework. It demonstrates the core capabilities of PrimeOS as a platform for building and running applications with high coherence, mathematical integrity, and seamless integration across all system layers.

## What is PrimeOS?

PrimeOS is an operating system designed around the principles of mathematical coherence, event-driven architecture, and component-based design. Unlike traditional operating systems that merely orchestrate hardware and software resources, PrimeOS creates a unified computational environment where:

- **Data maintains mathematical integrity** across all system interactions
- **Applications communicate seamlessly** through a unified event model
- **System resources form a coherent whole** maintained through constraint-based optimization
- **User identity and permissions** are integrated throughout all system components
- **Local and remote resources** are accessed through a unified interface

## Core Services

The reference implementation includes the following core services:

### 1. Identity & Authentication System
- **Prime Identity Provider (PIP)** - Secure user authentication with optional multi-factor authentication
- **Permission Management** - Granular access control for system resources
- **Identity Coherence** - Maintains consistent user identity across all applications
- **Credential Management** - Secure storage and management of user credentials

### 2. Storage & Data Management
- **PrimeStore** - IndexedDB-based persistent storage with coherence validation
- **Resource Manager** - Unified access to local and remote data sources
- **Data Coherence Engine** - Ensures mathematical consistency of stored data
- **Backup & Sync Service** - Automatic data backup and synchronization with cloud services

### 3. Application Platform
- **Application Launcher** - Discovers, installs, and launches Prime applications
- **Package Manager** - Manages installation, updates, and dependencies for applications
- **Runtime Environment** - Provides APIs for applications to utilize system services
- **Inter-Application Communication** - Enables secure data and event sharing between applications

### 4. User Interface System
- **Shell Environment** - The primary user interface for interacting with PrimeOS
- **Component Library** - Reusable UI components with coherence-aware state management
- **Adaptive Layout Engine** - Automatically adapts interface to different screen sizes and devices
- **Accessibility Layer** - Ensures all interfaces are accessible to users with disabilities

### 5. System Management
- **Resource Monitor** - Tracks system performance and resource utilization
- **Coherence Optimization** - Automatically optimizes system coherence
- **Diagnostics & Troubleshooting** - Tools for system health monitoring and issue resolution
- **Update & Recovery** - Manages system updates and provides recovery mechanisms

## Implemented Applications

The reference implementation currently includes these essential applications:

### Productivity Suite
- **Text Editor** - A simple text editor for creating and editing documents
- **Calculator** - Basic calculator application with keyboard support

### Utilities
- **File Explorer** - Browse and manage virtual files and directories
- **Settings** (placeholder) - System configuration interface

### Application Features
- Application lifecycle management (launch, suspend, resume, close)
- User preferences and state persistence
- Inter-application communication
- File handling between applications
- Responsive user interfaces with light/dark themes

## Architecture Overview

PrimeOS is built on a four-tier architecture that provides layers of abstraction while maintaining mathematical coherence throughout:

### Base0: Mathematical Foundation
The mathematical core of PrimeOS, implementing:
- Vector and tensor mathematics with precision guarantees
- Coherence calculation and validation
- Mathematical error detection and correction
- Clifford algebra and Lie group operations

### Base1: Core System
Core functionality that builds upon the mathematical foundation:
- Universal Object Reference (UOR) system for unified resource addressing
- EventBus for system-wide event propagation
- Identity and permission system
- Storage and resource management

### Base2: Component Framework
Component-based application framework with:
- Component registry and lifecycle management
- Variant/invariant property separation for optimal updates
- Resource allocation and optimization
- Constraint-based coherence validation

### Base3: Application Layer
User-facing applications and interfaces:
- Application lifecycle and intercommunication
- UI rendering and interaction
- User experience customization
- Resource utilization and optimization

## Getting Started

### Local Development

To run the PrimeOS Reference Implementation locally:

1. Clone the repository
   ```bash
   git clone https://github.com/your-username/PrimeOS.git
   cd PrimeOS/reference-implementation
   ```

2. Install dependencies
   ```bash
   npm install
   ```

3. Run tests to verify the implementation
   ```bash
   npm test
   npm run test:shell
   ```

4. Launch the application
   ```bash
   npm start
   ```

### Available Commands

```bash
# Building
npm run build        # Build all packages
npm run build:dev    # Build for development
npm run build:prod   # Build for production

# Testing
npm test             # Run all tests
npm run test:shell   # Run shell integration tests

# Development
npm start            # Start development server
```

### Online Demo

Experience PrimeOS without installation at:
[https://uor-foundation.github.io/PrimeOS/reference-implementation/](https://uor-foundation.github.io/PrimeOS/reference-implementation/)

## Implementation Details

### Directory Structure

- `apps/` - Built-in applications
  - `text-editor/` - Text editor application
  - `calculator/` - Calculator application
  - `file-explorer/` - File explorer application
- `core/` - Core system services
  - `identity/` - Identity management system
    - `identity-provider.js` - User authentication
  - `storage/` - Storage and data management 
    - `primestore.js` - Persistent data storage
  - `apps/` - Application support
    - `app-api.js` - Application API
  - `shell/` - Shell system
    - `shell.js` - Main shell implementation
    - `index.js` - Shell initialization
    - `shell.css` - Shell styling
- `css/` - Stylesheets
  - `styles.css` - Global styles
- `js/` - JavaScript modules
  - `app.js` - Main application entry point
  - `components.js` - UI component definitions
  - `framework.js` - Core framework code
  - `visualization.js` - Data visualization utilities
- `tests/` - Test suite
  - `shell-tests.js` - Shell unit tests
  - `shell-integration-tests.js` - Shell integration tests
- `index.html` - Main entry point

### Technology Stack

- **Core**: PrimeOS Framework (JavaScript ES6+)
- **Storage**: IndexedDB with coherence validation
- **UI Rendering**: DOM-based component system
- **Event System**: Custom EventBus for communication
- **State Management**: Variant/Invariant pattern for efficient updates
- **Application Lifecycle**: Suspended/Active states for resource optimization

## Implementation Progress

The current implementation focuses on core functionality:

### Completed Features
- ✅ Shell environment with desktop, taskbar, app launcher, and notifications
- ✅ Window management system (create, minimize, maximize, close)
- ✅ Application API with lifecycle management
- ✅ Inter-application communication
- ✅ Persistent storage system
- ✅ File handling between applications
- ✅ Three demo applications (Text Editor, Calculator, File Explorer)

### Upcoming Features
- 🔲 User authentication improvements
- 🔲 Advanced window management (snap, resize)
- 🔲 More application demos
- 🔲 Package installation system
- 🔲 Multi-user support
- 🔲 Cloud synchronization

### Extending the System
You can create new applications by:
1. Creating a new directory in `/apps/`
2. Implementing an application that follows the AppAPI pattern
3. Updating the application registry in the shell

## Contributing

We welcome contributions to the PrimeOS Reference Implementation! Please see our [Contribution Guidelines](CONTRIBUTING.md) for details on how to get involved.

## License

PrimeOS is released under the MIT License. See the LICENSE file for details.