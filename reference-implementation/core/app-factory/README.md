# PrimeOS App Factory

A PrimeOS package that leverages the Anthropic Claude API to guide users through the process of creating and modifying applications, with automatic code generation, testing, and publishing capabilities.

## Overview

App Factory enables non-technical users to create PrimeOS applications through an AI-assisted workflow. The system:

1. **Guides** users through the app creation process using natural language
2. **Generates** fully-functional application code based on user requirements
3. **Tests** applications automatically with unit and integration tests
4. **Iterates** on code until all tests pass and quality checks succeed
5. **Publishes** completed applications to personal or community app stores

By harnessing the power of Claude's AI capabilities, App Factory democratizes app development within the PrimeOS ecosystem, allowing anyone to create, modify, and share applications.

## Programming Paradigm for Claude Integration

The Claude integration in App Factory is designed around a functional programming paradigm that emphasizes:

### Functional File-Based Architecture

- **Focused File Components**: Each generated file has a specific, well-defined purpose
- **Pure Functions**: Functions avoid side effects and maintain predictable behavior
- **Stateless Operations**: Operations process inputs to outputs without hidden state
- **Composition**: Complex functionality is built by composing simpler functions
- **Immutable Data**: Preference for immutable data structures to prevent unexpected changes

### PrimeOS App Specification Format

PrimeOS App specs contain a comprehensive index of all files within the app, with each file having:

1. **Clear Single Responsibility**: Each file handles one specific aspect of functionality
2. **Explicit Interfaces**: Files define clear input and output interfaces
3. **Dependency Documentation**: Dependencies between files are explicitly documented
4. **Type Annotations**: Strong typing via JSDoc for improved reliability
5. **Functional Composition**: Complex operations built through function composition
6. **Minimal Side Effects**: Isolating side effects to specific boundary files

### Beyond Traditional Files

PrimeOS provides new representations for data beyond traditional files:

1. **Object Stores**: Persistent, structured data storage beyond the file system
2. **Event Streams**: Message-based communication between components
3. **Reactive Bindings**: Declarative data relationships that update automatically
4. **Capability-Based Security**: Access control based on explicit capabilities
5. **Virtual Resources**: Abstract resources that might not map directly to files
6. **Composable UI Components**: UI elements that follow a functional composition model

### Claude Integration Design Principles

The Claude integration follows these key principles:

1. **Context Management**: Breaking down large tasks into focused contexts that fit within Claude's context window
2. **Iterative Refinement**: Using Claude to progressively refine app specifications and implementations
3. **Knowledge Integration**: Combining Claude's capabilities with PrimeOS-specific knowledge
4. **Clear Prompting**: Designing prompts that guide Claude toward the functional paradigm
5. **Verification-Driven**: Generating specifications and code that can be verified programmatically

This functional approach ensures that Claude-generated applications are modular, maintainable, and adhere to PrimeOS architecture standards.

## Architecture

The App Factory system consists of the following core components:

### 1. AppFactoryManager

Central service responsible for coordinating the app creation workflow:
- Manages the multi-step app creation process
- Tracks project state and progress
- Interfaces with the Claude API
- Handles template management and code generation
- Orchestrates testing and validation

### 2. ClaudeService

Handles communication with the Anthropic Claude API:
- Manages API credentials and rate limiting
- Constructs prompts for different creation phases
- Processes API responses
- Handles error conditions and retries

### 3. AppSpecGenerator

Transforms user requirements into formal application specifications:
- Guides domain identification
- Facilitates entity and relationship mapping
- Creates structural diagrams
- Produces detailed application specifications
- Validates specifications against PrimeOS requirements

### 4. CodeGenerator

Transforms application specifications into functional code:
- Generates application structure based on PrimeOS patterns
- Creates all necessary application files
- Implements required interfaces and APIs
- Produces modular, maintainable code
- Generates comprehensive unit tests

### 5. TestRunner

Verifies generated code meets quality and functional requirements:
- Runs unit tests against generated code
- Performs integration testing with PrimeOS environment
- Validates code against linting rules
- Reports test results and errors
- Provides feedback for code regeneration

### 6. AppPublisher

Helps users share their applications through PrimeOS bundle system:
- Creates app bundles using the PrimeOS bundling system
- Generates publication metadata
- Assists with setting up personal app repositories
- Provides GitHub integration for app sharing
- Creates documentation for published apps

### 7. AppFactoryUI

User interface for the App Factory system:
- Multi-step wizard for app creation
- Visual representation of app structure
- Real-time feedback on generation process
- Interactive code previews and editing
- Progress tracking and status indicators

## Workflow

The App Factory guides users through the following workflow:

### Phase 1: Domain Identification

1. **Purpose Definition**: User describes the app's high-level purpose
2. **Domain Exploration**: Identifies the problem domain and relevant concepts
3. **Audience Analysis**: Determines target users and their needs
4. **Feature Brainstorming**: Maps desired capabilities and features

### Phase 2: Requirements Gathering

1. **Entity Identification**: Defines key data entities in the application
2. **Relationship Mapping**: Establishes relationships between entities
3. **Interaction Modeling**: Describes how users will interact with the app
4. **Capability Specification**: Defines specific functions and operations

### Phase 3: Specification Creation

1. **Architecture Planning**: Determines app structure and component organization
2. **Interface Design**: Defines user interface elements and layouts
3. **Data Model Creation**: Specifies data structures and storage requirements
4. **API Design**: Defines internal and external interfaces
5. **Test Planning**: Establishes test cases and validation criteria

### Phase 4: Code Generation

1. **Scaffold Creation**: Generates basic app structure
2. **Component Implementation**: Creates individual app components
3. **Integration Code**: Implements PrimeOS integration points
4. **Test Generation**: Creates unit and integration tests
5. **Documentation**: Produces inline documentation and usage examples

### Phase 5: Testing and Validation

1. **Static Analysis**: Performs linting and code quality checks
2. **Unit Testing**: Runs generated unit tests
3. **Integration Testing**: Verifies PrimeOS compatibility
4. **Error Remediation**: Addresses test failures and issues
5. **Iteration**: Regenerates code as needed until all tests pass

### Phase 6: Publishing

1. **Bundle Creation**: Packages the app using PrimeOS bundling system
2. **Repository Setup**: Assists with setting up GitHub repository
3. **Documentation Generation**: Creates README and usage documentation
4. **Publication**: Guides publishing to personal or community app store
5. **Verification**: Confirms successful publication and accessibility

## File Structure

The App Factory package consists of the following files:

```
/core/app-factory/
  ├── README.md                   # Package documentation
  ├── index.js                    # Main entry point
  ├── app-factory-manager.js      # Workflow management and orchestration
  ├── claude-service.js           # Anthropic Claude API integration
  ├── app-spec-generator.js       # Specification generation module
  ├── code-generator.js           # Code generation from specifications
  ├── test-runner.js              # Test execution and validation
  ├── app-publisher.js            # Publication and distribution
  ├── app-factory-ui.js           # User interface components
  ├── templates/                  # Code generation templates
  │   ├── app-structure.js        # Basic app structure templates
  │   ├── component-templates.js  # UI component templates
  │   ├── data-models.js          # Data structure templates
  │   ├── test-templates.js       # Unit test templates
  │   └── readme-template.js      # Documentation templates
  ├── prompts/                    # Claude prompt templates
  │   ├── domain-prompts.js       # Domain identification prompts
  │   ├── requirements-prompts.js # Requirements gathering prompts
  │   ├── spec-prompts.js         # Specification creation prompts
  │   ├── code-prompts.js         # Code generation prompts
  │   ├── test-prompts.js         # Test creation prompts
  │   └── edit-prompts.js         # Code editing prompts
  └── utils/
      ├── validation.js           # Input and output validation
      ├── prompt-builder.js       # Dynamic prompt construction
      ├── code-parser.js          # Code analysis utilities
      ├── persistence.js          # Project state management
      └── github-integration.js   # GitHub repository integration
```

## API Overview

### AppFactoryManager

```javascript
// Create a new app project
createProject(projectName, description)

// Load an existing project
loadProject(projectId)

// Import an existing app for modification
importApp(appBundle)

// Start or continue the app creation workflow
continueWorkflow(projectId, currentStep)

// Get project status and progress
getProjectStatus(projectId)

// Generate application code
generateApp(projectId)

// Run tests on generated code
runTests(projectId)

// Publish app to repository
publishApp(projectId, repositoryUrl)
```

### ClaudeService

```javascript
// Initialize with API credentials
initialize(apiKey, options)

// Generate domain insights from user input
generateDomainInsights(description)

// Create entity model from requirements
createEntityModel(requirements)

// Generate application specification
generateAppSpecification(domainModel, entityModel)

// Generate application code from specification
generateCode(specification, templates)

// Improve code based on test results
improveCode(code, testResults, specification)
```

### AppFactoryUI

```javascript
// Create app factory UI in container
render(container)

// Set current workflow step
setStep(stepNumber, data)

// Show progress indicator
showProgress(status)

// Display generation results
showResults(projectData)

// Show code preview
showCodePreview(files)

// Show test results
showTestResults(results)
```

## Integration Points

The App Factory integrates with other PrimeOS components:

1. **PrimeOS Bundle System**: For packaging and distributing generated apps
   - Uses BundleManager for app import/export
   - Generates compliant bundle manifests
   - Supports versioning and updates
   - Handles app installation and uninstallation

2. **PrimeOS Shell**: For UI integration and app launching
   - Registers as a system application
   - Uses standard window management
   - Follows PrimeOS design language
   - Notifies the Shell of new/updated apps

3. **PrimeOS Storage (PrimeStore)**: For persisting project data and generated code
   - Stores projects in dedicated app_factory_projects collection
   - Uses files collection for code storage
   - Implements proper coherence validation
   - Supports versioning and history

4. **PrimeOS Identity**: For API authentication and app signing
   - Secures Claude API credentials per user
   - Signs generated app bundles
   - Manages user app permissions
   - Controls GitHub publishing credentials

5. **PrimeOS Event System**: For component communication
   - Publishes app creation/update events
   - Listens for system events
   - Implements structured event data
   - Handles asynchronous operations

See the detailed integration plan in `/core/app-factory/integration-plan.md` for implementation specifics.

## Security Considerations

1. **API Key Management**:
   - Secure storage of Claude API credentials in the user's encrypted preferences
   - Support for user-provided API keys with per-user isolation
   - Rate limiting and usage monitoring with quota enforcement
   - Optional key rotation and expiration policies

2. **Code Execution**:
   - Sandboxed testing environment for generated code
   - Static analysis and validation of generated code
   - Prevention of malicious code injection with security scanning
   - Runtime isolation of generated applications

3. **Data Privacy**:
   - Clear disclosure of data sent to Claude API
   - Minimal prompt construction to avoid sending sensitive data
   - Option to review all API requests before sending
   - Local-only mode for sensitive projects

4. **App Publishing**:
   - Verification of app integrity before publishing
   - Code signing with user identity
   - Repository access control with validation
   - App bundle integrity verification

5. **User Data Protection**:
   - Encrypted storage of project data
   - Access controls based on user identity
   - Options for exporting and backing up projects
   - Proper data sanitization before sharing

## Implementation Plan

### Phase 1: Core Architecture and System Integration
- Implement basic AppFactoryManager
- Create ClaudeService API integration
- Design persistence model for projects in PrimeStore
- Implement minimal UI for workflow navigation
- Integrate with Shell and BundleManager
- Set up app_factory_projects collection in PrimeStore
- Configure event system integration

### Phase 2: Requirements & Specification with Manifold Support
- Implement domain identification workflow
- Create entity and relationship modeling
- Build specification generator with manifold decomposition
- Design and implement specification validator
- Add mathematical coherence validation
- Implement Base 0-3 hierarchy mapping

### Phase 3: Advanced Code Generation
- Implement code template system with manifold structure
- Create code generation module
- Build test generation functionality
- Implement code validation and linting
- Generate proper meta/invariant/variant structures
- Support proper mathematical coherence

### Phase 4: Testing and Bundle Infrastructure
- Create test runner integration
- Implement result parsing and feedback
- Build code regeneration workflow
- Create test reporting interface
- Integrate with BundleManager for app packaging
- Set up app installation and update workflows

### Phase 5: Publication System
- Implement local app installation
- Implement GitHub repository integration
- Create documentation generator
- Build publication workflow
- Add app signing and verification
- Create versioning and update support

### Phase 6: UI and User Experience Enhancement
- Create full wizard interface
- Implement code preview and editing
- Add progress visualization
- Create interactive entity modeling UI
- Build configuration management interface
- Develop user-friendly error handling

See the detailed implementation timeline in `/core/app-factory/integration-plan.md` for specifics.

## Usage Examples

### Creating a New App

```javascript
// Initialize App Factory
const appFactory = new AppFactoryManager({
  claudeService,
  store,
  eventBus
});

// Create a new project
const projectId = await appFactory.createProject(
  "Task Manager",
  "A simple task management app for organizing personal tasks"
);

// Start the guided process
const workflow = await appFactory.continueWorkflow(projectId);

// After completing the wizard and generating code
const testResults = await appFactory.runTests(projectId);

if (testResults.success) {
  // Publish to personal GitHub repo
  await appFactory.publishApp(projectId, "https://github.com/username/primeos-apps");
}
```

### Modifying an Existing App

```javascript
// Import existing app
const projectId = await appFactory.importApp(appBundle);

// Get app specification
const spec = await appFactory.getAppSpecification(projectId);

// Update specification
spec.features.push({
  name: "Dark Mode",
  description: "Add dark mode support to the application"
});

// Regenerate app with new feature
await appFactory.regenerateApp(projectId, spec);

// Run tests on the updated app
const testResults = await appFactory.runTests(projectId);

// Export updated app
const updatedBundle = await appFactory.exportApp(projectId);
```

## Future Enhancements

1. **Collaborative Creation**: 
   - Allow multiple users to work on app projects simultaneously
   - Real-time collaboration with conflict resolution
   - Role-based access control for team members
   - Project forking and merging capabilities

2. **Template and Component Library**: 
   - User-contributed app templates and patterns
   - Manifold-structured reusable components
   - Visual component browser and selection
   - Versioned component registry with coherence validation

3. **Advanced AI Features**:
   - Fine-tuning Claude for specific application domains
   - Automated coherence optimization across manifolds
   - Learning from user preferences and patterns
   - Specialized domain-specific code generation models

4. **Visual App Designer**: 
   - Drag-and-drop interface for app creation
   - Visual manifold relationship editor
   - Real-time preview of generated applications
   - Interactive application flow modeling

5. **App Performance Suite**: 
   - Automated performance testing and optimization
   - Mathematical coherence analysis visualization
   - Resource usage profiling and optimization
   - Automated code improvement suggestions

6. **Enterprise Integration**:
   - Team management and collaboration features
   - Integration with corporate identity systems
   - Enterprise app catalog and distribution
   - Governance and compliance checking

7. **Extended Platform Support**:
   - Mobile app generation capabilities
   - Cross-platform application deployment
   - Integration with external services and APIs
   - Hardware device integration support

## Dependencies

- **Anthropic Claude API**: For AI-driven code generation and assistance
- **PrimeOS Bundle System**: For app packaging and distribution
- **Jest Testing Framework**: For unit and integration testing
- **ESLint**: For code quality validation
- **GitHub API**: For repository integration
- **CodeMirror**: For code previewing and editing

## Testing

The App Factory components are thoroughly tested using Jest and Puppeteer. Tests are organized into both Node.js unit tests and browser-based integration tests.

### Node.js Tests

1. **app-factory-tests.js**: Tests for the main App Factory functionality
2. **app-factory-components-tests.js**: Tests for key components like CoherenceEngine, ClaudeOrchestrator, and AppFactoryManager
3. **app-factory-bundle-manager-tests.js**: Comprehensive tests for BundleManager, covering:
   - Bundle creation and initialization
   - File management (add, remove, categorize)
   - Bundle validation
   - Bundle exporting and importing
   - Event notifications
4. **app-factory-utils-tests.js**: Tests for utility modules like claude-api, persistence, and configuration
5. **app-factory-integration-tests.js**: Tests for integration components that connect App Factory with other PrimeOS systems:
   - AppFactoryBundleIntegration: Tests for Bundle System integration
   - AppFactoryAppAPIIntegration: Tests for AppAPI lifecycle and system services integration
   - AppFactoryShellIntegration: Tests for Shell UI and window management integration

### Browser Integration Tests

The reference implementation provides browser integration tests using Puppeteer, allowing components to be tested in a real browser environment:

1. **test.html**: Main browser test page that tests basic Shell and UI components
2. **browser-secure-vault-test.html**: Tests for SecureVault's event notification system in a browser context

### Running Tests

```bash
# Run all Node.js unit tests
npm test

# Run specific App Factory tests
npm test -- -t "App Factory"

# Run BundleManager tests
npm test -- -t "App Factory BundleManager"

# Run browser integration tests
npm run test:browser

# Run secure vault browser tests specifically
npm run test:secure-vault

# Run all tests (Node.js and browser)
npm run test:all

# Get code coverage report
npm run test:coverage
```

The test suite provides over 90% code coverage for all App Factory components, ensuring reliability and stability across both Node.js and browser environments.