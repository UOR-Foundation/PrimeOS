# App Factory Integration Plan

This document outlines the integration strategy for incorporating the App Factory into the PrimeOS Reference Implementation.

## 1. Storage Integration

### Implementation Details

1. **Store Schema Extensions**
   - Add a new `app_factory_projects` store to PrimeStore
   - Create indices for project status, creation date, and owner
   - Add schema validation for project data structure

2. **Project Persistence**
   - Store project metadata in `app_factory_projects` collection
   - Store generated code files in the existing `files` collection with appropriate references
   - Track project version history for iterative improvement

3. **Integration with File Structure**
   ```javascript
   // /core/app-factory/utils/persistence.js
   class AppFactoryStorage {
     constructor(store) {
       this.store = store;
       this.projectCollection = 'app_factory_projects';
       this.fileCollection = 'files';
     }
     
     async saveProject(project) {
       return this.store.put(this.projectCollection, project);
     }
     
     async getProject(projectId) {
       return this.store.get(this.projectCollection, projectId);
     }
     
     async saveProjectFiles(projectId, files) {
       const fileEntries = files.map(file => ({
         id: `${projectId}_${file.path.replace(/\//g, '_')}`,
         projectId: projectId,
         path: file.path,
         content: file.content,
         type: 'app_factory_file'
       }));
       
       return this.store.saveAll(this.fileCollection, fileEntries);
     }
     
     async getProjectFiles(projectId) {
       return this.store.query({
         index: 'projectId',
         value: projectId,
         collection: this.fileCollection
       });
     }
   }
   ```

4. **Modifications to AppFactoryManager**
   - Update to use PrimeStore for all persistence operations
   - Add proper error handling and transaction support

## 2. User Configuration

### Implementation Details

1. **User Preferences Schema**
   - Add App Factory preferences to the existing user preferences structure
   - Create default values for API keys, template preferences, etc.

2. **Configuration UI**
   - Add UI components for managing App Factory settings
   - Create preference panes for API credentials, default templates, GitHub integration

3. **Integration Points**
   ```javascript
   // /core/app-factory/utils/configuration.js
   class AppFactoryConfig {
     constructor(store, userId) {
       this.store = store;
       this.userId = userId;
       this.preferencesKey = `user_preferences_${userId}`;
     }
     
     async getPreferences() {
       const userPrefs = await this.store.get('system', this.preferencesKey) || {};
       
       // Return App Factory specific preferences with defaults
       return {
         apiKey: userPrefs.appFactory?.apiKey || '',
         templates: userPrefs.appFactory?.templates || 'default',
         defaultPublishTarget: userPrefs.appFactory?.defaultPublishTarget || 'local',
         githubUsername: userPrefs.appFactory?.githubUsername || '',
         githubToken: userPrefs.appFactory?.githubToken || '',
         ...userPrefs.appFactory
       };
     }
     
     async savePreferences(appFactoryPrefs) {
       // Get existing user preferences
       const userPrefs = await this.store.get('system', this.preferencesKey) || {};
       
       // Update only App Factory section
       userPrefs.appFactory = {
         ...userPrefs.appFactory,
         ...appFactoryPrefs
       };
       
       return this.store.put('system', this.preferencesKey, userPrefs);
     }
   }
   ```

4. **API Key Management**
   - Add secure storage for Claude API keys
   - Implement per-user API key storage
   - Add usage tracking and quota management

## 3. App Import/Export

### Implementation Details

1. **Bundle Integration**
   - Connect to existing BundleManager for app packaging
   - Use the BundleManager createBundle/importBundle methods
   - Add App Factory specific metadata to bundles

2. **Import Workflow**
   ```javascript
   // Modified method in app-factory-manager.js
   async importExistingApp(bundleId) {
     // Get the bundle from BundleManager
     const bundle = await this.bundleManager.getBundle(bundleId);
     
     if (!bundle) {
       throw new Error(`Bundle with ID ${bundleId} not found`);
     }
     
     // Create a new project from the bundle
     const project = {
       id: `imported_${bundle.id}_${Date.now()}`,
       name: bundle.name,
       description: bundle.description,
       importedFrom: bundleId,
       status: 'imported',
       createdAt: new Date(),
       updatedAt: new Date()
     };
     
     // Save the new project
     await this.storage.saveProject(project);
     
     // Extract files from the bundle
     const files = await this.bundleManager.extractBundleFiles(bundleId);
     
     // Save files to the project
     await this.storage.saveProjectFiles(project.id, files);
     
     // Derive a specification from the code
     const specification = await this.claudeService.deriveSpecificationFromCode(
       files,
       bundle.name,
       bundle.description
     );
     
     // Store the derived specification with the project
     project.specification = specification;
     await this.storage.saveProject(project);
     
     return project;
   }
   ```

3. **Export Workflow**
   ```javascript
   // Modified method in app-factory-manager.js
   async exportApp(projectId) {
     // Get project data
     const project = await this.storage.getProject(projectId);
     
     if (!project) {
       throw new Error(`Project with ID ${projectId} not found`);
     }
     
     // Get project files
     const files = await this.storage.getProjectFiles(projectId);
     
     // Create app manifest
     const manifest = this.appPublisher._generateAppManifest(project.specification);
     
     // Use BundleManager to create a bundle
     const bundleId = await this.bundleManager.createBundle({
       name: project.name,
       description: project.description,
       manifest,
       files,
       type: 'app'
     });
     
     return bundleId;
   }
   ```

4. **Reverse Engineering**
   - Implement code analysis for imported apps
   - Extract specifications and manifolds from existing apps

## 4. App Installation/Uninstallation

### Implementation Details

1. **Shell Integration**
   - Connect to Shell's app registration system
   - Register published apps with the app launcher
   - Handle app updates and version management

2. **Installation Process**
   ```javascript
   // Modified method in app-publisher.js
   async publishApp(projectId, options = {}) {
     // Get project data
     const project = await this.store.get(this.projectCollection, projectId);
     
     if (!project) {
       throw new Error(`Project with ID ${projectId} not found`);
     }
     
     // Create app bundle
     const bundleId = await this.createAppBundle(project);
     
     // Determine publish target
     const target = options.target || 'local';
     
     if (target === 'local') {
       // Install to local system
       await this.bundleManager.installBundle(bundleId);
       
       // Notify Shell to refresh app list
       this.eventBus.publish('apps:refresh', { source: 'appFactory' });
       
     } else if (target === 'github') {
       // Push to GitHub if credentials available
       if (!options.githubRepo) {
         throw new Error('GitHub repository URL required for GitHub publishing');
       }
       
       await this.publishToGitHub(bundleId, options.githubRepo);
     }
     
     // Update project status
     project.status = 'published';
     project.publishedAt = new Date();
     project.publishTarget = target;
     project.bundleId = bundleId;
     
     await this.store.put(this.projectCollection, project);
     
     return {
       success: true,
       bundleId,
       target
     };
   }
   ```

3. **Uninstallation Process**
   ```javascript
   // Add to app-publisher.js
   async uninstallApp(projectId) {
     // Get project data
     const project = await this.store.get(this.projectCollection, projectId);
     
     if (!project || !project.bundleId) {
       throw new Error(`Published app not found for project ${projectId}`);
     }
     
     // Use BundleManager to uninstall
     await this.bundleManager.uninstallBundle(project.bundleId);
     
     // Notify Shell to refresh app list
     this.eventBus.publish('apps:refresh', { source: 'appFactory' });
     
     // Update project status
     project.status = 'unpublished';
     project.unpublishedAt = new Date();
     
     await this.store.put(this.projectCollection, project);
     
     return {
       success: true
     };
   }
   ```

4. **Version Management**
   - Track app versions for iterative improvement
   - Support migration between versions
   - Handle app updates gracefully

## 5. Shell Integration

### Implementation Details

1. **App Factory Registration**
   - Register App Factory as a system application
   - Add App Factory to the system tray/menu
   - Create desktop shortcut for easy access

2. **App Launcher Modifications**
   ```javascript
   // Modify /core/shell/shell.js
   
   // Add App Factory to system apps
   initSystemApps() {
     // Existing system apps...
     
     // Add App Factory
     this.registerApp({
       id: 'app-factory',
       name: 'App Factory',
       description: 'AI-powered application creation',
       icon: 'app_factory_icon.svg',
       path: '/core/app-factory/index.js',
       isSystem: true,
       category: 'development'
     });
   }
   
   // Add App Factory button to app launcher
   renderAppLauncher() {
     // Existing code...
     
     // Add App Factory tile
     const appFactoryTile = document.createElement('div');
     appFactoryTile.className = 'app-launcher-tile system-app';
     appFactoryTile.innerHTML = `
       <img src="assets/icons/app_factory_icon.svg" alt="App Factory">
       <span>App Factory</span>
     `;
     appFactoryTile.addEventListener('click', () => {
       this.launchApp('app-factory');
     });
     
     this.appLauncherGrid.appendChild(appFactoryTile);
   }
   ```

3. **Window Management**
   - Define window behavior for App Factory UI
   - Support multiple project windows
   - Add code preview and editing capabilities

4. **UI/UX Integration**
   - Match PrimeOS design language
   - Support system theme changes
   - Implement responsive design for different window sizes

## 6. Event System Integration

### Implementation Details

1. **Event Bus Registration**
   - Register App Factory specific events
   - Listen for system events (user login, app installation, etc.)
   - Publish events for other components

2. **Event Definitions**
   ```javascript
   // Add to /core/app-factory/index.js
   
   // Define App Factory events
   const APP_FACTORY_EVENTS = {
     // Project lifecycle events
     PROJECT_CREATED: 'app-factory:project-created',
     PROJECT_UPDATED: 'app-factory:project-updated',
     PROJECT_DELETED: 'app-factory:project-deleted',
     
     // Generation events
     GENERATION_STARTED: 'app-factory:generation-started',
     GENERATION_PROGRESS: 'app-factory:generation-progress',
     GENERATION_COMPLETED: 'app-factory:generation-completed',
     GENERATION_FAILED: 'app-factory:generation-failed',
     
     // Testing events
     TESTS_STARTED: 'app-factory:tests-started',
     TESTS_COMPLETED: 'app-factory:tests-completed',
     
     // Publication events
     PUBLICATION_STARTED: 'app-factory:publication-started',
     PUBLICATION_COMPLETED: 'app-factory:publication-completed',
     PUBLICATION_FAILED: 'app-factory:publication-failed'
   };
   
   // Register for system events
   function registerEventHandlers(eventBus) {
     // Listen for user login to load projects
     eventBus.subscribe('identity:login', (data) => {
       appFactoryManager.loadUserProjects(data.userId);
     });
     
     // Listen for app installation to detect importable apps
     eventBus.subscribe('bundle:installed', (data) => {
       appFactoryManager.detectImportableApp(data.bundleId);
     });
     
     // Listen for theme changes
     eventBus.subscribe('system:theme-changed', (data) => {
       appFactoryUI.updateTheme(data.theme);
     });
   }
   ```

3. **Communication Patterns**
   - Define structured event data formats
   - Implement event acknowledgments for critical operations
   - Add error handling and retries

## 7. File Structure Updates

### New and Modified Files

1. **Core App Factory Integration**
   - `/core/app-factory/integration/bundle-integration.js` - BundleManager integration
   - `/core/app-factory/integration/shell-integration.js` - Shell integration
   - `/core/app-factory/integration/app-api-integration.js` - AppAPI integration
   - `/core/app-factory/utils/persistence.js` - Storage integration
   - `/core/app-factory/utils/configuration.js` - User configuration management

2. **UI Components**
   - `/core/app-factory/ui/app-factory-window.js` - Main App Factory window
   - `/core/app-factory/ui/project-browser.js` - Project listing and management
   - `/core/app-factory/ui/configuration-panel.js` - User settings UI
   - `/core/app-factory/ui/code-editor.js` - Integrated code editing

3. **Shell Modifications**
   - Update `/core/shell/shell.js` to register and launch App Factory
   - Update `/core/shell/index.js` for App Factory UI styling
   - Add App Factory icon to assets directory

4. **Bundle System Connection**
   - Update App Factory to use BundleManager for import/export
   - Add App Factory metadata to bundle manifests
   - Create version tracking for exported apps

## 8. Implementation Timeline

### Phase 1: Core Integration (2 weeks)
- Storage schema extension implementation
- Basic Shell integration
- Event system registration
- Initial UI components

### Phase 2: App Lifecycle Management (2 weeks)
- Import/Export functionality
- Installation/Uninstallation integration
- Version management system
- Basic user configuration

### Phase 3: Enhanced UI and Experience (2 weeks)
- Full UI integration with Shell design language
- Code editor with syntax highlighting
- Project browser with filtering and search
- Configuration panel with API key management

### Phase 4: Testing and Refinement (1 week)
- Comprehensive testing of integration points
- Performance optimization
- Error handling improvements
- Documentation updates

## 9. Testing Strategy

1. **Unit Tests**
   - Test storage integration components
   - Test bundle creation and extraction
   - Test configuration management
   - Test event handling

2. **Integration Tests**
   - Test App Factory with Shell interaction
   - Test import/export with BundleManager
   - Test app installation and launching
   - Test project persistence across sessions

3. **End-to-End Tests**
   - Complete app creation, testing, and publication workflow
   - App import, modification, and republication
   - User configuration persistence
   - Multi-app management scenarios