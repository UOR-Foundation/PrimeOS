/**
 * PrimeOS App Publisher
 * 
 * Service for publishing and distributing generated PrimeOS applications
 * through various channels (bundles, GitHub, etc.).
 */

class AppPublisher {
  /**
   * Creates a new App Publisher instance
   * @param {Object} options - Configuration options
   * @param {Object} options.store - PrimeStore instance for app persistence
   * @param {Object} options.eventBus - Event bus for notifications
   * @param {Object} options.bundleManager - Bundle manager for app packaging
   */
  constructor(options) {
    // Validate required dependencies
    if (!options.store) {
      throw new Error('AppPublisher requires a store instance');
    }
    
    // Store dependencies
    this.store = options.store;
    this.eventBus = options.eventBus || null;
    this.bundleManager = options.bundleManager || null;
    
    // GitHub integration settings
    this.githubConfig = options.githubConfig || {
      apiUrl: 'https://api.github.com',
      authMethod: 'token'
    };
    
    console.log('AppPublisher initialized');
  }
  
  /**
   * Create a bundle from app files
   * @param {Array} files - Array of file objects
   * @param {Object} metadata - App metadata
   * @returns {Promise<Object>} Bundle information
   */
  async createBundle(files, metadata) {
    if (!files || !Array.isArray(files)) {
      throw new Error('Files array is required');
    }
    
    if (!metadata || !metadata.name) {
      throw new Error('App metadata with name is required');
    }
    
    console.log(`Creating bundle for ${metadata.name}`);
    
    try {
      // Validate bundle manager availability
      if (!this.bundleManager) {
        throw new Error('Bundle manager is not available');
      }
      
      // Prepare bundle ID
      const bundleId = metadata.bundleId || 
        `com.primeos.${metadata.name.toLowerCase().replace(/\s+/g, '-')}`;
      
      // Create app record for bundling
      const appRecord = {
        id: bundleId,
        name: metadata.name,
        version: metadata.version || '1.0.0',
        author: metadata.author || 'PrimeOS App Factory',
        description: metadata.description || '',
        entryPoint: metadata.entryPoint || 'index.js',
        tags: metadata.tags || [],
        permissions: metadata.permissions || []
      };
      
      // Register the app
      await this.store.put({
        ...appRecord,
        type: 'app',
        registered: new Date().toISOString(),
        bundleable: true
      });
      
      // Prepare app files for storage
      const codeFiles = files.filter(file => !file.isResource).map(file => ({
        id: `${bundleId}:${file.path}`,
        path: file.path,
        appId: bundleId,
        name: file.path.split('/').pop(),
        type: 'file',
        isCode: true,
        content: file.content,
        encoding: 'text',
        created: new Date(),
        modified: new Date()
      }));
      
      const resourceFiles = files.filter(file => file.isResource).map(file => ({
        id: `${bundleId}:${file.path}`,
        path: file.path.replace(/^resources\//, ''),
        appId: bundleId,
        name: file.path.split('/').pop(),
        type: 'file',
        isCode: false,
        content: file.content,
        encoding: 'text',
        created: new Date(),
        modified: new Date()
      }));
      
      // Save all files
      await this.store.saveAll(null, [...codeFiles, ...resourceFiles]);
      
      // Create the bundle
      const bundle = await this.bundleManager.createBundle(bundleId);
      
      // Notify bundle creation
      this._notifyEvent('bundle-created', {
        bundleId,
        appName: metadata.name,
        fileCount: files.length
      });
      
      return {
        bundleId,
        bundle,
        metadata: appRecord
      };
    } catch (error) {
      console.error('Failed to create bundle:', error);
      throw error;
    }
  }
  
  /**
   * Export app as a standalone bundle file
   * @param {Array} files - Array of file objects
   * @param {Object} metadata - App metadata
   * @returns {Promise<Object>} Bundle object
   */
  async exportAppBundle(files, metadata) {
    if (!files || !Array.isArray(files)) {
      throw new Error('Files array is required');
    }
    
    if (!metadata || !metadata.name) {
      throw new Error('App metadata with name is required');
    }
    
    console.log(`Exporting bundle for ${metadata.name}`);
    
    try {
      // Prepare bundle ID
      const bundleId = metadata.bundleId || 
        `com.primeos.${metadata.name.toLowerCase().replace(/\s+/g, '-')}`;
      
      // Prepare manifest
      const manifest = {
        id: bundleId,
        name: metadata.name,
        version: metadata.version || '1.0.0',
        author: metadata.author || 'PrimeOS App Factory',
        description: metadata.description || '',
        entryPoint: metadata.entryPoint || 'index.js',
        tags: metadata.tags || [],
        permissions: metadata.permissions || [],
        compatibilityVersion: '1.0.0',
        created: new Date().toISOString()
      };
      
      // Prepare code and resources
      const code = {};
      const resources = {};
      
      for (const file of files) {
        const content = typeof btoa === 'function' ? 
          btoa(file.content) : 
          Buffer.from(file.content).toString('base64');
          
        if (file.isResource) {
          resources[file.path.replace(/^resources\//, '')] = content;
        } else {
          code[file.path] = content;
        }
      }
      
      // Create bundle
      const bundle = {
        manifest,
        code,
        resources
      };
      
      // Notify bundle export
      this._notifyEvent('bundle-exported', {
        bundleId,
        appName: metadata.name,
        fileCount: files.length
      });
      
      return bundle;
    } catch (error) {
      console.error('Failed to export app bundle:', error);
      throw error;
    }
  }
  
  /**
   * Publish app to GitHub repository
   * @param {Array} files - Array of file objects
   * @param {Object} metadata - App metadata
   * @param {Object} gitOptions - GitHub options
   * @returns {Promise<Object>} Publishing result
   */
  async publishToGitHub(files, metadata, gitOptions) {
    if (!files || !Array.isArray(files)) {
      throw new Error('Files array is required');
    }
    
    if (!metadata || !metadata.name) {
      throw new Error('App metadata with name is required');
    }
    
    if (!gitOptions || !gitOptions.repositoryUrl) {
      throw new Error('GitHub repository URL is required');
    }
    
    console.log(`Publishing to GitHub: ${gitOptions.repositoryUrl}`);
    
    try {
      // Validate GitHub token
      if (!gitOptions.token) {
        return {
          status: 'instructions',
          repositoryUrl: gitOptions.repositoryUrl,
          instructions: [
            '1. Create a new repository on GitHub',
            '2. Initialize with a README',
            '3. Clone the repository locally',
            '4. Copy the app files to the repository',
            '5. Create a bundle.json file with app metadata',
            '6. Commit and push the changes',
            '7. Your app is now published to GitHub!'
          ]
        };
      }
      
      // Parse repository URL
      const repoInfo = this._parseRepositoryUrl(gitOptions.repositoryUrl);
      
      if (!repoInfo) {
        throw new Error('Invalid GitHub repository URL');
      }
      
      // Create bundle.json for GitHub
      const bundleManifest = {
        name: metadata.name,
        version: metadata.version || '1.0.0',
        author: metadata.author || 'PrimeOS App Factory',
        description: metadata.description || '',
        entryPoint: metadata.entryPoint || 'index.js',
        generatedBy: 'PrimeOS App Factory',
        generatedOn: new Date().toISOString()
      };
      
      // Add bundle.json to files
      files.push({
        path: 'bundle.json',
        content: JSON.stringify(bundleManifest, null, 2),
        generated: true
      });
      
      // Check if repository exists
      const repoExists = await this._checkRepositoryExists(
        repoInfo.owner,
        repoInfo.repo,
        gitOptions.token
      );
      
      let result;
      
      if (repoExists) {
        // Push to existing repository
        result = await this._pushToExistingRepository(
          files,
          repoInfo,
          metadata,
          gitOptions
        );
      } else {
        // Create new repository
        result = await this._createNewRepository(
          files,
          repoInfo,
          metadata,
          gitOptions
        );
      }
      
      // Notify GitHub publish
      this._notifyEvent('github-published', {
        repositoryUrl: gitOptions.repositoryUrl,
        appName: metadata.name,
        fileCount: files.length
      });
      
      return result;
    } catch (error) {
      console.error('Failed to publish to GitHub:', error);
      
      // Return instructions as fallback
      return {
        status: 'error',
        error: error.message,
        repositoryUrl: gitOptions.repositoryUrl,
        instructions: [
          '1. Create a new repository on GitHub',
          '2. Initialize with a README',
          '3. Clone the repository locally',
          '4. Copy the app files to the repository',
          '5. Create a bundle.json file with app metadata',
          '6. Commit and push the changes',
          '7. Your app is now published to GitHub!'
        ]
      };
    }
  }
  
  /**
   * Parse GitHub repository URL
   * @private
   * @param {string} url - Repository URL
   * @returns {Object|null} Repository info
   */
  _parseRepositoryUrl(url) {
    // Match GitHub repository URL formats
    const patterns = [
      /github\.com\/([^\/]+)\/([^\/\.]+)(?:\.git)?$/,
      /github\.com\/([^\/]+)\/([^\/\.]+)(?:\.git)?\/$/,
      /^([^\/]+)\/([^\/\.]+)$/
    ];
    
    for (const pattern of patterns) {
      const match = url.match(pattern);
      if (match) {
        return {
          owner: match[1],
          repo: match[2]
        };
      }
    }
    
    return null;
  }
  
  /**
   * Check if a GitHub repository exists
   * @private
   * @param {string} owner - Repository owner
   * @param {string} repo - Repository name
   * @param {string} token - GitHub token
   * @returns {Promise<boolean>} Whether the repository exists
   */
  async _checkRepositoryExists(owner, repo, token) {
    try {
      // This is a reference implementation - in a real impl we would use GitHub API
      console.log(`Checking if repository exists: ${owner}/${repo}`);
      
      // Simulate API request
      return false;
    } catch (error) {
      console.error('Failed to check repository:', error);
      return false;
    }
  }
  
  /**
   * Create a new GitHub repository and push files
   * @private
   * @param {Array} files - App files
   * @param {Object} repoInfo - Repository info
   * @param {Object} metadata - App metadata
   * @param {Object} gitOptions - GitHub options
   * @returns {Promise<Object>} Result
   */
  async _createNewRepository(files, repoInfo, metadata, gitOptions) {
    // This is a reference implementation - in a real impl we would use GitHub API
    console.log(`Creating new repository: ${repoInfo.owner}/${repoInfo.repo}`);
    
    // Return successful result
    return {
      status: 'success',
      repositoryUrl: `https://github.com/${repoInfo.owner}/${repoInfo.repo}`,
      commitSha: '0123456789abcdef0123456789abcdef01234567',
      createdNew: true
    };
  }
  
  /**
   * Push files to an existing GitHub repository
   * @private
   * @param {Array} files - App files
   * @param {Object} repoInfo - Repository info
   * @param {Object} metadata - App metadata
   * @param {Object} gitOptions - GitHub options
   * @returns {Promise<Object>} Result
   */
  async _pushToExistingRepository(files, repoInfo, metadata, gitOptions) {
    // This is a reference implementation - in a real impl we would use GitHub API
    console.log(`Pushing to existing repository: ${repoInfo.owner}/${repoInfo.repo}`);
    
    // Return successful result
    return {
      status: 'success',
      repositoryUrl: `https://github.com/${repoInfo.owner}/${repoInfo.repo}`,
      commitSha: '0123456789abcdef0123456789abcdef01234567',
      createdNew: false
    };
  }
  
  /**
   * Generate documentation for an app
   * @param {Array} files - Array of file objects
   * @param {Object} metadata - App metadata
   * @returns {Promise<Array>} Generated documentation files
   */
  async generateDocumentation(files, metadata) {
    if (!files || !Array.isArray(files)) {
      throw new Error('Files array is required');
    }
    
    if (!metadata || !metadata.name) {
      throw new Error('App metadata with name is required');
    }
    
    console.log(`Generating documentation for ${metadata.name}`);
    
    try {
      const docFiles = [];
      
      // Generate README.md if not exists
      if (!files.some(file => file.path === 'README.md')) {
        docFiles.push({
          path: 'README.md',
          content: this._generateReadme(metadata),
          generated: true,
          isDocumentation: true
        });
      }
      
      // Generate API documentation
      const apiDoc = await this._generateApiDocs(files, metadata);
      if (apiDoc) {
        docFiles.push({
          path: 'API.md',
          content: apiDoc,
          generated: true,
          isDocumentation: true
        });
      }
      
      // Generate usage guide
      docFiles.push({
        path: 'USAGE.md',
        content: this._generateUsageGuide(metadata),
        generated: true,
        isDocumentation: true
      });
      
      // Notify documentation generation
      this._notifyEvent('documentation-generated', {
        appName: metadata.name,
        docFileCount: docFiles.length
      });
      
      return docFiles;
    } catch (error) {
      console.error('Failed to generate documentation:', error);
      
      // Generate minimal README as fallback
      return [{
        path: 'README.md',
        content: this._generateMinimalReadme(metadata),
        generated: true,
        isDocumentation: true
      }];
    }
  }
  
  /**
   * Generate README content
   * @private
   * @param {Object} metadata - App metadata
   * @returns {string} README content
   */
  _generateReadme(metadata) {
    return `# ${metadata.name}

${metadata.description || 'A PrimeOS Application'}

## Overview

This application was built using the PrimeOS App Factory.

## Features

${metadata.features ? metadata.features.map(f => `- ${f}`).join('\n') : '- Feature list coming soon'}

## Installation

1. Import the app bundle into your PrimeOS environment
2. Launch the app from the PrimeOS shell

## Development

To modify this application:

1. Open in the PrimeOS App Factory
2. Modify as needed
3. Export or publish your changes

## License

${metadata.license || 'MIT'}

## Created

This app was generated on ${new Date().toISOString().split('T')[0]} using PrimeOS App Factory.
`;
  }
  
  /**
   * Generate minimal README content
   * @private
   * @param {Object} metadata - App metadata
   * @returns {string} Minimal README content
   */
  _generateMinimalReadme(metadata) {
    return `# ${metadata.name}

${metadata.description || 'A PrimeOS Application'}

Generated by PrimeOS App Factory on ${new Date().toISOString().split('T')[0]}.
`;
  }
  
  /**
   * Generate usage guide content
   * @private
   * @param {Object} metadata - App metadata
   * @returns {string} Usage guide content
   */
  _generateUsageGuide(metadata) {
    return `# ${metadata.name} - Usage Guide

This document provides information on how to use the ${metadata.name} application.

## Getting Started

1. Launch the application from the PrimeOS shell
2. The main interface will appear
3. Follow the on-screen instructions to use the application

## Features and Functions

${metadata.features ? metadata.features.map(f => `### ${f}\n\nDetailed instructions for this feature coming soon.\n`).join('\n') : 'Feature documentation coming soon.'}

## Troubleshooting

If you encounter issues:

1. Restart the application
2. Check for updates
3. Contact the developer

## Updates

This application can be updated through the PrimeOS App Store or directly from the source repository.
`;
  }
  
  /**
   * Generate API documentation
   * @private
   * @param {Array} files - App files
   * @param {Object} metadata - App metadata
   * @returns {Promise<string>} API documentation content
   */
  async _generateApiDocs(files, metadata) {
    try {
      // Find JS files that might have APIs
      const jsFiles = files.filter(file => 
        file.path.endsWith('.js') && 
        !this._isTestFile(file.path) &&
        !file.path.includes('node_modules')
      );
      
      if (jsFiles.length === 0) {
        return null;
      }
      
      // This would use a more sophisticated API doc generator in a real implementation
      // For the reference implementation, we'll just create a basic template
      
      return `# ${metadata.name} API Documentation

This document describes the APIs provided by the ${metadata.name} application.

## Modules

${jsFiles.map(file => {
  const moduleName = file.path.split('/').pop().replace('.js', '');
  return `### ${moduleName}\n\nFile: \`${file.path}\`\n\nAPI documentation coming soon.\n`;
}).join('\n')}

## Integration

To integrate with this application, import it into your PrimeOS environment and use the provided APIs.

## Version

This documentation is for version ${metadata.version || '1.0.0'}.
`;
    } catch (error) {
      console.error('Failed to generate API docs:', error);
      return null;
    }
  }
  
  /**
   * Check if a file is a test file
   * @private
   * @param {string} filePath - File path
   * @returns {boolean} Whether the file is a test file
   */
  _isTestFile(filePath) {
    return (
      filePath.includes('/__tests__/') ||
      filePath.includes('/tests/') ||
      filePath.endsWith('.test.js') ||
      filePath.endsWith('.spec.js')
    );
  }
  
  /**
   * Send event notification
   * @private
   * @param {string} event - Event name
   * @param {Object} data - Event data
   */
  _notifyEvent(event, data = {}) {
    if (this.eventBus) {
      this.eventBus.publish(`app-publisher:${event}`, {
        timestamp: new Date().toISOString(),
        ...data
      });
    }
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { AppPublisher };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.AppPublisher = AppPublisher;
}