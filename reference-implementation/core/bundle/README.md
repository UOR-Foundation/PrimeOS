# PrimeOS App Bundle

A package for creating portable PrimeOS application bundles that can be shared, imported, and exported across different PrimeOS instances via decentralized networks and federated indexes.

## Overview

PrimeOS App Bundles provide a standardized format for packaging, distributing, and installing PrimeOS applications. The system enables:

1. **Dynamic bundling** - Create shareable app packages directly within PrimeOS
2. **Portability** - Export applications as self-contained bundles
3. **Decentralized distribution** - Share apps via decentralized remotes or federated indexes
4. **Verification** - Validate app signatures and integrity
5. **Installation** - Import apps from local files or remote sources

## Bundle Format

A PrimeOS App Bundle is a JSON-based package with the following structure:

```json
{
  "manifest": {
    "id": "com.example.app-name",
    "name": "App Name",
    "version": "1.0.0",
    "author": "Developer Name",
    "description": "App description",
    "license": "License name",
    "homepage": "https://example.com/app",
    "entryPoint": "index.js",
    "icon": "data:image/png;base64,...", // Base64-encoded icon
    "tags": ["category1", "category2"],
    "permissions": ["storage", "identity"],
    "dependencies": {
      "otherAppId": ">=1.0.0"
    },
    "compatibilityVersion": "1.0.0",
    "created": "2025-03-17T12:00:00.000Z",
    "signature": "..." // Digital signature for verification
  },
  "code": {
    "index.js": "...", // Base64-encoded source files
    "styles.css": "...",
    "components/component1.js": "..."
  },
  "resources": {
    "icons/icon.png": "...", // Base64-encoded resources 
    "translations/en.json": "..."
  }
}
```

## Core Components

### 1. BundleManager

The main service responsible for creating, importing, exporting, and managing app bundles.

Key methods:
- `createBundle(appId)` - Bundle an installed app for distribution
- `importBundle(bundleData, options)` - Import an app bundle (from file or URL)
- `exportBundle(appId, format)` - Export an app bundle (default: JSON)
- `validateBundle(bundleData)` - Check bundle integrity and validity
- `installBundle(bundleData)` - Install a validated bundle

### 2. BundleStore

Extends PrimeStore to manage bundle metadata and provide queries for the app catalog.

Key methods:
- `registerBundle(bundleManifest)` - Add bundle to local catalog
- `unregisterBundle(bundleId)` - Remove bundle from local catalog
- `getBundleMetadata(bundleId)` - Get specific bundle info
- `queryBundles(filter)` - Search for bundles matching criteria

### 3. BundleAPI

API extension for PrimeOS AppAPI to provide bundle-related functionality to applications.

Key methods:
- `getAvailableBundles(filter)` - Get installable bundles from catalog
- `installBundle(bundleId)` - Install a bundle from catalog
- `uninstallBundle(bundleId)` - Remove installed bundle
- `getLocallyInstalledBundles()` - List installed bundles

### 4. RemoteProvider

Interface for connecting to bundle repositories and federated app indexes.

Key methods:
- `connectToRemote(remoteUrl, options)` - Connect to a remote bundle source
- `fetchBundleCatalog(remote)` - Get available bundles from remote
- `fetchBundle(bundleId, remote)` - Download specific bundle from remote
- `publishBundle(bundleData, remote)` - Publish bundle to remote (if supported)

## Implementation Plan

1. **Phase 1: Core Bundle Format & Local Management**
   - Define bundle format specification
   - Implement BundleManager core functionality
   - Add BundleStore implementation
   - Create basic bundle API
   - Add local import/export capabilities

2. **Phase 2: Remote Connectivity**
   - Implement RemoteProvider interface
   - Add support for the official PrimeOS Apps repository
   - Create generic remote connection handlers
   - Implement bundle catalog synchronization

3. **Phase 3: Security & Verification**
   - Implement signature verification
   - Add permission validation
   - Create compatibility checking
   - Implement sandboxing for untrusted bundles

4. **Phase 4: UI Integration**
   - Create bundle catalog UI
   - Add import/export dialogs
   - Implement installation/update flow
   - Build bundle creation wizard

## Security Considerations

1. **Bundle Signatures**
   - All bundles should be digitally signed 
   - Verification against developer's public key
   - Option to trust developer/source

2. **Permissions Model**
   - Explicit user consent for requested permissions
   - Isolated storage for each bundle
   - Capability-based security model

3. **Sandbox Environment**
   - Execution in restricted context
   - Controlled access to system resources
   - Monitoring for unexpected behavior

## Integration Points

1. **Shell Integration**
   - App catalog accessible from shell UI
   - Installation status indicators
   - Bundle management interface

2. **Storage Integration**
   - Dedicated store for bundle metadata
   - Version tracking and updates
   - Bundle resources management

3. **Identity Integration**
   - Developer identity verification
   - User-specific bundle preferences
   - Installation authorization

## Getting Started with the App Bundle Framework

### For App Developers

```javascript
// Create a bundleable app
const myApp = {
  id: 'com.example.myapp',
  name: 'My App',
  version: '1.0.0',
  // App implementation...
};

// Register app for bundling
PrimeOS.BundleAPI.registerApp(myApp, {
  permissions: ['storage'],
  tags: ['utility']
});

// Export the app bundle
const bundleData = await PrimeOS.BundleAPI.createBundle(myApp.id);
// Share or save the bundle
```

### For PrimeOS Users

```javascript
// Import an app from file
const fileInput = document.getElementById('bundleFileInput');
fileInput.addEventListener('change', async (event) => {
  const file = event.target.files[0];
  const bundleData = await readFileAsJSON(file);
  await PrimeOS.BundleAPI.importBundle(bundleData);
});

// Install app from remote
const appCatalog = await PrimeOS.BundleAPI.getAvailableBundles();
await PrimeOS.BundleAPI.installBundle(appCatalog[0].id);
```

## Reference Resources

- [GitHub Repository](https://github.com/UOR-Foundation/PrimeOS-Apps) - The official PrimeOS App repository
- [Bundle Format Specification](https://example.com/primeos/bundle-spec) - Detailed format specification
- [Developer Portal](https://example.com/primeos/developers) - Resources for bundle developers

## Future Enhancements

1. **Bundle Federation**
   - P2P bundle sharing protocol
   - Distributed bundle indexes
   - Reputation system for bundles

2. **Advanced Features**
   - Delta updates for efficient updates
   - Dependency resolution
   - Bundle versioning and rollback
   - Bundle hooks for system integration

3. **Developer Tools**
   - Bundle creation wizard
   - Bundle testing framework
   - Verification tools