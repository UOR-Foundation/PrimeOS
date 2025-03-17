/**
 * PrimeOS Bundle UI
 * 
 * Provides UI components for the PrimeOS bundling system, including:
 * - App catalog view
 * - Bundle import/export dialogs
 * - Installation management
 */

/**
 * BundleCatalogUI - Creates and manages the bundle catalog interface
 */
class BundleCatalogUI {
  /**
   * Create a new bundle catalog UI
   * @param {Object} options - Configuration options
   * @param {BundleAPI} options.bundleAPI - BundleAPI instance
   * @param {HTMLElement} options.container - Container element
   * @param {Object} options.eventBus - Event bus for notifications
   */
  constructor(options) {
    // Validate required parameters
    if (!options.bundleAPI) {
      throw new Error('BundleCatalogUI requires a bundleAPI instance');
    }
    
    if (!options.container || !(options.container instanceof HTMLElement)) {
      throw new Error('BundleCatalogUI requires a valid container element');
    }
    
    if (!options.eventBus) {
      throw new Error('BundleCatalogUI requires an eventBus instance');
    }
    
    // Store dependencies
    this.bundleAPI = options.bundleAPI;
    this.container = options.container;
    this.eventBus = options.eventBus;
    
    // Initialize state
    this.state = {
      view: 'catalog', // 'catalog', 'installed', 'detail'
      loading: false,
      bundles: [],
      installedBundles: [],
      selectedBundle: null,
      filter: {
        query: '',
        tags: []
      },
      remotes: []
    };
    
    // Bind methods
    this.render = this.render.bind(this);
    this.loadBundles = this.loadBundles.bind(this);
    this.handleAction = this.handleAction.bind(this);
    this._handleBundleEvents = this._handleBundleEvents.bind(this);
    
    // Subscribe to bundle events
    this.eventBus.subscribe('bundle:imported', this._handleBundleEvents);
    this.eventBus.subscribe('bundle:uninstalled', this._handleBundleEvents);
    
    // Initialize UI
    this._createUI();
    this.loadBundles();
    
    console.log('BundleCatalogUI initialized');
  }
  
  /**
   * Create the initial UI structure
   * @private
   */
  _createUI() {
    // Clear container
    this.container.innerHTML = '';
    
    // Create header
    const header = document.createElement('div');
    header.className = 'bundle-catalog-header';
    
    const title = document.createElement('h2');
    title.textContent = 'PrimeOS App Catalog';
    header.appendChild(title);
    
    // Create toolbar
    const toolbar = document.createElement('div');
    toolbar.className = 'bundle-catalog-toolbar';
    
    // View selector
    const viewSelector = document.createElement('div');
    viewSelector.className = 'view-selector';
    
    const catalogBtn = document.createElement('button');
    catalogBtn.textContent = 'Browse';
    catalogBtn.onclick = () => this.setView('catalog');
    
    const installedBtn = document.createElement('button');
    installedBtn.textContent = 'Installed';
    installedBtn.onclick = () => this.setView('installed');
    
    viewSelector.appendChild(catalogBtn);
    viewSelector.appendChild(installedBtn);
    toolbar.appendChild(viewSelector);
    
    // Search input
    const searchBox = document.createElement('div');
    searchBox.className = 'search-box';
    
    const searchInput = document.createElement('input');
    searchInput.type = 'text';
    searchInput.placeholder = 'Search apps...';
    searchInput.oninput = (e) => this.setFilter({ query: e.target.value });
    
    searchBox.appendChild(searchInput);
    toolbar.appendChild(searchBox);
    
    // Import/Export buttons
    const actionsBox = document.createElement('div');
    actionsBox.className = 'actions-box';
    
    const importBtn = document.createElement('button');
    importBtn.textContent = 'Import';
    importBtn.onclick = () => this.showImportDialog();
    
    actionsBox.appendChild(importBtn);
    toolbar.appendChild(actionsBox);
    
    // Add toolbar to header
    header.appendChild(toolbar);
    this.container.appendChild(header);
    
    // Create content area
    const content = document.createElement('div');
    content.className = 'bundle-catalog-content';
    this.contentContainer = content;
    this.container.appendChild(content);
    
    // Create loading indicator
    const loadingIndicator = document.createElement('div');
    loadingIndicator.className = 'loading-indicator';
    loadingIndicator.textContent = 'Loading...';
    loadingIndicator.style.display = 'none';
    this.loadingIndicator = loadingIndicator;
    this.container.appendChild(loadingIndicator);
    
    // Add styles
    this._addStyles();
  }
  
  /**
   * Add required CSS styles
   * @private
   */
  _addStyles() {
    // Check if styles already exist
    if (document.getElementById('bundle-catalog-styles')) {
      return;
    }
    
    const styles = document.createElement('style');
    styles.id = 'bundle-catalog-styles';
    styles.textContent = `
      .bundle-catalog-header {
        padding: 1rem;
        border-bottom: 1px solid #eee;
      }
      
      .bundle-catalog-toolbar {
        display: flex;
        justify-content: space-between;
        margin-top: 1rem;
      }
      
      .view-selector button {
        margin-right: 0.5rem;
        padding: 0.5rem 1rem;
        border: 1px solid #ddd;
        background: #f5f5f5;
        cursor: pointer;
      }
      
      .view-selector button.active {
        background: #e0e0e0;
        font-weight: bold;
      }
      
      .search-box input {
        padding: 0.5rem;
        width: 250px;
        border: 1px solid #ddd;
      }
      
      .actions-box button {
        padding: 0.5rem 1rem;
        margin-left: 0.5rem;
        background: #4a90e2;
        color: white;
        border: none;
        cursor: pointer;
      }
      
      .bundle-catalog-content {
        padding: 1rem;
        display: grid;
        grid-template-columns: repeat(auto-fill, minmax(250px, 1fr));
        grid-gap: 1rem;
      }
      
      .bundle-card {
        border: 1px solid #eee;
        border-radius: 4px;
        padding: 1rem;
        cursor: pointer;
        transition: box-shadow 0.2s;
      }
      
      .bundle-card:hover {
        box-shadow: 0 2px 5px rgba(0,0,0,0.1);
      }
      
      .bundle-card h3 {
        margin-top: 0;
      }
      
      .bundle-card-footer {
        display: flex;
        justify-content: space-between;
        margin-top: 1rem;
      }
      
      .bundle-card-tags {
        display: flex;
        flex-wrap: wrap;
        margin-top: 0.5rem;
      }
      
      .bundle-card-tag {
        background: #f0f0f0;
        padding: 0.2rem 0.5rem;
        border-radius: 2px;
        font-size: 0.8rem;
        margin-right: 0.5rem;
        margin-bottom: 0.5rem;
      }
      
      .bundle-detail {
        padding: 1rem;
      }
      
      .bundle-detail-header {
        display: flex;
        justify-content: space-between;
        align-items: center;
      }
      
      .bundle-detail-content {
        margin-top: 1rem;
      }
      
      .bundle-detail-section {
        margin-bottom: 1.5rem;
      }
      
      .bundle-detail-buttons {
        display: flex;
        margin-top: 1rem;
      }
      
      .bundle-detail-buttons button {
        margin-right: 0.5rem;
      }
      
      .loading-indicator {
        position: absolute;
        top: 50%;
        left: 50%;
        transform: translate(-50%, -50%);
        background: rgba(255,255,255,0.9);
        padding: 1rem;
        border-radius: 4px;
        box-shadow: 0 2px 10px rgba(0,0,0,0.1);
      }
    `;
    
    document.head.appendChild(styles);
  }
  
  /**
   * Handle bundle-related events
   * @private
   * @param {Object} eventData - Event data
   */
  _handleBundleEvents(eventData) {
    // Reload bundles on relevant events
    this.loadBundles();
  }
  
  /**
   * Set the current view
   * @param {string} view - View name ('catalog', 'installed', 'detail')
   * @param {Object} data - Additional view data
   */
  setView(view, data = {}) {
    this.state.view = view;
    
    if (view === 'detail' && data.bundle) {
      this.state.selectedBundle = data.bundle;
    }
    
    this.render();
  }
  
  /**
   * Set the current filter
   * @param {Object} filter - Filter criteria
   */
  setFilter(filter) {
    this.state.filter = { ...this.state.filter, ...filter };
    this.render();
  }
  
  /**
   * Load available and installed bundles
   */
  async loadBundles() {
    try {
      this.state.loading = true;
      this.loadingIndicator.style.display = 'block';
      this.render();
      
      // Load available bundles
      const availableBundles = await this.bundleAPI.getAvailableBundles();
      this.state.bundles = availableBundles;
      
      // Load installed bundles
      const installedBundles = await this.bundleAPI.getLocallyInstalledBundles();
      this.state.installedBundles = installedBundles;
      
      // Mark installed bundles in the available list
      this.state.bundles = this.state.bundles.map(bundle => {
        const isInstalled = this.state.installedBundles.some(installed => installed.id === bundle.id);
        return { ...bundle, installed: isInstalled };
      });
    } catch (error) {
      console.error('Failed to load bundles:', error);
    } finally {
      this.state.loading = false;
      this.loadingIndicator.style.display = 'none';
      this.render();
    }
  }
  
  /**
   * Render the current view
   */
  render() {
    if (!this.contentContainer) return;
    
    // Clear content
    this.contentContainer.innerHTML = '';
    
    // Render based on current view
    switch (this.state.view) {
      case 'catalog':
        this._renderCatalogView();
        break;
      case 'installed':
        this._renderInstalledView();
        break;
      case 'detail':
        this._renderDetailView();
        break;
      default:
        this._renderCatalogView();
    }
    
    // Update active button in view selector
    const buttons = this.container.querySelectorAll('.view-selector button');
    buttons.forEach(button => {
      button.classList.remove('active');
      if ((button.textContent === 'Browse' && this.state.view === 'catalog') ||
          (button.textContent === 'Installed' && this.state.view === 'installed')) {
        button.classList.add('active');
      }
    });
  }
  
  /**
   * Render the catalog view
   * @private
   */
  _renderCatalogView() {
    const { bundles, filter } = this.state;
    
    // Filter bundles
    const filteredBundles = bundles.filter(bundle => {
      if (filter.query) {
        const query = filter.query.toLowerCase();
        if (!bundle.name.toLowerCase().includes(query) && 
            !bundle.description.toLowerCase().includes(query)) {
          return false;
        }
      }
      
      if (filter.tags && filter.tags.length > 0) {
        if (!bundle.tags || !bundle.tags.some(tag => filter.tags.includes(tag))) {
          return false;
        }
      }
      
      return true;
    });
    
    // Render bundle cards
    if (filteredBundles.length === 0) {
      const emptyMessage = document.createElement('div');
      emptyMessage.className = 'empty-message';
      emptyMessage.textContent = 'No bundles found. Try a different search or connect to more remote repositories.';
      emptyMessage.style.gridColumn = '1 / -1';
      emptyMessage.style.textAlign = 'center';
      emptyMessage.style.padding = '2rem';
      this.contentContainer.appendChild(emptyMessage);
      return;
    }
    
    filteredBundles.forEach(bundle => {
      const card = this._createBundleCard(bundle);
      this.contentContainer.appendChild(card);
    });
  }
  
  /**
   * Render the installed bundles view
   * @private
   */
  _renderInstalledView() {
    const { installedBundles, filter } = this.state;
    
    // Filter bundles
    const filteredBundles = installedBundles.filter(bundle => {
      if (filter.query) {
        const query = filter.query.toLowerCase();
        if (!bundle.name.toLowerCase().includes(query) && 
            !bundle.description.toLowerCase().includes(query)) {
          return false;
        }
      }
      
      return true;
    });
    
    // Render bundle cards
    if (filteredBundles.length === 0) {
      const emptyMessage = document.createElement('div');
      emptyMessage.className = 'empty-message';
      emptyMessage.textContent = 'No bundles installed. Browse the catalog to find and install bundles.';
      emptyMessage.style.gridColumn = '1 / -1';
      emptyMessage.style.textAlign = 'center';
      emptyMessage.style.padding = '2rem';
      this.contentContainer.appendChild(emptyMessage);
      return;
    }
    
    filteredBundles.forEach(bundle => {
      const card = this._createBundleCard(bundle, true);
      this.contentContainer.appendChild(card);
    });
  }
  
  /**
   * Render the bundle detail view
   * @private
   */
  _renderDetailView() {
    const { selectedBundle } = this.state;
    
    if (!selectedBundle) {
      this.setView('catalog');
      return;
    }
    
    // Create detail container
    const detailContainer = document.createElement('div');
    detailContainer.className = 'bundle-detail';
    detailContainer.style.gridColumn = '1 / -1';
    
    // Create header
    const header = document.createElement('div');
    header.className = 'bundle-detail-header';
    
    const backButton = document.createElement('button');
    backButton.textContent = '← Back';
    backButton.onclick = () => this.setView(selectedBundle.installed ? 'installed' : 'catalog');
    
    const title = document.createElement('h2');
    title.textContent = selectedBundle.name;
    
    header.appendChild(backButton);
    header.appendChild(title);
    detailContainer.appendChild(header);
    
    // Create content
    const content = document.createElement('div');
    content.className = 'bundle-detail-content';
    
    // Description section
    const descSection = document.createElement('div');
    descSection.className = 'bundle-detail-section';
    
    const descTitle = document.createElement('h3');
    descTitle.textContent = 'Description';
    
    const desc = document.createElement('p');
    desc.textContent = selectedBundle.description || 'No description available.';
    
    descSection.appendChild(descTitle);
    descSection.appendChild(desc);
    content.appendChild(descSection);
    
    // Details section
    const detailsSection = document.createElement('div');
    detailsSection.className = 'bundle-detail-section';
    
    const detailsTitle = document.createElement('h3');
    detailsTitle.textContent = 'Details';
    
    const detailsList = document.createElement('dl');
    detailsList.style.display = 'grid';
    detailsList.style.gridTemplateColumns = 'auto 1fr';
    detailsList.style.gap = '0.5rem';
    
    const details = [
      { label: 'Version', value: selectedBundle.version },
      { label: 'Author', value: selectedBundle.author || 'Unknown' },
      { label: 'ID', value: selectedBundle.id },
      { label: 'License', value: selectedBundle.license || 'Unspecified' }
    ];
    
    details.forEach(detail => {
      const dt = document.createElement('dt');
      dt.textContent = detail.label + ':';
      dt.style.fontWeight = 'bold';
      
      const dd = document.createElement('dd');
      dd.textContent = detail.value;
      dd.style.margin = '0';
      
      detailsList.appendChild(dt);
      detailsList.appendChild(dd);
    });
    
    detailsSection.appendChild(detailsTitle);
    detailsSection.appendChild(detailsList);
    content.appendChild(detailsSection);
    
    // Tags section if available
    if (selectedBundle.tags && selectedBundle.tags.length > 0) {
      const tagsSection = document.createElement('div');
      tagsSection.className = 'bundle-detail-section';
      
      const tagsTitle = document.createElement('h3');
      tagsTitle.textContent = 'Tags';
      
      const tagsList = document.createElement('div');
      tagsList.className = 'bundle-card-tags';
      
      selectedBundle.tags.forEach(tag => {
        const tagEl = document.createElement('span');
        tagEl.className = 'bundle-card-tag';
        tagEl.textContent = tag;
        tagsList.appendChild(tagEl);
      });
      
      tagsSection.appendChild(tagsTitle);
      tagsSection.appendChild(tagsList);
      content.appendChild(tagsSection);
    }
    
    // Permissions section if available
    if (selectedBundle.permissions && selectedBundle.permissions.length > 0) {
      const permSection = document.createElement('div');
      permSection.className = 'bundle-detail-section';
      
      const permTitle = document.createElement('h3');
      permTitle.textContent = 'Permissions';
      
      const permList = document.createElement('ul');
      
      selectedBundle.permissions.forEach(perm => {
        const permItem = document.createElement('li');
        permItem.textContent = perm;
        permList.appendChild(permItem);
      });
      
      permSection.appendChild(permTitle);
      permSection.appendChild(permList);
      content.appendChild(permSection);
    }
    
    // Action buttons
    const buttonsContainer = document.createElement('div');
    buttonsContainer.className = 'bundle-detail-buttons';
    
    if (selectedBundle.installed) {
      // Uninstall button
      const uninstallBtn = document.createElement('button');
      uninstallBtn.textContent = 'Uninstall';
      uninstallBtn.onclick = () => this.handleAction('uninstall', selectedBundle);
      
      // Export button
      const exportBtn = document.createElement('button');
      exportBtn.textContent = 'Export';
      exportBtn.onclick = () => this.handleAction('export', selectedBundle);
      
      buttonsContainer.appendChild(uninstallBtn);
      buttonsContainer.appendChild(exportBtn);
    } else {
      // Install button
      const installBtn = document.createElement('button');
      installBtn.textContent = 'Install';
      installBtn.onclick = () => this.handleAction('install', selectedBundle);
      
      buttonsContainer.appendChild(installBtn);
    }
    
    content.appendChild(buttonsContainer);
    detailContainer.appendChild(content);
    
    this.contentContainer.appendChild(detailContainer);
  }
  
  /**
   * Create a bundle card element
   * @private
   * @param {Object} bundle - Bundle data
   * @param {boolean} installed - Whether this is an installed bundle
   * @returns {HTMLElement} Card element
   */
  _createBundleCard(bundle, installed = false) {
    const card = document.createElement('div');
    card.className = 'bundle-card';
    
    // Card header
    const name = document.createElement('h3');
    name.textContent = bundle.name;
    card.appendChild(name);
    
    // Version
    const version = document.createElement('div');
    version.textContent = `Version: ${bundle.version}`;
    version.style.color = '#666';
    version.style.fontSize = '0.9rem';
    card.appendChild(version);
    
    // Description
    const desc = document.createElement('p');
    desc.textContent = bundle.description || 'No description available.';
    desc.style.marginTop = '0.5rem';
    desc.style.height = '3em';
    desc.style.overflow = 'hidden';
    desc.style.textOverflow = 'ellipsis';
    card.appendChild(desc);
    
    // Tags
    if (bundle.tags && bundle.tags.length > 0) {
      const tagsContainer = document.createElement('div');
      tagsContainer.className = 'bundle-card-tags';
      
      bundle.tags.slice(0, 3).forEach(tag => {
        const tagEl = document.createElement('span');
        tagEl.className = 'bundle-card-tag';
        tagEl.textContent = tag;
        tagsContainer.appendChild(tagEl);
      });
      
      card.appendChild(tagsContainer);
    }
    
    // Card footer
    const footer = document.createElement('div');
    footer.className = 'bundle-card-footer';
    
    // Author
    const author = document.createElement('span');
    author.textContent = bundle.author || 'Unknown';
    author.style.fontSize = '0.9rem';
    footer.appendChild(author);
    
    // Status/action
    const status = document.createElement('span');
    if (bundle.installed) {
      status.textContent = 'Installed';
      status.style.color = 'green';
    }
    footer.appendChild(status);
    
    card.appendChild(footer);
    
    // Add click handler to show details
    card.onclick = () => this.setView('detail', { bundle });
    
    return card;
  }
  
  /**
   * Handle a UI action
   * @param {string} action - Action name
   * @param {Object} bundle - Bundle data
   */
  async handleAction(action, bundle) {
    if (!bundle) return;
    
    switch (action) {
      case 'install':
        await this.installBundle(bundle);
        break;
      case 'uninstall':
        await this.uninstallBundle(bundle);
        break;
      case 'export':
        await this.exportBundle(bundle);
        break;
    }
  }
  
  /**
   * Install a bundle
   * @param {Object} bundle - Bundle to install
   */
  async installBundle(bundle) {
    try {
      this.state.loading = true;
      this.loadingIndicator.style.display = 'block';
      this.loadingIndicator.textContent = `Installing ${bundle.name}...`;
      
      const result = await this.bundleAPI.installBundle(bundle.id, bundle.remoteUrl);
      
      if (result.success) {
        this.showNotification(`Successfully installed ${bundle.name}`);
        await this.loadBundles();
        this.setView('installed');
      } else {
        this.showNotification(`Failed to install: ${result.error}`, 'error');
      }
    } catch (error) {
      console.error(`Failed to install bundle ${bundle.id}:`, error);
      this.showNotification(`Installation error: ${error.message}`, 'error');
    } finally {
      this.state.loading = false;
      this.loadingIndicator.style.display = 'none';
    }
  }
  
  /**
   * Uninstall a bundle
   * @param {Object} bundle - Bundle to uninstall
   */
  async uninstallBundle(bundle) {
    if (!confirm(`Are you sure you want to uninstall ${bundle.name}?`)) {
      return;
    }
    
    try {
      this.state.loading = true;
      this.loadingIndicator.style.display = 'block';
      this.loadingIndicator.textContent = `Uninstalling ${bundle.name}...`;
      
      const result = await this.bundleAPI.uninstallBundle(bundle.id);
      
      if (result.success) {
        this.showNotification(`Successfully uninstalled ${bundle.name}`);
        await this.loadBundles();
        this.setView('installed');
      } else {
        this.showNotification(`Failed to uninstall: ${result.error}`, 'error');
      }
    } catch (error) {
      console.error(`Failed to uninstall bundle ${bundle.id}:`, error);
      this.showNotification(`Uninstallation error: ${error.message}`, 'error');
    } finally {
      this.state.loading = false;
      this.loadingIndicator.style.display = 'none';
    }
  }
  
  /**
   * Export a bundle
   * @param {Object} bundle - Bundle to export
   */
  async exportBundle(bundle) {
    try {
      this.state.loading = true;
      this.loadingIndicator.style.display = 'block';
      this.loadingIndicator.textContent = `Exporting ${bundle.name}...`;
      
      const result = await this.bundleAPI.exportBundle(bundle.id);
      
      if (result.success) {
        this.bundleAPI.saveBundleToFile(result.bundle, `${bundle.id}.bundle.json`);
        this.showNotification(`Successfully exported ${bundle.name}`);
      } else {
        this.showNotification(`Failed to export: ${result.error}`, 'error');
      }
    } catch (error) {
      console.error(`Failed to export bundle ${bundle.id}:`, error);
      this.showNotification(`Export error: ${error.message}`, 'error');
    } finally {
      this.state.loading = false;
      this.loadingIndicator.style.display = 'none';
    }
  }
  
  /**
   * Show the import bundle dialog
   */
  showImportDialog() {
    // Create modal container
    const modal = document.createElement('div');
    modal.className = 'import-modal';
    modal.style.position = 'fixed';
    modal.style.top = '0';
    modal.style.left = '0';
    modal.style.width = '100%';
    modal.style.height = '100%';
    modal.style.backgroundColor = 'rgba(0, 0, 0, 0.5)';
    modal.style.display = 'flex';
    modal.style.justifyContent = 'center';
    modal.style.alignItems = 'center';
    modal.style.zIndex = '1000';
    
    // Create modal content
    const content = document.createElement('div');
    content.className = 'import-modal-content';
    content.style.backgroundColor = 'white';
    content.style.padding = '2rem';
    content.style.borderRadius = '4px';
    content.style.maxWidth = '500px';
    content.style.width = '100%';
    
    // Create header
    const header = document.createElement('div');
    header.className = 'import-modal-header';
    
    const title = document.createElement('h3');
    title.textContent = 'Import Bundle';
    title.style.marginTop = '0';
    
    const closeBtn = document.createElement('button');
    closeBtn.textContent = '×';
    closeBtn.style.position = 'absolute';
    closeBtn.style.top = '1rem';
    closeBtn.style.right = '1rem';
    closeBtn.style.border = 'none';
    closeBtn.style.background = 'none';
    closeBtn.style.fontSize = '1.5rem';
    closeBtn.style.cursor = 'pointer';
    closeBtn.onclick = () => document.body.removeChild(modal);
    
    header.appendChild(title);
    header.appendChild(closeBtn);
    content.appendChild(header);
    
    // Create import form
    const form = document.createElement('div');
    form.className = 'import-form';
    
    // File upload
    const fileSection = document.createElement('div');
    fileSection.className = 'import-section';
    fileSection.style.marginBottom = '1.5rem';
    
    const fileLabel = document.createElement('p');
    fileLabel.textContent = 'Import from file:';
    
    const fileInput = document.createElement('input');
    fileInput.type = 'file';
    fileInput.accept = '.json';
    
    fileSection.appendChild(fileLabel);
    fileSection.appendChild(fileInput);
    form.appendChild(fileSection);
    
    // Remote URL
    const urlSection = document.createElement('div');
    urlSection.className = 'import-section';
    
    const urlLabel = document.createElement('p');
    urlLabel.textContent = 'Import from URL:';
    
    const urlInput = document.createElement('input');
    urlInput.type = 'text';
    urlInput.placeholder = 'https://example.com/bundle.json';
    urlInput.style.width = '100%';
    urlInput.style.padding = '0.5rem';
    urlInput.style.marginBottom = '1rem';
    
    urlSection.appendChild(urlLabel);
    urlSection.appendChild(urlInput);
    form.appendChild(urlSection);
    
    // Buttons
    const buttons = document.createElement('div');
    buttons.className = 'import-buttons';
    buttons.style.display = 'flex';
    buttons.style.justifyContent = 'flex-end';
    buttons.style.marginTop = '1.5rem';
    
    const cancelBtn = document.createElement('button');
    cancelBtn.textContent = 'Cancel';
    cancelBtn.style.marginRight = '0.5rem';
    cancelBtn.onclick = () => document.body.removeChild(modal);
    
    const importBtn = document.createElement('button');
    importBtn.textContent = 'Import';
    importBtn.style.backgroundColor = '#4a90e2';
    importBtn.style.color = 'white';
    importBtn.style.border = 'none';
    importBtn.style.padding = '0.5rem 1rem';
    importBtn.style.cursor = 'pointer';
    importBtn.onclick = async () => {
      try {
        if (fileInput.files && fileInput.files[0]) {
          // Import from file
          this.state.loading = true;
          this.loadingIndicator.style.display = 'block';
          this.loadingIndicator.textContent = 'Importing bundle...';
          
          const result = await this.bundleAPI.importBundleFromFile(fileInput.files[0]);
          
          if (result.success) {
            this.showNotification(`Successfully imported bundle: ${result.bundleId}`);
            await this.loadBundles();
            document.body.removeChild(modal);
          } else {
            this.showNotification(`Import failed: ${result.error}`, 'error');
          }
        } else if (urlInput.value) {
          // Import from URL
          this.showNotification(`URL import not implemented yet`, 'warning');
        } else {
          this.showNotification('Please select a file or enter a URL', 'warning');
        }
      } catch (error) {
        console.error('Import failed:', error);
        this.showNotification(`Import error: ${error.message}`, 'error');
      } finally {
        this.state.loading = false;
        this.loadingIndicator.style.display = 'none';
      }
    };
    
    buttons.appendChild(cancelBtn);
    buttons.appendChild(importBtn);
    form.appendChild(buttons);
    
    content.appendChild(form);
    modal.appendChild(content);
    
    // Add to document
    document.body.appendChild(modal);
  }
  
  /**
   * Show a notification
   * @param {string} message - Notification message
   * @param {string} type - Notification type (info, success, error, warning)
   */
  showNotification(message, type = 'info') {
    this.eventBus.publish('shell:show-notification', {
      appId: 'bundle-catalog',
      title: type.charAt(0).toUpperCase() + type.slice(1),
      message,
      type,
      timeout: 5000
    });
  }
  
  /**
   * Clean up resources when UI is no longer needed
   */
  dispose() {
    // Unsubscribe from events
    this.eventBus.unsubscribe('bundle:imported', this._handleBundleEvents);
    this.eventBus.unsubscribe('bundle:uninstalled', this._handleBundleEvents);
    
    // Remove UI
    this.container.innerHTML = '';
    
    console.log('BundleCatalogUI disposed');
  }
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { BundleCatalogUI };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.BundleCatalogUI = BundleCatalogUI;
}