/**
 * PrimeOS App Factory UI
 * 
 * User interface component for the App Factory system that guides users
 * through the process of creating and modifying PrimeOS applications.
 */

class AppFactoryUI {
  /**
   * Creates a new App Factory UI instance
   * @param {Object} options - Configuration options
   * @param {HTMLElement} options.container - DOM container for the UI
   * @param {Object} options.manager - AppFactoryManager instance
   * @param {Object} options.eventBus - Event bus for notifications
   */
  constructor(options) {
    // Validate required dependencies
    if (!options.container) {
      throw new Error('AppFactoryUI requires a container element');
    }
    
    if (!options.manager) {
      throw new Error('AppFactoryUI requires an AppFactoryManager instance');
    }
    
    // Store dependencies
    this.container = options.container;
    this.manager = options.manager;
    this.eventBus = options.eventBus || null;
    
    // Initialize UI state
    this.state = {
      currentStep: 'welcome',
      projectId: null,
      projectData: null,
      activePanel: 'workflow',
      isLoading: false,
      errors: []
    };
    
    // Bind methods
    this.render = this.render.bind(this);
    this.setStep = this.setStep.bind(this);
    this.handleError = this.handleError.bind(this);
    
    // Register event handlers
    if (this.eventBus) {
      this.eventBus.subscribe('app-factory:step-completed', this._handleStepCompleted.bind(this));
      this.eventBus.subscribe('app-factory:tests-completed', this._handleTestsCompleted.bind(this));
      this.eventBus.subscribe('app-factory:app-published', this._handleAppPublished.bind(this));
      this.eventBus.subscribe('app-factory:error', this.handleError.bind(this));
    }
    
    console.log('AppFactoryUI initialized');
  }
  
  /**
   * Render the UI in the container
   */
  render() {
    // Create UI structure
    this.container.innerHTML = `
      <div class="app-factory-ui">
        <header class="app-factory-header">
          <h1>PrimeOS App Factory</h1>
          <div class="header-actions" id="header-actions"></div>
        </header>
        
        <div class="app-factory-main">
          <nav class="app-factory-sidebar" id="app-factory-sidebar"></nav>
          
          <main class="app-factory-content" id="app-factory-content">
            <div class="loading-overlay" id="loading-overlay" style="display: none;">
              <div class="loading-spinner"></div>
              <div class="loading-message">Processing...</div>
            </div>
            
            <div class="error-container" id="error-container" style="display: none;"></div>
            
            <div class="step-container" id="step-container"></div>
          </main>
        </div>
      </div>
    `;
    
    // Populate sidebar
    this._renderSidebar();
    
    // Render initial step
    this._renderStep();
    
    // Add event listeners
    this._attachEventListeners();
  }
  
  /**
   * Set the current workflow step
   * @param {string} stepId - Step ID
   * @param {Object} data - Step data
   */
  setStep(stepId, data = {}) {
    // Update state
    this.state.currentStep = stepId;
    this.state.stepData = data;
    
    // Render step content
    this._renderStep();
    
    // Update sidebar
    this._updateSidebarActive();
    
    // Scroll to top
    const content = document.getElementById('app-factory-content');
    if (content) {
      content.scrollTop = 0;
    }
  }
  
  /**
   * Show progress indicator
   * @param {string} message - Optional progress message
   */
  showProgress(message = 'Processing...') {
    this.state.isLoading = true;
    
    const overlay = document.getElementById('loading-overlay');
    if (overlay) {
      const messageEl = overlay.querySelector('.loading-message');
      if (messageEl) {
        messageEl.textContent = message;
      }
      overlay.style.display = 'flex';
    }
  }
  
  /**
   * Hide progress indicator
   */
  hideProgress() {
    this.state.isLoading = false;
    
    const overlay = document.getElementById('loading-overlay');
    if (overlay) {
      overlay.style.display = 'none';
    }
  }
  
  /**
   * Handle error
   * @param {Error|string} error - Error object or message
   */
  handleError(error) {
    // Add to errors array
    this.state.errors.push({
      message: error.message || error,
      timestamp: new Date().toISOString()
    });
    
    // Show error container
    const errorContainer = document.getElementById('error-container');
    if (errorContainer) {
      errorContainer.innerHTML = `
        <div class="error-message">
          <button class="close-button">&times;</button>
          <h3>Error</h3>
          <p>${error.message || error}</p>
        </div>
      `;
      errorContainer.style.display = 'block';
      
      // Add close button event listener
      const closeButton = errorContainer.querySelector('.close-button');
      if (closeButton) {
        closeButton.addEventListener('click', () => {
          errorContainer.style.display = 'none';
        });
      }
    }
    
    // Hide progress indicator
    this.hideProgress();
  }
  
  /**
   * Show code preview
   * @param {Array} files - Files to preview
   */
  showCodePreview(files) {
    const previewContainer = document.getElementById('code-preview-container');
    if (!previewContainer) {
      // Create preview container if it doesn't exist
      const stepContainer = document.getElementById('step-container');
      if (stepContainer) {
        const container = document.createElement('div');
        container.id = 'code-preview-container';
        container.className = 'code-preview-container';
        container.innerHTML = `
          <div class="code-preview-header">
            <h3>Code Preview</h3>
            <button class="close-button" id="close-preview-button">&times;</button>
          </div>
          <div class="file-list" id="file-list"></div>
          <div class="file-content" id="file-content"></div>
        `;
        stepContainer.appendChild(container);
        
        // Add close button event listener
        const closeButton = document.getElementById('close-preview-button');
        if (closeButton) {
          closeButton.addEventListener('click', () => {
            container.remove();
          });
        }
      }
    }
    
    // Populate file list
    const fileList = document.getElementById('file-list');
    if (fileList) {
      fileList.innerHTML = '';
      
      files.forEach((file, index) => {
        const fileItem = document.createElement('div');
        fileItem.className = 'file-item';
        fileItem.textContent = file.path;
        fileItem.dataset.index = index;
        
        fileItem.addEventListener('click', () => {
          // Remove active class from all items
          fileList.querySelectorAll('.file-item').forEach(item => {
            item.classList.remove('active');
          });
          
          // Add active class to clicked item
          fileItem.classList.add('active');
          
          // Show file content
          const fileContent = document.getElementById('file-content');
          if (fileContent) {
            fileContent.innerHTML = `
              <div class="file-path">${file.path}</div>
              <pre><code>${this._escapeHtml(file.content)}</code></pre>
            `;
          }
        });
        
        fileList.appendChild(fileItem);
        
        // Auto-select first file
        if (index === 0) {
          fileItem.click();
        }
      });
    }
  }
  
  /**
   * Show test results
   * @param {Object} results - Test results
   */
  showTestResults(results) {
    const resultsContainer = document.getElementById('test-results-container');
    if (!resultsContainer) {
      // Create results container if it doesn't exist
      const stepContainer = document.getElementById('step-container');
      if (stepContainer) {
        const container = document.createElement('div');
        container.id = 'test-results-container';
        container.className = 'test-results-container';
        
        // Determine success/failure class
        const resultClass = results.success ? 'success' : 'failure';
        
        container.innerHTML = `
          <div class="test-results-header ${resultClass}">
            <h3>Test Results</h3>
            <div class="test-summary">
              <span class="test-passed">${results.passed} passed</span>
              <span class="test-failed">${results.failed || 0} failed</span>
              <span class="test-total">${results.total} total</span>
            </div>
            <button class="close-button" id="close-results-button">&times;</button>
          </div>
          <div class="test-details" id="test-details"></div>
        `;
        stepContainer.appendChild(container);
        
        // Add close button event listener
        const closeButton = document.getElementById('close-results-button');
        if (closeButton) {
          closeButton.addEventListener('click', () => {
            container.remove();
          });
        }
        
        // Populate test details
        const detailsContainer = document.getElementById('test-details');
        if (detailsContainer) {
          // Add lint results if available
          if (results.lintResults) {
            detailsContainer.innerHTML += `
              <div class="result-section">
                <h4>Lint Results</h4>
                <div class="lint-summary">
                  <div class="lint-stat">
                    <span class="stat-label">Passed:</span>
                    <span class="stat-value">${results.lintResults.passed}</span>
                  </div>
                  <div class="lint-stat">
                    <span class="stat-label">Errors:</span>
                    <span class="stat-value">${results.lintResults.errors || 0}</span>
                  </div>
                  <div class="lint-stat">
                    <span class="stat-label">Warnings:</span>
                    <span class="stat-value">${results.lintResults.warnings || 0}</span>
                  </div>
                </div>
              </div>
            `;
          }
          
          // Add unit test results if available
          if (results.unitTestResults) {
            let testHtml = `
              <div class="result-section">
                <h4>Unit Tests</h4>
                <div class="test-files">
            `;
            
            results.unitTestResults.testResults.forEach(fileResult => {
              testHtml += `
                <div class="test-file">
                  <div class="test-file-header">
                    <div class="test-file-path">${fileResult.testFilePath}</div>
                    <div class="test-file-summary">
                      <span class="test-passed">${fileResult.passed} passed</span>
                      <span class="test-failed">${fileResult.failed} failed</span>
                    </div>
                  </div>
                  <div class="test-cases">
              `;
              
              fileResult.testResults.forEach(testCase => {
                const testClass = testCase.status === 'passed' ? 'passed' : 'failed';
                testHtml += `
                  <div class="test-case ${testClass}">
                    <div class="test-name">${testCase.name}</div>
                    ${testCase.error ? `<div class="test-error">${testCase.error}</div>` : ''}
                  </div>
                `;
              });
              
              testHtml += `
                  </div>
                </div>
              `;
            });
            
            testHtml += `
                </div>
              </div>
            `;
            
            detailsContainer.innerHTML += testHtml;
          }
          
          // Add recommendations if available
          if (results.details && results.details.recommendations) {
            let recHtml = `
              <div class="result-section">
                <h4>Recommendations</h4>
                <ul class="recommendations">
            `;
            
            results.details.recommendations.forEach(rec => {
              recHtml += `<li class="${rec.type}">${rec.message}</li>`;
            });
            
            recHtml += `
                </ul>
              </div>
            `;
            
            detailsContainer.innerHTML += recHtml;
          }
        }
      }
    }
  }
  
  /**
   * Show results after workflow completion
   * @param {Object} projectData - Project data
   */
  showResults(projectData) {
    // Create results content
    const resultsContent = `
      <div class="results-container">
        <h2>App Created Successfully!</h2>
        
        <div class="app-summary">
          <div class="app-info">
            <div class="app-name">${projectData.name}</div>
            <div class="app-description">${projectData.description || ''}</div>
          </div>
          
          <div class="stats">
            <div class="stat-item">
              <div class="stat-value">${projectData.files ? projectData.files.length : 0}</div>
              <div class="stat-label">Files</div>
            </div>
            ${projectData.testResults ? `
              <div class="stat-item">
                <div class="stat-value">${projectData.testResults.passed}/${projectData.testResults.total}</div>
                <div class="stat-label">Tests Passed</div>
              </div>
            ` : ''}
          </div>
        </div>
        
        <div class="action-buttons">
          <button class="primary-button" id="view-code-button">View Code</button>
          <button class="secondary-button" id="export-app-button">Export App</button>
          ${projectData.publishingInfo ? `
            <button class="secondary-button" id="view-published-button">View Published</button>
          ` : ''}
        </div>
      </div>
    `;
    
    // Update step container
    const stepContainer = document.getElementById('step-container');
    if (stepContainer) {
      stepContainer.innerHTML = resultsContent;
      
      // Add event listeners for buttons
      const viewCodeButton = document.getElementById('view-code-button');
      if (viewCodeButton && projectData.files) {
        viewCodeButton.addEventListener('click', () => {
          this.showCodePreview(projectData.files);
        });
      }
      
      const exportAppButton = document.getElementById('export-app-button');
      if (exportAppButton) {
        exportAppButton.addEventListener('click', () => {
          this._handleExportApp(projectData);
        });
      }
      
      const viewPublishedButton = document.getElementById('view-published-button');
      if (viewPublishedButton && projectData.publishingInfo) {
        viewPublishedButton.addEventListener('click', () => {
          if (projectData.publishingInfo.result && projectData.publishingInfo.result.repositoryUrl) {
            window.open(projectData.publishingInfo.result.repositoryUrl, '_blank');
          }
        });
      }
    }
  }
  
  /**
   * Render sidebar navigation
   * @private
   */
  _renderSidebar() {
    const sidebar = document.getElementById('app-factory-sidebar');
    if (!sidebar) return;
    
    // Define workflow steps
    const steps = [
      { id: 'welcome', name: 'Welcome', icon: 'home' },
      { id: 'domain', name: 'Domain Definition', icon: 'compass' },
      { id: 'requirements', name: 'Requirements', icon: 'list' },
      { id: 'specification', name: 'Specification', icon: 'blueprint' },
      { id: 'generation', name: 'Code Generation', icon: 'code' },
      { id: 'testing', name: 'Testing', icon: 'vial' },
      { id: 'publishing', name: 'Publishing', icon: 'upload' },
      { id: 'results', name: 'Results', icon: 'check-circle' }
    ];
    
    // Create sidebar HTML
    let sidebarHtml = `
      <div class="sidebar-section">
        <h3>Workflow</h3>
        <ul class="sidebar-menu">
    `;
    
    steps.forEach(step => {
      const activeClass = step.id === this.state.currentStep ? 'active' : '';
      sidebarHtml += `
        <li class="sidebar-item ${activeClass}" data-step="${step.id}">
          <span class="step-icon">${step.icon}</span>
          <span class="step-name">${step.name}</span>
        </li>
      `;
    });
    
    sidebarHtml += `
        </ul>
      </div>
      
      <div class="sidebar-section">
        <h3>Projects</h3>
        <ul class="project-list" id="project-list">
          <li class="project-item new-project" id="new-project-button">
            <span class="project-icon">+</span>
            <span class="project-name">New Project</span>
          </li>
        </ul>
      </div>
    `;
    
    sidebar.innerHTML = sidebarHtml;
    
    // Add event listeners
    sidebar.querySelectorAll('.sidebar-item').forEach(item => {
      item.addEventListener('click', () => {
        const stepId = item.dataset.step;
        if (stepId) {
          this.setStep(stepId);
        }
      });
    });
    
    const newProjectButton = document.getElementById('new-project-button');
    if (newProjectButton) {
      newProjectButton.addEventListener('click', () => {
        this.setStep('welcome');
      });
    }
  }
  
  /**
   * Update active state in sidebar
   * @private
   */
  _updateSidebarActive() {
    const sidebar = document.getElementById('app-factory-sidebar');
    if (!sidebar) return;
    
    // Remove active class from all items
    sidebar.querySelectorAll('.sidebar-item').forEach(item => {
      item.classList.remove('active');
    });
    
    // Add active class to current step
    const activeItem = sidebar.querySelector(`[data-step="${this.state.currentStep}"]`);
    if (activeItem) {
      activeItem.classList.add('active');
    }
  }
  
  /**
   * Render step content
   * @private
   */
  _renderStep() {
    const stepContainer = document.getElementById('step-container');
    if (!stepContainer) return;
    
    switch (this.state.currentStep) {
      case 'welcome':
        this._renderWelcomeStep(stepContainer);
        break;
      case 'domain':
        this._renderDomainStep(stepContainer);
        break;
      case 'requirements':
        this._renderRequirementsStep(stepContainer);
        break;
      case 'specification':
        this._renderSpecificationStep(stepContainer);
        break;
      case 'generation':
        this._renderGenerationStep(stepContainer);
        break;
      case 'testing':
        this._renderTestingStep(stepContainer);
        break;
      case 'publishing':
        this._renderPublishingStep(stepContainer);
        break;
      case 'results':
        this._renderResultsStep(stepContainer);
        break;
      default:
        stepContainer.innerHTML = `<div class="error-message">Unknown step: ${this.state.currentStep}</div>`;
    }
  }
  
  /**
   * Render welcome step
   * @private
   * @param {HTMLElement} container - Step container
   */
  _renderWelcomeStep(container) {
    container.innerHTML = `
      <div class="step-content">
        <h2>Welcome to PrimeOS App Factory</h2>
        
        <p class="intro-text">
          Create PrimeOS applications with AI assistance. The App Factory guides you through the process
          of defining your app, generating code, testing, and publishing.
        </p>
        
        <div class="option-cards">
          <div class="option-card" id="new-app-card">
            <div class="card-icon">✨</div>
            <h3>Create New App</h3>
            <p>Start from scratch with a new application</p>
          </div>
          
          <div class="option-card" id="import-app-card">
            <div class="card-icon">📥</div>
            <h3>Import Existing App</h3>
            <p>Modify an existing PrimeOS application</p>
          </div>
          
          <div class="option-card" id="templates-card">
            <div class="card-icon">📋</div>
            <h3>Start from Template</h3>
            <p>Begin with a pre-built application template</p>
          </div>
        </div>
        
        <div class="new-app-form" id="new-app-form" style="display: none;">
          <h3>Create New Application</h3>
          
          <div class="form-group">
            <label for="app-name">App Name</label>
            <input type="text" id="app-name" placeholder="Enter app name">
          </div>
          
          <div class="form-group">
            <label for="app-description">Description</label>
            <textarea id="app-description" placeholder="Describe your application"></textarea>
          </div>
          
          <div class="form-actions">
            <button class="secondary-button" id="cancel-new-app">Cancel</button>
            <button class="primary-button" id="create-app-button">Create App</button>
          </div>
        </div>
      </div>
    `;
    
    // Add event listeners
    const newAppCard = document.getElementById('new-app-card');
    const newAppForm = document.getElementById('new-app-form');
    
    if (newAppCard && newAppForm) {
      newAppCard.addEventListener('click', () => {
        // Hide cards, show form
        document.querySelector('.option-cards').style.display = 'none';
        newAppForm.style.display = 'block';
      });
    }
    
    const cancelButton = document.getElementById('cancel-new-app');
    if (cancelButton) {
      cancelButton.addEventListener('click', () => {
        // Show cards, hide form
        document.querySelector('.option-cards').style.display = 'grid';
        newAppForm.style.display = 'none';
      });
    }
    
    const createAppButton = document.getElementById('create-app-button');
    if (createAppButton) {
      createAppButton.addEventListener('click', async () => {
        const nameInput = document.getElementById('app-name');
        const descInput = document.getElementById('app-description');
        
        if (!nameInput || !nameInput.value.trim()) {
          this.handleError('App name is required');
          return;
        }
        
        // Show loading indicator
        this.showProgress('Creating project...');
        
        try {
          // Create project via manager
          const projectId = await this.manager.createProject(
            nameInput.value.trim(),
            descInput ? descInput.value.trim() : ''
          );
          
          // Store project ID
          this.state.projectId = projectId;
          
          // Hide loading indicator
          this.hideProgress();
          
          // Continue to first workflow step
          this.setStep('domain');
        } catch (error) {
          this.handleError(error);
        }
      });
    }
  }
  
  /**
   * Render domain definition step
   * @private
   * @param {HTMLElement} container - Step container
   */
  _renderDomainStep(container) {
    // Check if project exists
    if (!this.state.projectId) {
      container.innerHTML = `
        <div class="error-message">
          No active project. Please create or select a project first.
          <button class="primary-button" id="go-welcome-button">Go to Welcome</button>
        </div>
      `;
      
      const welcomeButton = document.getElementById('go-welcome-button');
      if (welcomeButton) {
        welcomeButton.addEventListener('click', () => {
          this.setStep('welcome');
        });
      }
      
      return;
    }
    
    // Continue workflow
    this.showProgress('Loading domain definition step...');
    
    // Get current workflow state
    this.manager.continueWorkflow(this.state.projectId)
      .then(workflow => {
        this.hideProgress();
        
        if (workflow.result.status === 'completed') {
          // Domain already completed, show summary and continue
          container.innerHTML = `
            <div class="step-content">
              <h2>Domain Definition</h2>
              
              <div class="step-summary">
                <div class="summary-header">
                  <span class="status-badge completed">Completed</span>
                </div>
                
                <div class="domain-info">
                  <div class="info-item">
                    <div class="info-label">Purpose</div>
                    <div class="info-value">${workflow.result.data.purpose || 'Not specified'}</div>
                  </div>
                  
                  <div class="info-item">
                    <div class="info-label">Domain</div>
                    <div class="info-value">${workflow.result.data.domain || 'Not specified'}</div>
                  </div>
                  
                  <div class="info-item">
                    <div class="info-label">Target Audience</div>
                    <div class="info-value">${workflow.result.data.audience || 'Not specified'}</div>
                  </div>
                </div>
                
                <div class="form-actions">
                  <button class="secondary-button" id="edit-domain-button">Edit</button>
                  <button class="primary-button" id="continue-requirements-button">Continue to Requirements</button>
                </div>
              </div>
            </div>
          `;
          
          // Add event listeners
          const continueButton = document.getElementById('continue-requirements-button');
          if (continueButton) {
            continueButton.addEventListener('click', () => {
              this.setStep('requirements');
            });
          }
        } else if (workflow.result.status === 'awaiting_input') {
          // Show domain input form
          container.innerHTML = `
            <div class="step-content">
              <h2>Domain Definition</h2>
              
              <p class="step-description">
                Define the domain and purpose of your application to help generate appropriate requirements.
              </p>
              
              <div class="domain-form">
                ${workflow.result.requiredInputs.map(input => `
                  <div class="form-group">
                    <label for="${input.id}">${input.label}</label>
                    <textarea 
                      id="${input.id}" 
                      placeholder="${input.description}"
                      ${input.type === 'text' ? '' : 'type="text"'}
                    ></textarea>
                  </div>
                `).join('')}
                
                <div class="form-actions">
                  <button class="primary-button" id="submit-domain-button">Continue</button>
                </div>
              </div>
            </div>
          `;
          
          // Add event listener for form submission
          const submitButton = document.getElementById('submit-domain-button');
          if (submitButton) {
            submitButton.addEventListener('click', async () => {
              // Collect form data
              const domainData = {};
              
              workflow.result.requiredInputs.forEach(input => {
                const inputEl = document.getElementById(input.id);
                if (inputEl) {
                  domainData[input.id] = inputEl.value.trim();
                }
              });
              
              // Validate required fields
              if (!domainData.purpose) {
                this.handleError('App purpose is required');
                return;
              }
              
              // Show loading indicator
              this.showProgress('Analyzing domain...');
              
              try {
                // Submit domain data
                await this.manager.updateDomainStep(this.state.projectId, domainData);
                
                // Domain step will automatically continue to requirements
              } catch (error) {
                this.handleError(error);
              }
            });
          }
        } else {
          // Handle error or other status
          container.innerHTML = `
            <div class="error-message">
              Unexpected workflow status: ${workflow.result.status}
              <button class="primary-button" id="retry-button">Retry</button>
            </div>
          `;
          
          const retryButton = document.getElementById('retry-button');
          if (retryButton) {
            retryButton.addEventListener('click', () => {
              this._renderDomainStep(container);
            });
          }
        }
      })
      .catch(error => {
        this.hideProgress();
        this.handleError(error);
      });
  }
  
  /**
   * Handle step completed event
   * @private
   * @param {Object} event - Event data
   */
  _handleStepCompleted(event) {
    // Move to next step
    if (event.nextStep && this.state.currentStep === event.step) {
      this.setStep(event.nextStep);
    }
  }
  
  /**
   * Handle tests completed event
   * @private
   * @param {Object} event - Event data
   */
  _handleTestsCompleted(event) {
    // Update UI based on test results
    this.hideProgress();
    
    if (this.state.currentStep === 'testing') {
      // Refresh the testing step to show results
      this._renderStep();
    }
  }
  
  /**
   * Handle app published event
   * @private
   * @param {Object} event - Event data
   */
  _handleAppPublished(event) {
    this.hideProgress();
    
    if (this.state.currentStep === 'publishing') {
      // Move to results step
      this.setStep('results');
    }
  }
  
  /**
   * Handle export app action
   * @private
   * @param {Object} projectData - Project data
   */
  async _handleExportApp(projectData) {
    this.showProgress('Exporting app...');
    
    try {
      // Export app via manager
      const bundle = await this.manager.exportProject(this.state.projectId);
      
      // In a real implementation, this would trigger a download
      // For this reference implementation, just show success message
      this.hideProgress();
      
      alert('App exported successfully!');
    } catch (error) {
      this.handleError(error);
    }
  }
  
  /**
   * Attach global event listeners
   * @private
   */
  _attachEventListeners() {
    // Add any global event listeners here
  }
  
  /**
   * Escape HTML for safe rendering
   * @private
   * @param {string} html - HTML to escape
   * @returns {string} Escaped HTML
   */
  _escapeHtml(html) {
    const div = document.createElement('div');
    div.textContent = html;
    return div.innerHTML;
  }
  
  // Remaining step render methods would be implemented here
  // _renderRequirementsStep, _renderSpecificationStep, etc.
}

// Export for use in PrimeOS
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { AppFactoryUI };
} else if (typeof window !== 'undefined') {
  if (!window.PrimeOS) {
    window.PrimeOS = {};
  }
  window.PrimeOS.AppFactoryUI = AppFactoryUI;
}