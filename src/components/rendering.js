/**
 * PrimeOS JavaScript Library - Component Rendering
 * Rendering system for components
 * Version 1.0.0
 */

// Import Prime using CommonJS to avoid circular dependency
const Prime = require('../core.js');
// Ensure all modules are loaded in correct order
require('../mathematics.js');
require('../coherence.js');
require('../framework/index.js');
require('./base.js');

(function (Prime) {
  /**
   * Enhanced rendering system with cross-platform support
   */
  const render = {
    /**
     * Registered renderers by target type
     */
    renderers: new Map(),

    /**
     * Default rendering options
     */
    defaultOptions: {
      mode: '2d',
      interactive: false,
      dimensions: [300, 300],
      animate: false,
      theme: 'light',
    },

    /**
     * Render an object to a DOM element
     * @param {*} object - Object to render
     * @param {Element} element - DOM element
     * @param {Object} options - Rendering options
     * @returns {Element} Updated element
     */
    toDOM: function (object, element, options = {}) {
      if (!element) {
        throw new Prime.ValidationError('DOM element is required');
      }

      // Merge options with defaults
      const mergedOptions = { ...this.defaultOptions, ...options };

      // If object is a component, use its renderer if available
      if (object && object.meta && object.invariant) {
        try {
          // Check for various rendering method names
          if (typeof object.invariant.render === 'function') {
            return object.invariant.render.call(object, element, mergedOptions);
          } else if (typeof object.invariant.renderDOM === 'function') {
            return object.invariant.renderDOM.call(
              object,
              element,
              mergedOptions,
            );
          } else if (typeof object.invariant.renderToDOM === 'function') {
            return object.invariant.renderToDOM.call(
              object,
              element,
              mergedOptions,
            );
          } else if (typeof object.render === 'function') {
            return object.render(element, mergedOptions);
          }
        } catch (error) {
          Prime.Logger.error('Error rendering component:', error);
          element.textContent = `Error rendering component: ${error.message}`;
          return element;
        }
      }

      // Check if we have a specific renderer for this object type
      const objectType = this._getObjectType(object);
      const renderer = this.renderers.get(`dom:${objectType}`);

      if (renderer) {
        return renderer(object, element, mergedOptions);
      }

      // Handle different object types
      if (
        Prime.Clifford &&
        Prime.Clifford.isMultivector &&
        Prime.Clifford.isMultivector(object)
      ) {
        return this._renderMultivector(object, element, mergedOptions);
      }

      if (Prime.Utils.isArray(object)) {
        return this._renderArray(object, element, mergedOptions);
      }

      if (object instanceof HTMLElement) {
        element.innerHTML = '';
        element.appendChild(object);
        return element;
      }

      // Generic object rendering
      if (Prime.Utils.isObject(object)) {
        return this._renderObject(object, element, mergedOptions);
      }

      // Fallback to string representation
      element.textContent = String(object);
      return element;
    },

    /**
     * Render to a Canvas 2D context
     * @param {*} object - Object to render
     * @param {CanvasRenderingContext2D} ctx - Canvas 2D context
     * @param {Object} options - Rendering options
     * @returns {CanvasRenderingContext2D} Updated context
     */
    toCanvas: function (object, ctx, options = {}) {
      if (!ctx) {
        throw new Prime.ValidationError('Canvas context is required');
      }

      // Merge options with defaults
      const mergedOptions = { ...this.defaultOptions, ...options };

      // Set up dimensions
      const width =
        mergedOptions.dimensions[0] || (ctx.canvas ? ctx.canvas.width : 300);
      const height =
        mergedOptions.dimensions[1] || (ctx.canvas ? ctx.canvas.height : 150);

      // Clear canvas if method exists
      if (ctx.clearRect) {
        ctx.clearRect(0, 0, width, height);
      }

      // If object is a component, use its renderer if available
      if (object && object.meta && object.invariant) {
        try {
          // Check for various rendering method names
          if (typeof object.invariant.renderCanvas === 'function') {
            return object.invariant.renderCanvas.call(
              object,
              ctx,
              mergedOptions,
            );
          } else if (typeof object.invariant.renderToCanvas === 'function') {
            return object.invariant.renderToCanvas.call(
              object,
              ctx,
              mergedOptions,
            );
          } else if (typeof object.renderCanvas === 'function') {
            return object.renderCanvas(ctx, mergedOptions);
          } else if (
            typeof object.invariant.render === 'function' &&
            mergedOptions.target === 'canvas'
          ) {
            return object.invariant.render.call(object, ctx, mergedOptions);
          }
        } catch (error) {
          Prime.Logger.error('Error rendering component to canvas:', error);
          ctx.fillText(`Error: ${error.message}`, 10, 20);
          return ctx;
        }
      }

      // Check if we have a specific renderer for this object type
      const objectType = this._getObjectType(object);
      const renderer = this.renderers.get(`canvas:${objectType}`);

      if (renderer) {
        return renderer(object, ctx, mergedOptions);
      }

      // Handle different object types
      if (
        Prime.Clifford &&
        Prime.Clifford.isMultivector &&
        Prime.Clifford.isMultivector(object)
      ) {
        return this._renderMultivectorCanvas(object, ctx, mergedOptions);
      }

      if (Prime.Utils.isArray(object)) {
        return this._renderArrayCanvas(object, ctx, mergedOptions);
      }

      if (
        Prime.Lie &&
        Prime.Lie.isGroupElement &&
        Prime.Lie.isGroupElement(object)
      ) {
        return this._renderTransformationCanvas(object, ctx, mergedOptions);
      }

      // Fallback to text representation
      ctx.fillStyle = '#000';
      ctx.font = '12px sans-serif';
      ctx.fillText(String(object), 10, 20);

      return ctx;
    },

    /**
     * Render to WebGL context
     * @param {*} object - Object to render
     * @param {WebGLRenderingContext} gl - WebGL context
     * @param {Object} options - Rendering options
     * @returns {WebGLRenderingContext} Updated context
     */
    toWebGL: function (object, gl, options = {}) {
      if (!gl) {
        throw new Prime.ValidationError('WebGL context is required');
      }

      // Merge options with defaults
      const mergedOptions = { ...this.defaultOptions, ...options };

      // Clear the context
      gl.clearColor(0.0, 0.0, 0.0, 1.0);
      gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);

      // If object is a component, use its renderer if available
      if (
        object &&
        object.meta &&
        object.invariant &&
        object.invariant.renderWebGL
      ) {
        return object.invariant.renderWebGL(gl, mergedOptions);
      }

      // Check if we have a specific renderer for this object type
      const objectType = this._getObjectType(object);
      const renderer = this.renderers.get(`webgl:${objectType}`);

      if (renderer) {
        return renderer(object, gl, mergedOptions);
      }

      // Handle different object types
      if (
        Prime.Clifford &&
        Prime.Clifford.isMultivector &&
        Prime.Clifford.isMultivector(object)
      ) {
        return this._renderMultivectorWebGL(object, gl, mergedOptions);
      }

      // Fallback - do nothing and return the context
      Prime.Logger.warn('No WebGL renderer available for object', {
        objectType,
      });

      return gl;
    },

    /**
     * Render to SVG
     * @param {*} object - Object to render
     * @param {Object} options - Rendering options
     * @returns {string} SVG markup
     */
    toSVG: function (object, options = {}) {
      // Merge options with defaults
      const mergedOptions = { ...this.defaultOptions, ...options };

      // If object is a component, use its renderer if available
      if (
        object &&
        object.meta &&
        object.invariant &&
        object.invariant.renderSVG
      ) {
        return object.invariant.renderSVG(mergedOptions);
      }

      // Check if we have a specific renderer for this object type
      const objectType = this._getObjectType(object);
      const renderer = this.renderers.get(`svg:${objectType}`);

      if (renderer) {
        return renderer(object, mergedOptions);
      }

      // Handle different object types
      if (
        Prime.Clifford &&
        Prime.Clifford.isMultivector &&
        Prime.Clifford.isMultivector(object)
      ) {
        return this._renderMultivectorSVG(object, mergedOptions);
      }

      if (Prime.Utils.isArray(object)) {
        return this._renderArraySVG(object, mergedOptions);
      }

      // Fallback to basic SVG with text
      const width = mergedOptions.dimensions[0] || 300;
      const height = mergedOptions.dimensions[1] || 150;

      return `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${width} ${height}" width="${width}" height="${height}">
        <rect width="${width}" height="${height}" fill="#f0f0f0" />
        <text x="10" y="20" font-family="sans-serif" font-size="12">${String(object)}</text>
      </svg>`;
    },

    /**
     * Register a renderer
     * @param {string} targetType - Target type (dom, canvas, webgl, svg)
     * @param {string} objectType - Object type to render
     * @param {Function} rendererFn - Renderer function
     * @returns {boolean} Success
     */
    registerRenderer: function (targetType, objectType, rendererFn) {
      if (!Prime.Utils.isString(targetType)) {
        throw new Prime.ValidationError('Target type must be a string');
      }

      if (!Prime.Utils.isString(objectType)) {
        throw new Prime.ValidationError('Object type must be a string');
      }

      if (!Prime.Utils.isFunction(rendererFn)) {
        throw new Prime.ValidationError('Renderer must be a function');
      }

      this.renderers.set(`${targetType}:${objectType}`, rendererFn);
      return true;
    },

    /**
     * Batch render multiple components to multiple DOM elements
     * @param {Array} components - Array of components to render
     * @param {Array} elements - Array of DOM elements
     * @param {Object} options - Rendering options
     * @returns {Array} Array of updated elements
     */
    batchRender: function (components, elements, options = {}) {
      if (!Array.isArray(components)) {
        throw new Prime.ValidationError('Components must be an array');
      }

      if (!Array.isArray(elements)) {
        throw new Prime.ValidationError('Elements must be an array');
      }

      if (components.length !== elements.length) {
        throw new Prime.ValidationError(
          'Components and elements arrays must have the same length',
        );
      }

      // Merge options with defaults
      const mergedOptions = { ...this.defaultOptions, ...options };

      // Render each component in parallel
      const results = [];
      for (let i = 0; i < components.length; i++) {
        results.push(this.toDOM(components[i], elements[i], mergedOptions));
      }

      return results;
    },

    /**
     * Enable or disable rendering caching
     * @param {boolean} enable - Whether to enable caching
     * @returns {boolean} Caching status
     */
    enableCaching: function (enable) {
      this._cacheEnabled = enable === true;

      // Clear cache when disabling
      if (!this._cacheEnabled) {
        this._clearCache();
      }

      return this._cacheEnabled;
    },

    /**
     * Check if caching is enabled
     * @returns {boolean} Whether caching is enabled
     */
    isCachingEnabled: function () {
      return this._cacheEnabled === true;
    },

    /**
     * Clear the render cache
     * @private
     */
    _clearCache: function () {
      this._renderCache = new Map();
    },

    /**
     * Initialize cache if not already done
     * @private
     */
    _initCache: function () {
      if (!this._renderCache) {
        this._renderCache = new Map();
      }
    },

    /**
     * Create animation frames
     * @param {Function} renderFn - Render function
     * @param {Object} options - Animation options
     * @returns {Object} Animation controller
     */
    animate: function (renderFn, options = {}) {
      if (!Prime.Utils.isFunction(renderFn)) {
        throw new Prime.ValidationError('Render function is required');
      }

      const mergedOptions = {
        duration: options.duration || 1000,
        fps: options.fps || 60,
        easing: options.easing || ((t) => t),
        onComplete: options.onComplete || (() => {}),
        onFrame: options.onFrame || (() => {}),
      };

      let startTime = null;
      let animationId = null;
      let isRunning = false;

      const controller = {
        start: function () {
          if (isRunning) return;

          isRunning = true;
          startTime = Date.now();

          const animate = () => {
            const elapsed = Date.now() - startTime;
            const progress = Math.min(elapsed / mergedOptions.duration, 1);
            const easedProgress = mergedOptions.easing(progress);

            // Execute render function with progress
            renderFn(easedProgress);

            // Call frame callback
            mergedOptions.onFrame(easedProgress);

            if (progress < 1) {
              animationId = requestAnimationFrame(animate);
            } else {
              isRunning = false;
              mergedOptions.onComplete();
            }
          };

          animate();
          return this;
        },

        stop: function () {
          if (!isRunning) return;

          if (animationId) {
            cancelAnimationFrame(animationId);
            animationId = null;
          }

          isRunning = false;
          return this;
        },

        isRunning: function () {
          return isRunning;
        },

        restart: function () {
          this.stop();
          this.start();
          return this;
        },
      };

      return controller;
    },

    /**
     * Get object type for rendering
     * @private
     * @param {*} object - Object to render
     * @returns {string} Object type
     */
    _getObjectType: function (object) {
      if (object === null) return 'null';
      if (object === undefined) return 'undefined';

      // Check for components
      if (object && object.meta && object.variant && object.lifecycle) {
        return `component:${object.meta.type || 'generic'}`;
      }

      // Check for specialized types
      if (
        Prime.Clifford &&
        Prime.Clifford.isMultivector &&
        Prime.Clifford.isMultivector(object)
      ) {
        return 'multivector';
      }

      if (
        Prime.Lie &&
        Prime.Lie.isGroupElement &&
        Prime.Lie.isGroupElement(object)
      ) {
        return 'lieGroupElement';
      }

      if (Prime.UOR && Prime.UOR.isObject && Prime.UOR.isObject(object)) {
        return 'uorObject';
      }

      // Standard JavaScript types
      if (Array.isArray(object)) return 'array';
      if (object instanceof Date) return 'date';
      if (object instanceof RegExp) return 'regexp';
      if (object instanceof Map) return 'map';
      if (object instanceof Set) return 'set';
      if (object instanceof Promise) return 'promise';
      if (object instanceof Error) return 'error';
      if (typeof HTMLElement !== 'undefined' && object instanceof HTMLElement)
        return 'htmlElement';
      if (typeof SVGElement !== 'undefined' && object instanceof SVGElement)
        return 'svgElement';

      // Primitive types
      if (typeof object === 'string') return 'string';
      if (typeof object === 'number') return 'number';
      if (typeof object === 'boolean') return 'boolean';
      if (typeof object === 'function') return 'function';
      if (typeof object === 'object') return 'object';

      return typeof object;
    },

    // Production implementations for rendering specific object types

    /**
     * Render a multivector to a DOM element
     * @private
     * @param {Object} multivector - Multivector to render
     * @param {Element} element - DOM element
     * @param {Object} options - Rendering options
     * @returns {Element} Updated element
     */
    _renderMultivector: function (multivector, element, options) {
      // Create container
      const container = document.createElement('div');
      container.className = 'primeos-multivector';

      // Add header
      const header = document.createElement('div');
      header.className = 'primeos-multivector-header';
      header.textContent = 'Multivector';
      container.appendChild(header);

      // Create table for components
      const table = document.createElement('table');
      table.className = 'primeos-multivector-components';

      // Add table header
      const thead = document.createElement('thead');
      const headerRow = document.createElement('tr');

      const gradeHeader = document.createElement('th');
      gradeHeader.textContent = 'Grade';
      headerRow.appendChild(gradeHeader);

      const basisHeader = document.createElement('th');
      basisHeader.textContent = 'Basis';
      headerRow.appendChild(basisHeader);

      const valueHeader = document.createElement('th');
      valueHeader.textContent = 'Value';
      headerRow.appendChild(valueHeader);

      thead.appendChild(headerRow);
      table.appendChild(thead);

      // Add table body
      const tbody = document.createElement('tbody');

      // Extract components from multivector
      const components = Prime.Clifford.extractComponents(multivector);

      // Sort components by grade
      components.sort((a, b) => a.grade - b.grade);

      // Create rows for each component
      for (const component of components) {
        const row = document.createElement('tr');

        const gradeCell = document.createElement('td');
        gradeCell.textContent = component.grade;
        row.appendChild(gradeCell);

        const basisCell = document.createElement('td');
        basisCell.textContent = component.basis;
        row.appendChild(basisCell);

        const valueCell = document.createElement('td');
        valueCell.textContent = component.value
          .toFixed(6)
          .replace(/\.?0+$/, '');
        row.appendChild(valueCell);

        tbody.appendChild(row);
      }

      table.appendChild(tbody);
      container.appendChild(table);

      // Add visualization if requested
      if (options.visualize !== false && components.length > 0) {
        const visualContainer = document.createElement('div');
        visualContainer.className = 'primeos-multivector-visualization';
        visualContainer.style.width =
          (options.dimensions && options.dimensions[0]) || '200px';
        visualContainer.style.height =
          (options.dimensions && options.dimensions[1]) || '200px';

        // Create a canvas element for visualization
        const canvas = document.createElement('canvas');
        canvas.width = parseInt(visualContainer.style.width);
        canvas.height = parseInt(visualContainer.style.height);
        visualContainer.appendChild(canvas);

        // Visualize the multivector on the canvas
        const ctx = canvas.getContext('2d');
        this._renderMultivectorCanvas(multivector, ctx, options);

        container.appendChild(visualContainer);
      }

      // Clear the element and add the container
      element.innerHTML = '';
      element.appendChild(container);

      return element;
    },

    /**
     * Render a multivector to a canvas context
     * @private
     * @param {Object} multivector - Multivector to render
     * @param {CanvasRenderingContext2D} ctx - Canvas context
     * @param {Object} options - Rendering options
     * @returns {CanvasRenderingContext2D} Updated context
     */
    _renderMultivectorCanvas: function (multivector, ctx, options) {
      // Get canvas dimensions
      const width = ctx.canvas.width;
      const height = ctx.canvas.height;

      // Clear the canvas
      ctx.clearRect(0, 0, width, height);

      // Set up coordinate system (origin at center)
      ctx.save();
      ctx.translate(width / 2, height / 2);

      // Extract grades 1 and 2 for visualization (vectors and bivectors)
      const components = Prime.Clifford.extractComponents(multivector);
      const vectors = components.filter((c) => c.grade === 1);
      const bivectors = components.filter((c) => c.grade === 2);

      // Determine scale based on largest component
      const maxValue = Math.max(
        0.1,
        ...components.map((c) => Math.abs(c.value)),
      );
      const scale = (Math.min(width, height) * 0.4) / maxValue;

      // Draw coordinate axes
      ctx.strokeStyle = '#ccc';
      ctx.lineWidth = 1;
      ctx.beginPath();
      ctx.moveTo(-width / 2, 0);
      ctx.lineTo(width / 2, 0);
      ctx.moveTo(0, -height / 2);
      ctx.lineTo(0, height / 2);
      ctx.stroke();

      // Draw vectors (grade 1 components)
      if (vectors.length > 0) {
        ctx.lineWidth = 2;
        ctx.strokeStyle = '#36c';

        for (const vector of vectors) {
          const basis = vector.basis;
          const value = vector.value;

          ctx.beginPath();
          ctx.moveTo(0, 0);

          // Handle different basis elements (e1, e2, e3, etc.)
          if (basis === 'e1') {
            ctx.lineTo(value * scale, 0);
          } else if (basis === 'e2') {
            ctx.lineTo(0, -value * scale); // Negative for canvas y-axis
          } else if (basis === 'e3') {
            // For 3D, we use a projection
            ctx.lineTo(value * scale * 0.7, value * scale * 0.7);
          } else {
            // For higher dimensions, we position them around a circle
            const angle = (parseInt(basis.substring(1)) * Math.PI) / 4;
            ctx.lineTo(
              Math.cos(angle) * value * scale,
              -Math.sin(angle) * value * scale,
            );
          }

          ctx.stroke();

          // Draw arrowhead
          if (basis === 'e1' || basis === 'e2' || basis === 'e3') {
            let x = 0,
              y = 0;

            if (basis === 'e1') {
              x = value * scale;
              y = 0;
            } else if (basis === 'e2') {
              x = 0;
              y = -value * scale;
            } else if (basis === 'e3') {
              x = value * scale * 0.7;
              y = value * scale * 0.7;
            }

            const angle = Math.atan2(y, x);
            const arrowSize = 8;

            ctx.beginPath();
            ctx.moveTo(x, y);
            ctx.lineTo(
              x - arrowSize * Math.cos(angle - Math.PI / 6),
              y - arrowSize * Math.sin(angle - Math.PI / 6),
            );
            ctx.lineTo(
              x - arrowSize * Math.cos(angle + Math.PI / 6),
              y - arrowSize * Math.sin(angle + Math.PI / 6),
            );
            ctx.closePath();
            ctx.fillStyle = '#36c';
            ctx.fill();
          }
        }
      }

      // Draw bivectors (grade 2 components)
      if (bivectors.length > 0) {
        ctx.lineWidth = 1;
        ctx.fillStyle = 'rgba(255, 102, 0, 0.3)';
        ctx.strokeStyle = 'rgb(255, 102, 0)';

        for (const bivector of bivectors) {
          const basis = bivector.basis;
          const value = bivector.value;

          // Handle different bivector planes
          if (basis === 'e12') {
            // e1∧e2 plane (xy-plane)
            const radius = Math.abs(value) * scale * 0.8;

            ctx.beginPath();
            ctx.arc(0, 0, radius, 0, 2 * Math.PI);
            ctx.fill();
            ctx.stroke();

            // Add orientation arrow
            ctx.beginPath();
            ctx.moveTo(radius * 0.7, 0);
            ctx.arc(
              0,
              0,
              radius * 0.7,
              0,
              value > 0 ? -Math.PI / 2 : Math.PI / 2,
            );
            ctx.stroke();

            // Add arrowhead
            const arrowAngle = value > 0 ? -Math.PI / 2 : Math.PI / 2;
            const arrowX = radius * 0.7 * Math.cos(arrowAngle);
            const arrowY = radius * 0.7 * Math.sin(arrowAngle);

            ctx.beginPath();
            ctx.moveTo(arrowX, arrowY);
            ctx.lineTo(
              arrowX + 5 * Math.cos(arrowAngle - 2.5),
              arrowY + 5 * Math.sin(arrowAngle - 2.5),
            );
            ctx.lineTo(
              arrowX + 5 * Math.cos(arrowAngle + 2.5),
              arrowY + 5 * Math.sin(arrowAngle + 2.5),
            );
            ctx.closePath();
            ctx.fillStyle = 'rgb(255, 102, 0)';
            ctx.fill();
          } else if (basis === 'e13' || basis === 'e23') {
            // Represent other planes with ellipses
            ctx.save();
            if (basis === 'e13') {
              ctx.rotate(Math.PI / 4); // Rotate for e1∧e3 plane
            } else {
              ctx.rotate(-Math.PI / 4); // Rotate for e2∧e3 plane
            }

            ctx.scale(1, 0.5); // Create an ellipse for perspective

            const radius = Math.abs(value) * scale * 0.6;

            ctx.beginPath();
            ctx.arc(0, 0, radius, 0, 2 * Math.PI);
            ctx.restore();
            ctx.fill();
            ctx.stroke();
          }
        }
      }

      // Restore original context
      ctx.restore();

      // Add text label
      ctx.font = '12px Arial';
      ctx.fillStyle = '#000';
      ctx.textAlign = 'left';
      ctx.textBaseline = 'top';

      // Create a compact representation of the multivector
      let label = 'MV:';
      for (const component of components) {
        label += ` ${component.value.toFixed(2)}${component.basis}`;
      }

      // Truncate if too long
      if (label.length > 30) {
        label = label.substring(0, 27) + '...';
      }

      ctx.fillText(label, 10, 10);

      return ctx;
    },

    /**
     * Render a multivector using WebGL
     * @private
     * @param {Object} multivector - Multivector to render
     * @param {WebGLRenderingContext} gl - WebGL context
     * @param {Object} options - Rendering options
     * @returns {WebGLRenderingContext} Updated context
     */
    _renderMultivectorWebGL: function (multivector, gl, options) {
      // Only implement if Prime.Clifford.WebGLRenderer is available
      if (Prime.Clifford && Prime.Clifford.WebGLRenderer) {
        return Prime.Clifford.WebGLRenderer.render(multivector, gl, options);
      }

      // Otherwise create a basic WebGL visualization

      // Get canvas dimensions
      const width = gl.canvas.width;
      const height = gl.canvas.height;

      // Clear the canvas
      gl.viewport(0, 0, width, height);
      gl.clearColor(0.95, 0.95, 0.95, 1.0);
      gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);

      // Enable depth testing
      gl.enable(gl.DEPTH_TEST);

      // Extract components from multivector
      const components = Prime.Clifford.extractComponents(multivector);

      // Only proceed if we have components to visualize
      if (components.length === 0) {
        return gl;
      }

      // Create the shader program
      const vertexShaderSource = `
        attribute vec4 aPosition;
        attribute vec4 aColor;
        uniform mat4 uModelViewMatrix;
        uniform mat4 uProjectionMatrix;
        varying vec4 vColor;
        
        void main() {
          gl_Position = uProjectionMatrix * uModelViewMatrix * aPosition;
          vColor = aColor;
        }
      `;

      const fragmentShaderSource = `
        precision mediump float;
        varying vec4 vColor;
        
        void main() {
          gl_FragColor = vColor;
        }
      `;

      // Create shaders
      const vertexShader = gl.createShader(gl.VERTEX_SHADER);
      gl.shaderSource(vertexShader, vertexShaderSource);
      gl.compileShader(vertexShader);

      const fragmentShader = gl.createShader(gl.FRAGMENT_SHADER);
      gl.shaderSource(fragmentShader, fragmentShaderSource);
      gl.compileShader(fragmentShader);

      // Create shader program
      const shaderProgram = gl.createProgram();
      gl.attachShader(shaderProgram, vertexShader);
      gl.attachShader(shaderProgram, fragmentShader);
      gl.linkProgram(shaderProgram);
      gl.useProgram(shaderProgram);

      // Define basic perspective matrix
      const fieldOfView = (45 * Math.PI) / 180;
      const aspect = width / height;
      const zNear = 0.1;
      const zFar = 100.0;

      const projectionMatrix = [
        1 / (aspect * Math.tan(fieldOfView / 2)),
        0,
        0,
        0,
        0,
        1 / Math.tan(fieldOfView / 2),
        0,
        0,
        0,
        0,
        -(zFar + zNear) / (zFar - zNear),
        -1,
        0,
        0,
        -(2 * zFar * zNear) / (zFar - zNear),
        0,
      ];

      // Define model-view matrix (a simple translation back 6 units)
      const modelViewMatrix = [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -6, 1];

      // Get shader locations
      const positionAttributeLocation = gl.getAttribLocation(
        shaderProgram,
        'aPosition',
      );
      const colorAttributeLocation = gl.getAttribLocation(
        shaderProgram,
        'aColor',
      );
      const projectionMatrixLocation = gl.getUniformLocation(
        shaderProgram,
        'uProjectionMatrix',
      );
      const modelViewMatrixLocation = gl.getUniformLocation(
        shaderProgram,
        'uModelViewMatrix',
      );

      // Set up uniforms
      gl.uniformMatrix4fv(projectionMatrixLocation, false, projectionMatrix);
      gl.uniformMatrix4fv(modelViewMatrixLocation, false, modelViewMatrix);

      // Draw axes
      const axisVertices = [
        // X axis - red
        -2, 0, 0, 1, 2, 0, 0, 1,
        // Y axis - green
        0, -2, 0, 1, 0, 2, 0, 1,
        // Z axis - blue
        0, 0, -2, 1, 0, 0, 2, 1,
      ];

      const axisColors = [
        // X axis - red
        1, 0, 0, 1, 1, 0, 0, 1,
        // Y axis - green
        0, 1, 0, 1, 0, 1, 0, 1,
        // Z axis - blue
        0, 0, 1, 1, 0, 0, 1, 1,
      ];

      // Create axis buffers
      const axisPositionBuffer = gl.createBuffer();
      gl.bindBuffer(gl.ARRAY_BUFFER, axisPositionBuffer);
      gl.bufferData(
        gl.ARRAY_BUFFER,
        new Float32Array(axisVertices),
        gl.STATIC_DRAW,
      );

      const axisColorBuffer = gl.createBuffer();
      gl.bindBuffer(gl.ARRAY_BUFFER, axisColorBuffer);
      gl.bufferData(
        gl.ARRAY_BUFFER,
        new Float32Array(axisColors),
        gl.STATIC_DRAW,
      );

      // Draw axes
      gl.bindBuffer(gl.ARRAY_BUFFER, axisPositionBuffer);
      gl.vertexAttribPointer(
        positionAttributeLocation,
        4,
        gl.FLOAT,
        false,
        0,
        0,
      );
      gl.enableVertexAttribArray(positionAttributeLocation);

      gl.bindBuffer(gl.ARRAY_BUFFER, axisColorBuffer);
      gl.vertexAttribPointer(colorAttributeLocation, 4, gl.FLOAT, false, 0, 0);
      gl.enableVertexAttribArray(colorAttributeLocation);

      gl.drawArrays(gl.LINES, 0, 6);

      // Now draw the multivector representation
      // This is a simplified implementation - a full implementation would be much more complex

      return gl;
    },

    _renderMultivectorSVG: function (multivector, options) {
      const width = options.dimensions[0] || 300;
      const height = options.dimensions[1] || 150;
      return `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${width} ${height}" width="${width}" height="${height}">
        <text x="10" y="20">Multivector: ${JSON.stringify(multivector)}</text>
      </svg>`;
    },

    _renderArray: function (array, element, options) {
      if (options.mode === 'table') {
        const table = document.createElement('table');
        const tbody = document.createElement('tbody');

        array.forEach((item, index) => {
          const row = document.createElement('tr');
          const indexCell = document.createElement('td');
          indexCell.textContent = index;
          row.appendChild(indexCell);

          const valueCell = document.createElement('td');
          valueCell.textContent = String(item);
          row.appendChild(valueCell);

          tbody.appendChild(row);
        });

        table.appendChild(tbody);
        element.innerHTML = '';
        element.appendChild(table);
      } else {
        element.textContent = JSON.stringify(array);
      }

      return element;
    },

    _renderArrayCanvas: function (array, ctx, options) {
      ctx.fillText(JSON.stringify(array), 10, 20);
      return ctx;
    },

    _renderArraySVG: function (array, options) {
      const width = options.dimensions[0] || 300;
      const height = options.dimensions[1] || 150;
      return `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${width} ${height}" width="${width}" height="${height}">
        <text x="10" y="20">${JSON.stringify(array)}</text>
      </svg>`;
    },

    _renderTransformationCanvas: function (transformation, ctx, options) {
      ctx.fillText(`Transformation: ${JSON.stringify(transformation)}`, 10, 20);
      return ctx;
    },

    _renderObject: function (object, element, options) {
      if (options.mode === 'table') {
        const table = document.createElement('table');
        const tbody = document.createElement('tbody');

        Object.entries(object).forEach(([key, value]) => {
          const row = document.createElement('tr');
          const keyCell = document.createElement('td');
          keyCell.textContent = key;
          row.appendChild(keyCell);

          const valueCell = document.createElement('td');
          valueCell.textContent = String(value);
          row.appendChild(valueCell);

          tbody.appendChild(row);
        });

        table.appendChild(tbody);
        element.innerHTML = '';
        element.appendChild(table);
      } else {
        element.textContent = JSON.stringify(object);
      }

      return element;
    },
  };

  // Export render to Prime
  Prime.render = render;

  // Publish component module loaded event
  Prime.EventBus.publish('module:loaded', { name: 'component-rendering' });
})(Prime);

// CommonJS export (no ES module export to avoid circular dependency)
if (typeof module !== 'undefined' && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== 'undefined') {
  window.Prime = Prime;
}
