/**
 * PrimeOS JavaScript Library - Component Rendering
 * Rendering system for components
 * Version 1.0.0
 */

// Import Prime using CommonJS to avoid circular dependency
const Prime = require("../core.js");
// Ensure all modules are loaded in correct order
require("../mathematics.js");
require("../coherence.js");
require("../framework/index.js");
require("./base.js");

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
      mode: "2d",
      interactive: false,
      dimensions: [300, 300],
      animate: false,
      theme: "light",
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
        throw new Prime.ValidationError("DOM element is required");
      }

      // Merge options with defaults
      const mergedOptions = { ...this.defaultOptions, ...options };

      // If object is a component, use its renderer if available
      if (object && object.meta && object.invariant) {
        try {
          // Check for various rendering method names
          if (typeof object.invariant.render === "function") {
            return object.invariant.render.call(object, element, mergedOptions);
          } else if (typeof object.invariant.renderDOM === "function") {
            return object.invariant.renderDOM.call(
              object,
              element,
              mergedOptions,
            );
          } else if (typeof object.invariant.renderToDOM === "function") {
            return object.invariant.renderToDOM.call(
              object,
              element,
              mergedOptions,
            );
          } else if (typeof object.render === "function") {
            return object.render(element, mergedOptions);
          }
        } catch (error) {
          Prime.Logger.error("Error rendering component:", error);
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
        element.innerHTML = "";
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
        throw new Prime.ValidationError("Canvas context is required");
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
          if (typeof object.invariant.renderCanvas === "function") {
            return object.invariant.renderCanvas.call(
              object,
              ctx,
              mergedOptions,
            );
          } else if (typeof object.invariant.renderToCanvas === "function") {
            return object.invariant.renderToCanvas.call(
              object,
              ctx,
              mergedOptions,
            );
          } else if (typeof object.renderCanvas === "function") {
            return object.renderCanvas(ctx, mergedOptions);
          } else if (
            typeof object.invariant.render === "function" &&
            mergedOptions.target === "canvas"
          ) {
            return object.invariant.render.call(object, ctx, mergedOptions);
          }
        } catch (error) {
          Prime.Logger.error("Error rendering component to canvas:", error);
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
      ctx.fillStyle = "#000";
      ctx.font = "12px sans-serif";
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
        throw new Prime.ValidationError("WebGL context is required");
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
      Prime.Logger.warn("No WebGL renderer available for object", {
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
        throw new Prime.ValidationError("Target type must be a string");
      }

      if (!Prime.Utils.isString(objectType)) {
        throw new Prime.ValidationError("Object type must be a string");
      }

      if (!Prime.Utils.isFunction(rendererFn)) {
        throw new Prime.ValidationError("Renderer must be a function");
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
        throw new Prime.ValidationError("Components must be an array");
      }

      if (!Array.isArray(elements)) {
        throw new Prime.ValidationError("Elements must be an array");
      }

      if (components.length !== elements.length) {
        throw new Prime.ValidationError(
          "Components and elements arrays must have the same length",
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
        throw new Prime.ValidationError("Render function is required");
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
      if (object === null) return "null";
      if (object === undefined) return "undefined";

      // Check for components
      if (object && object.meta && object.variant && object.lifecycle) {
        return `component:${object.meta.type || "generic"}`;
      }

      // Check for specialized types
      if (
        Prime.Clifford &&
        Prime.Clifford.isMultivector &&
        Prime.Clifford.isMultivector(object)
      ) {
        return "multivector";
      }

      if (
        Prime.Lie &&
        Prime.Lie.isGroupElement &&
        Prime.Lie.isGroupElement(object)
      ) {
        return "lieGroupElement";
      }

      if (Prime.UOR && Prime.UOR.isObject && Prime.UOR.isObject(object)) {
        return "uorObject";
      }

      // Standard JavaScript types
      if (Array.isArray(object)) return "array";
      if (object instanceof Date) return "date";
      if (object instanceof RegExp) return "regexp";
      if (object instanceof Map) return "map";
      if (object instanceof Set) return "set";
      if (object instanceof Promise) return "promise";
      if (object instanceof Error) return "error";
      if (typeof HTMLElement !== "undefined" && object instanceof HTMLElement)
        return "htmlElement";
      if (typeof SVGElement !== "undefined" && object instanceof SVGElement)
        return "svgElement";

      // Primitive types
      if (typeof object === "string") return "string";
      if (typeof object === "number") return "number";
      if (typeof object === "boolean") return "boolean";
      if (typeof object === "function") return "function";
      if (typeof object === "object") return "object";

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
      const container = document.createElement("div");
      container.className = "primeos-multivector";

      // Add header
      const header = document.createElement("div");
      header.className = "primeos-multivector-header";
      header.textContent = "Multivector";
      container.appendChild(header);

      // Create table for components
      const table = document.createElement("table");
      table.className = "primeos-multivector-components";

      // Add table header
      const thead = document.createElement("thead");
      const headerRow = document.createElement("tr");

      const gradeHeader = document.createElement("th");
      gradeHeader.textContent = "Grade";
      headerRow.appendChild(gradeHeader);

      const basisHeader = document.createElement("th");
      basisHeader.textContent = "Basis";
      headerRow.appendChild(basisHeader);

      const valueHeader = document.createElement("th");
      valueHeader.textContent = "Value";
      headerRow.appendChild(valueHeader);

      thead.appendChild(headerRow);
      table.appendChild(thead);

      // Add table body
      const tbody = document.createElement("tbody");

      // Extract components from multivector
      const components = Prime.Clifford.extractComponents(multivector);

      // Sort components by grade
      components.sort((a, b) => a.grade - b.grade);

      // Create rows for each component
      for (const component of components) {
        const row = document.createElement("tr");

        const gradeCell = document.createElement("td");
        gradeCell.textContent = component.grade;
        row.appendChild(gradeCell);

        const basisCell = document.createElement("td");
        basisCell.textContent = component.basis;
        row.appendChild(basisCell);

        const valueCell = document.createElement("td");
        valueCell.textContent = component.value
          .toFixed(6)
          .replace(/\.?0+$/, "");
        row.appendChild(valueCell);

        tbody.appendChild(row);
      }

      table.appendChild(tbody);
      container.appendChild(table);

      // Add visualization if requested
      if (options.visualize !== false && components.length > 0) {
        const visualContainer = document.createElement("div");
        visualContainer.className = "primeos-multivector-visualization";
        visualContainer.style.width =
          (options.dimensions && options.dimensions[0]) || "200px";
        visualContainer.style.height =
          (options.dimensions && options.dimensions[1]) || "200px";

        // Create a canvas element for visualization
        const canvas = document.createElement("canvas");
        canvas.width = parseInt(visualContainer.style.width);
        canvas.height = parseInt(visualContainer.style.height);
        visualContainer.appendChild(canvas);

        // Visualize the multivector on the canvas
        const ctx = canvas.getContext("2d");
        this._renderMultivectorCanvas(multivector, ctx, options);

        container.appendChild(visualContainer);
      }

      // Clear the element and add the container
      element.innerHTML = "";
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
      ctx.strokeStyle = "#ccc";
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
        ctx.strokeStyle = "#36c";

        for (const vector of vectors) {
          const basis = vector.basis;
          const value = vector.value;

          ctx.beginPath();
          ctx.moveTo(0, 0);

          // Handle different basis elements (e1, e2, e3, etc.)
          if (basis === "e1") {
            ctx.lineTo(value * scale, 0);
          } else if (basis === "e2") {
            ctx.lineTo(0, -value * scale); // Negative for canvas y-axis
          } else if (basis === "e3") {
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
          if (basis === "e1" || basis === "e2" || basis === "e3") {
            let x = 0,
              y = 0;

            if (basis === "e1") {
              x = value * scale;
              y = 0;
            } else if (basis === "e2") {
              x = 0;
              y = -value * scale;
            } else if (basis === "e3") {
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
            ctx.fillStyle = "#36c";
            ctx.fill();
          }
        }
      }

      // Draw bivectors (grade 2 components)
      if (bivectors.length > 0) {
        ctx.lineWidth = 1;
        ctx.fillStyle = "rgba(255, 102, 0, 0.3)";
        ctx.strokeStyle = "rgb(255, 102, 0)";

        for (const bivector of bivectors) {
          const basis = bivector.basis;
          const value = bivector.value;

          // Handle different bivector planes
          if (basis === "e12") {
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
            ctx.fillStyle = "rgb(255, 102, 0)";
            ctx.fill();
          } else if (basis === "e13" || basis === "e23") {
            // Represent other planes with ellipses
            ctx.save();
            if (basis === "e13") {
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
      ctx.font = "12px Arial";
      ctx.fillStyle = "#000";
      ctx.textAlign = "left";
      ctx.textBaseline = "top";

      // Create a compact representation of the multivector
      let label = "MV:";
      for (const component of components) {
        label += ` ${component.value.toFixed(2)}${component.basis}`;
      }

      // Truncate if too long
      if (label.length > 30) {
        label = label.substring(0, 27) + "...";
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
        "aPosition",
      );
      const colorAttributeLocation = gl.getAttribLocation(
        shaderProgram,
        "aColor",
      );
      const projectionMatrixLocation = gl.getUniformLocation(
        shaderProgram,
        "uProjectionMatrix",
      );
      const modelViewMatrixLocation = gl.getUniformLocation(
        shaderProgram,
        "uModelViewMatrix",
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
      try {
        // Create vertex data based on multivector components
        const vertexData = [];
        const colorData = [];
        
        // Process each component based on its grade
        for (const component of components) {
          const { grade, value: coefficient, basis } = component;
          
          // Only visualize components with non-zero coefficients
          if (Math.abs(coefficient) < 0.00001) {
            continue;
          }
          
          // Get the absolute coefficient (for scaling)
          const absCoef = Math.abs(coefficient);
          // Normalize coefficient for visualization (min 0.1, max 1.0)
          const normCoef = 0.1 + 0.9 * Math.min(absCoef, 1.0);
          
          // Convert coefficient to color: positive = blue-green, negative = red-orange
          const isPositive = coefficient > 0;
          const r = isPositive ? 0 : 1.0;
          const g = isPositive ? 0.8 * normCoef : 0.5 * normCoef;
          const b = isPositive ? 1.0 * normCoef : 0;
          const alpha = 0.7 + 0.3 * normCoef;
          
          // Process by grade
          switch (grade) {
            case 0: // Scalar - draw a point at origin
              vertexData.push(0, 0, 0, 1);
              colorData.push(r, g, b, alpha);
              break;
              
            case 1: // Vector - draw a line
              // Extract coordinates from basis
              const coords = [0, 0, 0, 0];
              for (let i = 0; i < basis.length; i++) {
                const basisIdx = parseInt(basis[i].substring(1)) - 1;
                if (basisIdx >= 0 && basisIdx < 3) {
                  coords[basisIdx] = coefficient;
                }
              }
              
              // Create line from origin to point
              vertexData.push(
                0, 0, 0, 1,                       // Origin
                coords[0], coords[1], coords[2], 1 // End point
              );
              
              // Same color for both vertices
              colorData.push(
                r, g, b, alpha,
                r, g, b, alpha
              );
              break;
              
            case 2: // Bivector - draw a parallelogram
              // Extract plane information from basis (e.g., "e12", "e23", "e31")
              const plane = basis.substring(1).split('').map(c => parseInt(c) - 1);
              const scale = normCoef;
              
              // Only handle standard basis planes (xy, yz, zx)
              if (plane.length === 2 && 
                  plane[0] >= 0 && plane[0] < 3 && 
                  plane[1] >= 0 && plane[1] < 3) {
                
                // Create basis vectors for the plane
                const v1 = [0, 0, 0];
                const v2 = [0, 0, 0];
                v1[plane[0]] = scale;
                v2[plane[1]] = scale;
                
                // Create vertices for parallelogram
                const v3 = [v1[0] + v2[0], v1[1] + v2[1], v1[2] + v2[2]];
                
                // Draw first triangle
                vertexData.push(
                  0, 0, 0, 1,      // Origin
                  v1[0], v1[1], v1[2], 1,
                  v3[0], v3[1], v3[2], 1
                );
                
                // Draw second triangle
                vertexData.push(
                  0, 0, 0, 1,      // Origin
                  v2[0], v2[1], v2[2], 1,
                  v3[0], v3[1], v3[2], 1
                );
                
                // Same color for all vertices in triangles
                for (let i = 0; i < 6; i++) {
                  colorData.push(r, g, b, alpha * 0.7);
                }
              }
              break;
              
            case 3: // Trivector - draw a parallelepiped
              // Scale factor based on coefficient
              const boxScale = normCoef * 0.5;
              
              // Create vertices for cube/parallelepiped
              const boxVertices = [
                // Front face - 2 triangles
                -boxScale, -boxScale,  boxScale, 1,
                 boxScale, -boxScale,  boxScale, 1,
                 boxScale,  boxScale,  boxScale, 1,
                
                -boxScale, -boxScale,  boxScale, 1,
                 boxScale,  boxScale,  boxScale, 1,
                -boxScale,  boxScale,  boxScale, 1,
                
                // Back face - 2 triangles
                -boxScale, -boxScale, -boxScale, 1,
                 boxScale,  boxScale, -boxScale, 1,
                 boxScale, -boxScale, -boxScale, 1,
                
                -boxScale, -boxScale, -boxScale, 1,
                -boxScale,  boxScale, -boxScale, 1,
                 boxScale,  boxScale, -boxScale, 1,
                
                // Top face - 2 triangles
                -boxScale,  boxScale, -boxScale, 1,
                -boxScale,  boxScale,  boxScale, 1,
                 boxScale,  boxScale,  boxScale, 1,
                
                -boxScale,  boxScale, -boxScale, 1,
                 boxScale,  boxScale,  boxScale, 1,
                 boxScale,  boxScale, -boxScale, 1,
                
                // Bottom face - 2 triangles
                -boxScale, -boxScale, -boxScale, 1,
                 boxScale, -boxScale, -boxScale, 1,
                 boxScale, -boxScale,  boxScale, 1,
                
                -boxScale, -boxScale, -boxScale, 1,
                 boxScale, -boxScale,  boxScale, 1,
                -boxScale, -boxScale,  boxScale, 1,
                
                // Right face - 2 triangles
                 boxScale, -boxScale, -boxScale, 1,
                 boxScale,  boxScale, -boxScale, 1,
                 boxScale,  boxScale,  boxScale, 1,
                
                 boxScale, -boxScale, -boxScale, 1,
                 boxScale,  boxScale,  boxScale, 1,
                 boxScale, -boxScale,  boxScale, 1,
                
                // Left face - 2 triangles
                -boxScale, -boxScale, -boxScale, 1,
                -boxScale, -boxScale,  boxScale, 1,
                -boxScale,  boxScale,  boxScale, 1,
                
                -boxScale, -boxScale, -boxScale, 1,
                -boxScale,  boxScale,  boxScale, 1,
                -boxScale,  boxScale, -boxScale, 1,
              ];
              
              vertexData.push(...boxVertices);
              
              // Same color for all vertices in the cube
              for (let i = 0; i < boxVertices.length / 4; i++) {
                colorData.push(r, g, b, alpha * 0.5);
              }
              break;
              
            default:
              // Higher-dimensional components cannot be directly visualized
              break;
          }
        }
        
        // If we have vertex data, render it
        if (vertexData.length > 0) {
          // Create and bind vertex buffer
          const vertexBuffer = gl.createBuffer();
          gl.bindBuffer(gl.ARRAY_BUFFER, vertexBuffer);
          gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(vertexData), gl.STATIC_DRAW);
          
          // Create and bind color buffer
          const colorBuffer = gl.createBuffer();
          gl.bindBuffer(gl.ARRAY_BUFFER, colorBuffer);
          gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(colorData), gl.STATIC_DRAW);
          
          // Enable blending for transparent surfaces
          gl.enable(gl.BLEND);
          gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
          
          // Draw the multivector objects
          gl.bindBuffer(gl.ARRAY_BUFFER, vertexBuffer);
          gl.vertexAttribPointer(positionAttributeLocation, 4, gl.FLOAT, false, 0, 0);
          gl.enableVertexAttribArray(positionAttributeLocation);
          
          gl.bindBuffer(gl.ARRAY_BUFFER, colorBuffer);
          gl.vertexAttribPointer(colorAttributeLocation, 4, gl.FLOAT, false, 0, 0);
          gl.enableVertexAttribArray(colorAttributeLocation);
          
          // Determine the number of vertices
          const numVertices = vertexData.length / 4;
          gl.drawArrays(gl.TRIANGLES, 0, numVertices);
        }
      } catch (error) {
        Prime.Logger.error("Error rendering multivector in WebGL", {
          error: error.message,
          stack: error.stack,
          multivector: JSON.stringify(multivector)
        });
      }

      return gl;
    },

    _renderMultivectorSVG: function (multivector, options) {
      const width = options.dimensions[0] || 300;
      const height = options.dimensions[1] || 150;
      
      // Extract components from multivector
      const components = Prime.Clifford.extractComponents(multivector);
      
      // Only proceed if we have components to visualize
      if (components.length === 0) {
        return `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${width} ${height}" width="${width}" height="${height}">
          <text x="10" y="20">Empty Multivector</text>
        </svg>`;
      }
      
      // Set up SVG with header and stylesheet
      let svg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${width} ${height}" width="${width}" height="${height}">
        <defs>
          <style>
            .mv-axis { stroke: #aaa; stroke-width: 1; }
            .mv-vector { stroke-width: 2; }
            .mv-vector-label { font-size: 10px; fill: #000; }
            .mv-scalar { fill: #555; stroke: #000; }
            .mv-bivector { fill-opacity: 0.3; stroke-width: 1; }
            .mv-positive { stroke: #36c; fill: #36c; }
            .mv-negative { stroke: #f60; fill: #f60; }
            .mv-title { font-family: sans-serif; font-size: 12px; fill: #333; }
          </style>
        </defs>
        <rect width="${width}" height="${height}" fill="#f8f8f8" />
        <text x="10" y="16" class="mv-title">Multivector Visualization</text>`;
        
      // Center coordinates for visualization
      const centerX = width / 2;
      const centerY = height / 2;
      
      // Draw coordinate system
      svg += `<g transform="translate(${centerX}, ${centerY})">
        <line x1="-${width/2 - 20}" y1="0" x2="${width/2 - 20}" y2="0" class="mv-axis" />
        <line x1="0" y1="-${height/2 - 20}" x2="0" y2="${height/2 - 20}" class="mv-axis" />
        <text x="${width/2 - 15}" y="12" class="mv-vector-label">x</text>
        <text x="-10" y="-${height/2 - 10}" class="mv-vector-label">y</text>`;
      
      // Determine scale based on largest component
      const maxValue = Math.max(0.1, ...components.map(c => Math.abs(c.value)));
      const scale = (Math.min(width, height) * 0.4) / maxValue;
      
      // Process each component by grade
      for (const component of components) {
        const { grade, value: coefficient, basis } = component;
        
        // Only visualize components with non-zero coefficients
        if (Math.abs(coefficient) < 0.00001) {
          continue;
        }
        
        // Coefficient properties for visualization
        const absCoef = Math.abs(coefficient);
        const signClass = coefficient > 0 ? 'mv-positive' : 'mv-negative';
        
        // Process by grade
        switch (grade) {
          case 0: // Scalar - draw a circle at origin
            const radius = 5 + 10 * Math.min(absCoef, 1);
            svg += `<circle cx="0" cy="0" r="${radius}" class="mv-scalar ${signClass}" />`;
            svg += `<text x="8" y="-8" class="mv-vector-label">${coefficient.toFixed(2)}</text>`;
            break;
            
          case 1: // Vector - draw an arrow
            // Extract basis vector (e1, e2, e3, etc.)
            let x = 0, y = 0;
            const basisIdx = parseInt(basis.substring(1)) - 1;
            
            if (basisIdx === 0) { // e1 (x-axis)
              x = coefficient * scale;
            } else if (basisIdx === 1) { // e2 (y-axis)
              y = -coefficient * scale; // SVG y-axis is flipped
            } else {
              // For higher dimensions, position them at angles
              const angle = (basisIdx * Math.PI) / 4;
              x = Math.cos(angle) * coefficient * scale;
              y = -Math.sin(angle) * coefficient * scale;
            }
            
            // Calculate arrow properties
            const arrowLength = Math.sqrt(x*x + y*y);
            const arrowHead = 10; // Size of arrow head
            const angle = Math.atan2(y, x);
            
            // Draw vector
            svg += `<line x1="0" y1="0" x2="${x}" y2="${y}" class="mv-vector ${signClass}" />`;
            
            // Draw arrowhead
            svg += `<polygon points="
              ${x},${y},
              ${x - arrowHead * Math.cos(angle - Math.PI/6)},${y - arrowHead * Math.sin(angle - Math.PI/6)},
              ${x - arrowHead * Math.cos(angle + Math.PI/6)},${y - arrowHead * Math.sin(angle + Math.PI/6)}
            " class="${signClass}" />`;
            
            // Label
            svg += `<text x="${x + 5}" y="${y - 5}" class="mv-vector-label">${coefficient.toFixed(2)}${basis}</text>`;
            break;
            
          case 2: // Bivector - draw a shaded area
            // Extract plane information
            const planeIndices = basis.substring(1).split('').map(c => parseInt(c) - 1);
            
            // Only visualize standard planes
            if (planeIndices.length === 2 && planeIndices[0] >= 0 && planeIndices[0] < 3 &&
                planeIndices[1] >= 0 && planeIndices[1] < 3) {
              
              const scaledCoef = coefficient * scale * 0.7;
              
              // Handle different basis planes (e12, e23, e31)
              if (planeIndices[0] === 0 && planeIndices[1] === 1) { // e12 (xy-plane)
                const radius = Math.abs(scaledCoef);
                svg += `<ellipse cx="0" cy="0" rx="${radius}" ry="${radius}" class="mv-bivector ${signClass}" />`;
                
                // Add orientation arrow
                const arcFlag = coefficient > 0 ? 1 : 0;
                svg += `<path d="M ${radius * 0.7} 0 A ${radius * 0.7} ${radius * 0.7} 0 0 ${arcFlag} 0 ${-radius * 0.7}" 
                            class="${signClass}" fill="none" stroke-width="1.5" />`;
                            
                // Arrowhead on the arc
                const arrowX = coefficient > 0 ? 0 : 0;
                const arrowY = coefficient > 0 ? -radius * 0.7 : radius * 0.7;
                const arrowAngle = coefficient > 0 ? -Math.PI/2 : Math.PI/2;
                
                svg += `<polygon points="
                  ${arrowX},${arrowY},
                  ${arrowX + 5 * Math.cos(arrowAngle - Math.PI/6)},${arrowY + 5 * Math.sin(arrowAngle - Math.PI/6)},
                  ${arrowX + 5 * Math.cos(arrowAngle + Math.PI/6)},${arrowY + 5 * Math.sin(arrowAngle + Math.PI/6)}
                " class="${signClass}" />`;
              }
              else {
                // For other planes, draw a parallelogram
                let v1x = 0, v1y = 0, v2x = 0, v2y = 0;
                
                // Set up vectors for the plane
                if (planeIndices[0] === 0) v1x = scaledCoef; // e1
                else if (planeIndices[0] === 1) v1y = -scaledCoef; // e2
                
                if (planeIndices[1] === 0) v2x = scaledCoef; // e1
                else if (planeIndices[1] === 1) v2y = -scaledCoef; // e2
                
                // Calculate vertices of parallelogram
                const v3x = v1x + v2x;
                const v3y = v1y + v2y;
                
                // Draw filled parallelogram
                svg += `<polygon points="0,0 ${v1x},${v1y} ${v3x},${v3y} ${v2x},${v2y}" 
                                class="mv-bivector ${signClass}" />`;
              }
              
              // Label
              svg += `<text x="5" y="-${height/2 - 40 + planeIndices[0] * 15}" 
                            class="mv-vector-label">${coefficient.toFixed(2)}${basis}</text>`;
            }
            break;
            
          case 3: // Trivector - visualize as a sphere/cube
            const volScale = Math.abs(coefficient) * scale * 0.4;
            const volClass = coefficient > 0 ? 'mv-positive' : 'mv-negative';
            
            // Draw a shaded circle to represent volume
            svg += `<circle cx="0" cy="0" r="${volScale}" 
                            class="mv-bivector ${volClass}" 
                            style="fill-opacity: 0.2; stroke-dasharray: 3,2" />`;
            
            // Add text label for volume
            svg += `<text x="0" y="0" dy="4" text-anchor="middle" 
                          class="mv-vector-label">${coefficient.toFixed(2)}${basis}</text>`;
            break;
        }
      }
      
      // Close the group and SVG
      svg += `</g>
      
        <!-- Component Table -->
        <g transform="translate(10, ${height - 10 - (components.length * 15)})">
          <rect x="0" y="0" width="120" height="${components.length * 15 + 20}" 
                fill="white" fill-opacity="0.8" stroke="#ccc" />
          <text x="5" y="15" class="mv-title">Components:</text>`;
      
      // Add component list
      components.forEach((comp, idx) => {
        const y = 32 + idx * 15;
        svg += `<text x="10" y="${y}" class="mv-vector-label">${comp.value.toFixed(2)}${comp.basis}</text>`;
      });
      
      svg += `</g>
      </svg>`;
      
      return svg;
    },

    _renderArray: function (array, element, options) {
      if (options.mode === "table") {
        const table = document.createElement("table");
        const tbody = document.createElement("tbody");

        array.forEach((item, index) => {
          const row = document.createElement("tr");
          const indexCell = document.createElement("td");
          indexCell.textContent = index;
          row.appendChild(indexCell);

          const valueCell = document.createElement("td");
          valueCell.textContent = String(item);
          row.appendChild(valueCell);

          tbody.appendChild(row);
        });

        table.appendChild(tbody);
        element.innerHTML = "";
        element.appendChild(table);
      } else {
        element.textContent = JSON.stringify(array);
      }

      return element;
    },

    _renderArrayCanvas: function (array, ctx, options) {
      // Get canvas dimensions
      const width = ctx.canvas.width;
      const height = ctx.canvas.height;
      
      // Clear canvas
      ctx.clearRect(0, 0, width, height);
      
      // Draw title
      ctx.fillStyle = "#333";
      ctx.font = "12px sans-serif";
      ctx.textAlign = "left";
      ctx.textBaseline = "top";
      ctx.fillText("Array Visualization", 10, 10);
      
      // Set up visualization area
      const margin = 40;
      const chartWidth = width - 2 * margin;
      const chartHeight = height - 2 * margin;
      const maxItems = Math.min(array.length, 50); // Limit display to 50 items
      
      // Check if array contains numbers
      const isNumeric = array.every(item => typeof item === 'number' || (typeof item === 'string' && !isNaN(item)));
      
      if (isNumeric) {
        // Convert all items to numbers
        const numericArray = array.slice(0, maxItems).map(item => Number(item));
        
        // Find the min and max values
        const minValue = Math.min(0, ...numericArray);
        const maxValue = Math.max(0, ...numericArray);
        const valueRange = maxValue - minValue;
        
        // Calculate bar properties
        const barWidth = chartWidth / numericArray.length;
        const barSpacing = Math.max(1, barWidth * 0.2);
        const adjustedBarWidth = barWidth - barSpacing;
        
        // Draw coordinate system
        ctx.strokeStyle = "#ccc";
        ctx.lineWidth = 1;
        
        // X-axis
        ctx.beginPath();
        ctx.moveTo(margin, height - margin);
        ctx.lineTo(width - margin, height - margin);
        ctx.stroke();
        
        // Y-axis
        ctx.beginPath();
        ctx.moveTo(margin, margin);
        ctx.lineTo(margin, height - margin);
        ctx.stroke();
        
        // Draw zero line if needed
        if (minValue < 0) {
          const zeroY = height - margin - (0 - minValue) / valueRange * chartHeight;
          ctx.beginPath();
          ctx.moveTo(margin, zeroY);
          ctx.lineTo(width - margin, zeroY);
          ctx.stroke();
        }
        
        // Draw bars
        numericArray.forEach((value, index) => {
          const x = margin + index * barWidth + barSpacing / 2;
          
          // Calculate bar height and position
          let barHeight, y;
          if (value >= 0) {
            barHeight = (value / valueRange) * chartHeight;
            y = height - margin - barHeight;
          } else {
            barHeight = (Math.abs(value) / valueRange) * chartHeight;
            y = height - margin;
          }
          
          // Choose color based on value
          if (value >= 0) {
            ctx.fillStyle = "#36c"; // Blue for positive
          } else {
            ctx.fillStyle = "#f60"; // Orange for negative
          }
          
          // Draw the bar
          ctx.fillRect(x, y, adjustedBarWidth, barHeight);
          
          // Draw value label for larger bars
          if (Math.abs(barHeight) > 20) {
            ctx.fillStyle = "#fff";
            ctx.font = "10px sans-serif";
            ctx.textAlign = "center";
            ctx.textBaseline = "middle";
            ctx.fillText(value.toFixed(1), x + adjustedBarWidth / 2, y + barHeight / 2);
          }
          
          // Draw index labels for every nth item depending on array size
          const labelInterval = Math.ceil(numericArray.length / 10);
          if (index % labelInterval === 0) {
            ctx.fillStyle = "#333";
            ctx.font = "10px sans-serif";
            ctx.textAlign = "center";
            ctx.textBaseline = "top";
            ctx.fillText(index.toString(), x + adjustedBarWidth / 2, height - margin + 5);
          }
        });
      } else {
        // For non-numeric arrays, display as text with styling
        const fontSize = Math.min(14, Math.max(8, Math.floor(250 / array.length)));
        ctx.font = `${fontSize}px monospace`;
        ctx.textAlign = "left";
        ctx.textBaseline = "top";
        
        // Draw array structure
        ctx.fillStyle = "#333";
        ctx.fillText("[", margin, margin);
        
        // Calculate item positions
        const items = array.slice(0, maxItems).map(item => {
          // Format different types
          if (typeof item === 'object' && item !== null) {
            return '{ obj }';
          } else if (typeof item === 'string') {
            return `"${item.length > 20 ? item.substring(0, 17) + '...' : item}"`;
          } else {
            return String(item);
          }
        });
        
        // Join with commas and draw
        const itemsText = items.join(", ");
        ctx.fillText(itemsText, margin + 10, margin);
        ctx.fillText("]", margin + 20 + ctx.measureText(itemsText).width, margin);
        
        // Add length indicator
        ctx.fillStyle = "#666";
        ctx.fillText(`Length: ${array.length}`, margin, margin + fontSize + 10);
        
        // If array is truncated, indicate it
        if (array.length > maxItems) {
          ctx.fillStyle = "#900";
          ctx.fillText(`(${array.length - maxItems} more items not shown)`, margin, margin + (fontSize + 10) * 2);
        }
      }
      
      return ctx;
    },

    _renderArraySVG: function (array, options) {
      const width = options.dimensions[0] || 300;
      const height = options.dimensions[1] || 150;
      const margin = 40;
      const chartWidth = width - 2 * margin;
      const chartHeight = height - 2 * margin;
      const maxItems = Math.min(array.length, 50); // Limit display to 50 items
      
      // Determine if array is numeric
      const isNumeric = array.every(item => typeof item === 'number' || (typeof item === 'string' && !isNaN(item)));
      
      // Start SVG with styles
      let svg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${width} ${height}" width="${width}" height="${height}">
        <defs>
          <style>
            .array-title { font-family: sans-serif; font-size: 12px; fill: #333; }
            .array-axis { stroke: #ccc; stroke-width: 1; }
            .array-bar-positive { fill: #36c; }
            .array-bar-negative { fill: #f60; }
            .array-label { font-family: sans-serif; font-size: 10px; fill: #333; }
            .array-value { font-family: sans-serif; font-size: 10px; fill: #fff; text-anchor: middle; }
            .array-text { font-family: monospace; font-size: 12px; fill: #333; }
            .array-info { font-family: sans-serif; font-size: 11px; fill: #666; }
            .array-warning { font-family: sans-serif; font-size: 11px; fill: #900; }
          </style>
        </defs>
        <rect width="${width}" height="${height}" fill="#f8f8f8" />
        <text x="10" y="20" class="array-title">Array Visualization</text>`;
      
      if (isNumeric && array.length > 0) {
        // Convert values to numbers and limit to maxItems
        const numericArray = array.slice(0, maxItems).map(item => Number(item));
        
        // Find the min and max values
        const minValue = Math.min(0, ...numericArray);
        const maxValue = Math.max(0, ...numericArray);
        const valueRange = maxValue - minValue || 1; // Avoid division by zero
        
        // Calculate bar properties
        const barWidth = chartWidth / numericArray.length;
        const barSpacing = Math.max(1, barWidth * 0.2);
        const adjustedBarWidth = barWidth - barSpacing;
        
        // Draw coordinate system
        svg += `<g transform="translate(0, 0)">
          <!-- X-axis -->
          <line x1="${margin}" y1="${height - margin}" x2="${width - margin}" y2="${height - margin}" class="array-axis" />
          
          <!-- Y-axis -->
          <line x1="${margin}" y1="${margin}" x2="${margin}" y2="${height - margin}" class="array-axis" />`;
        
        // Draw zero line if needed
        if (minValue < 0) {
          const zeroY = height - margin - (0 - minValue) / valueRange * chartHeight;
          svg += `<line x1="${margin}" y1="${zeroY}" x2="${width - margin}" y2="${zeroY}" class="array-axis" stroke-dasharray="4 2" />`;
        }
        
        // Draw bars
        numericArray.forEach((value, index) => {
          const x = margin + index * barWidth + barSpacing / 2;
          
          // Calculate bar height and position
          let barHeight, y;
          if (value >= 0) {
            barHeight = (value / valueRange) * chartHeight;
            y = height - margin - barHeight;
          } else {
            barHeight = (Math.abs(value) / valueRange) * chartHeight;
            y = height - margin;
          }
          
          // Ensure minimum visible height
          barHeight = Math.max(barHeight, 1);
          
          // Choose bar class based on value
          const barClass = value >= 0 ? 'array-bar-positive' : 'array-bar-negative';
          
          // Draw the bar
          svg += `<rect x="${x}" y="${y}" width="${adjustedBarWidth}" height="${barHeight}" class="${barClass}" />`;
          
          // Draw value label for larger bars
          if (Math.abs(barHeight) > 20) {
            svg += `<text x="${x + adjustedBarWidth / 2}" y="${y + barHeight / 2}" dy="0.35em" class="array-value">${value.toFixed(1)}</text>`;
          }
          
          // Draw index labels for every nth item
          const labelInterval = Math.ceil(numericArray.length / 10);
          if (index % labelInterval === 0) {
            svg += `<text x="${x + adjustedBarWidth / 2}" y="${height - margin + 15}" class="array-label" text-anchor="middle">${index}</text>`;
          }
        });
        
        // Add min/max labels
        svg += `<text x="${margin}" y="${margin - 5}" class="array-label" text-anchor="start">Max: ${maxValue}</text>`;
        if (minValue < 0) {
          svg += `<text x="${margin}" y="${height - margin + 25}" class="array-label" text-anchor="start">Min: ${minValue}</text>`;
        }
        
        svg += `</g>`;
      } else {
        // For non-numeric arrays, display as text
        svg += `<g transform="translate(${margin}, ${margin + 20})">`;
        
        // Format array items
        const items = array.slice(0, maxItems).map(item => {
          // Format different types
          if (typeof item === 'object' && item !== null) {
            return '{ obj }';
          } else if (typeof item === 'string') {
            return `"${item.length > 20 ? item.substring(0, 17) + '...' : item}"`;
          } else {
            return String(item);
          }
        });
        
        // Draw array brackets and items
        svg += `<text x="0" y="0" class="array-text">[</text>`;
        
        if (items.length > 0) {
          const formattedText = items.join(", ");
          svg += `<text x="15" y="0" class="array-text">${formattedText}</text>`;
          
          // Close bracket - need to estimate text width
          const estimatedWidth = 15 + formattedText.length * 7; // Rough monospace width estimate
          svg += `<text x="${estimatedWidth + 5}" y="0" class="array-text">]</text>`;
        } else {
          svg += `<text x="15" y="0" class="array-text">]</text>`;
        }
        
        // Add array info
        svg += `<text x="0" y="25" class="array-info">Length: ${array.length}</text>`;
        
        // If array is truncated, indicate it
        if (array.length > maxItems) {
          svg += `<text x="0" y="45" class="array-warning">(${array.length - maxItems} more items not shown)</text>`;
        }
        
        svg += `</g>`;
      }
      
      svg += `</svg>`;
      return svg;
    },

    _renderTransformationCanvas: function (transformation, ctx, options) {
      // Get canvas dimensions
      const width = ctx.canvas.width;
      const height = ctx.canvas.height;
      
      // Clear canvas
      ctx.clearRect(0, 0, width, height);
      
      // Draw title
      ctx.fillStyle = "#333";
      ctx.font = "12px sans-serif";
      ctx.textAlign = "left";
      ctx.textBaseline = "top";
      ctx.fillText("Transformation Visualization", 10, 10);
      
      // Set up grid parameters
      const gridSize = Math.min(width, height) * 0.8;
      const cellSize = gridSize / 10;
      const centerX = width / 2;
      const centerY = height / 2;
      
      // Check if transformation has a matrix representation
      if (transformation.matrix || (transformation.getMatrix && typeof transformation.getMatrix === 'function')) {
        const matrix = transformation.matrix || transformation.getMatrix();
        
        // Draw the original coordinate grid (before transformation)
        ctx.strokeStyle = "#ccc";
        ctx.lineWidth = 0.5;
        
        // Draw grid lines
        for (let i = -5; i <= 5; i++) {
          // Vertical lines
          ctx.beginPath();
          ctx.moveTo(centerX + i * cellSize, centerY - gridSize / 2);
          ctx.lineTo(centerX + i * cellSize, centerY + gridSize / 2);
          ctx.stroke();
          
          // Horizontal lines
          ctx.beginPath();
          ctx.moveTo(centerX - gridSize / 2, centerY + i * cellSize);
          ctx.lineTo(centerX + gridSize / 2, centerY + i * cellSize);
          ctx.stroke();
        }
        
        // Draw coordinate axes
        ctx.strokeStyle = "#666";
        ctx.lineWidth = 1;
        
        // X-axis
        ctx.beginPath();
        ctx.moveTo(centerX - gridSize / 2, centerY);
        ctx.lineTo(centerX + gridSize / 2, centerY);
        ctx.stroke();
        
        // Y-axis
        ctx.beginPath();
        ctx.moveTo(centerX, centerY - gridSize / 2);
        ctx.lineTo(centerX, centerY + gridSize / 2);
        ctx.stroke();
        
        // Draw transformed coordinate system
        ctx.strokeStyle = "#36c";
        ctx.lineWidth = 2;
        
        // Determine the transformation type and dimensions
        const is2D = matrix.length === 4 || matrix.length === 9; // 2x2 or 3x3 matrix
        const is3D = matrix.length === 16; // 4x4 matrix
        
        if (is2D) {
          // Get the transformed basis vectors
          let e1x, e1y, e2x, e2y;
          
          if (matrix.length === 4) {
            // 2x2 matrix
            e1x = matrix[0];
            e1y = matrix[1];
            e2x = matrix[2];
            e2y = matrix[3];
          } else {
            // 3x3 matrix (homogeneous coordinates)
            e1x = matrix[0];
            e1y = matrix[1];
            e2x = matrix[3];
            e2y = matrix[4];
          }
          
          // Scale the vectors for visualization
          const scale = cellSize * 2;
          e1x *= scale;
          e1y *= scale;
          e2x *= scale;
          e2y *= scale;
          
          // Draw transformed x-axis (e1)
          ctx.beginPath();
          ctx.moveTo(centerX, centerY);
          ctx.lineTo(centerX + e1x, centerY - e1y); // Flip y-coordinate for canvas
          ctx.stroke();
          
          // Draw transformed y-axis (e2)
          ctx.strokeStyle = "#f60";
          ctx.beginPath();
          ctx.moveTo(centerX, centerY);
          ctx.lineTo(centerX + e2x, centerY - e2y); // Flip y-coordinate for canvas
          ctx.stroke();
          
          // Draw arrows on the transformed axes
          const drawArrow = (x, y, angle) => {
            const arrowSize = 10;
            ctx.beginPath();
            ctx.moveTo(x, y);
            ctx.lineTo(
              x - arrowSize * Math.cos(angle - Math.PI / 6),
              y - arrowSize * Math.sin(angle - Math.PI / 6)
            );
            ctx.lineTo(
              x - arrowSize * Math.cos(angle + Math.PI / 6),
              y - arrowSize * Math.sin(angle + Math.PI / 6)
            );
            ctx.closePath();
            ctx.fill();
          };
          
          // Draw arrow for e1 (x-axis)
          ctx.fillStyle = "#36c";
          const e1Angle = Math.atan2(-e1y, e1x); // Flip y-coordinate for canvas
          drawArrow(centerX + e1x, centerY - e1y, e1Angle);
          
          // Draw arrow for e2 (y-axis)
          ctx.fillStyle = "#f60";
          const e2Angle = Math.atan2(-e2y, e2x); // Flip y-coordinate for canvas
          drawArrow(centerX + e2x, centerY - e2y, e2Angle);
          
          // Draw transformed grid (optional, can be visually complex)
          if (options.showTransformedGrid) {
            ctx.strokeStyle = "rgba(54, 108, 204, 0.3)";
            ctx.lineWidth = 0.5;
            
            // Draw a few grid lines to show the transformation
            for (let i = -2; i <= 2; i++) {
              // Vertical transformed grid lines
              ctx.beginPath();
              ctx.moveTo(centerX + i * e1x, centerY - i * e1y);
              ctx.lineTo(centerX + i * e1x + 5 * e2x, centerY - i * e1y - 5 * e2y);
              ctx.stroke();
              
              // Horizontal transformed grid lines
              ctx.beginPath();
              ctx.moveTo(centerX + i * e2x, centerY - i * e2y);
              ctx.lineTo(centerX + i * e2x + 5 * e1x, centerY - i * e2y - 5 * e1y);
              ctx.stroke();
            }
          }
          
          // Draw matrix values
          ctx.fillStyle = "#333";
          ctx.font = "12px monospace";
          ctx.textAlign = "left";
          ctx.textBaseline = "top";
          
          const formatValue = (val) => val.toFixed(2).replace(/\.00$/, '');
          
          if (matrix.length === 4) {
            ctx.fillText(`[${formatValue(matrix[0])}, ${formatValue(matrix[2])}]`, 10, height - 60);
            ctx.fillText(`[${formatValue(matrix[1])}, ${formatValue(matrix[3])}]`, 10, height - 40);
          } else {
            ctx.fillText(`[${formatValue(matrix[0])}, ${formatValue(matrix[3])}, ${formatValue(matrix[6])}]`, 10, height - 80);
            ctx.fillText(`[${formatValue(matrix[1])}, ${formatValue(matrix[4])}, ${formatValue(matrix[7])}]`, 10, height - 60);
            ctx.fillText(`[${formatValue(matrix[2])}, ${formatValue(matrix[5])}, ${formatValue(matrix[8])}]`, 10, height - 40);
          }
        } else if (is3D) {
          // For 3D transformations, we'll create a simple projection
          // Get the transformed basis vectors
          const e1x = matrix[0];
          const e1y = matrix[1];
          const e1z = matrix[2];
          
          const e2x = matrix[4];
          const e2y = matrix[5];
          const e2z = matrix[6];
          
          const e3x = matrix[8];
          const e3y = matrix[9];
          const e3z = matrix[10];
          
          // Scale the vectors for visualization
          const scale = cellSize * 1.5;
          
          // Simple perspective projection
          const project = (x, y, z) => {
            // Move z further away for better perspective
            const projZ = z + 4;
            // Perspective divide
            const factor = 2 / projZ;
            return {
              x: centerX + x * scale * factor,
              y: centerY - y * scale * factor // Flip y-coordinate for canvas
            };
          };
          
          // Draw the transformed coordinate axes
          const origin = project(0, 0, 0);
          
          // Draw x-axis (red)
          const e1Proj = project(e1x, e1y, e1z);
          ctx.strokeStyle = "#c33";
          ctx.beginPath();
          ctx.moveTo(origin.x, origin.y);
          ctx.lineTo(e1Proj.x, e1Proj.y);
          ctx.stroke();
          
          // Draw y-axis (green)
          const e2Proj = project(e2x, e2y, e2z);
          ctx.strokeStyle = "#3c3";
          ctx.beginPath();
          ctx.moveTo(origin.x, origin.y);
          ctx.lineTo(e2Proj.x, e2Proj.y);
          ctx.stroke();
          
          // Draw z-axis (blue)
          const e3Proj = project(e3x, e3y, e3z);
          ctx.strokeStyle = "#33c";
          ctx.beginPath();
          ctx.moveTo(origin.x, origin.y);
          ctx.lineTo(e3Proj.x, e3Proj.y);
          ctx.stroke();
          
          // Label the axes
          ctx.font = "12px sans-serif";
          ctx.fillStyle = "#c33";
          ctx.fillText("x", e1Proj.x + 5, e1Proj.y);
          ctx.fillStyle = "#3c3";
          ctx.fillText("y", e2Proj.x + 5, e2Proj.y);
          ctx.fillStyle = "#33c";
          ctx.fillText("z", e3Proj.x + 5, e3Proj.y);
          
          // Draw matrix values in a compact form
          ctx.fillStyle = "#333";
          ctx.font = "10px monospace";
          ctx.textAlign = "left";
          ctx.textBaseline = "top";
          
          const formatValue = (val) => val.toFixed(1).replace(/\.0$/, '');
          
          ctx.fillText("Matrix:", 10, height - 100);
          ctx.fillText(`[${formatValue(matrix[0])}, ${formatValue(matrix[4])}, ${formatValue(matrix[8])}, ${formatValue(matrix[12])}]`, 10, height - 85);
          ctx.fillText(`[${formatValue(matrix[1])}, ${formatValue(matrix[5])}, ${formatValue(matrix[9])}, ${formatValue(matrix[13])}]`, 10, height - 70);
          ctx.fillText(`[${formatValue(matrix[2])}, ${formatValue(matrix[6])}, ${formatValue(matrix[10])}, ${formatValue(matrix[14])}]`, 10, height - 55);
          ctx.fillText(`[${formatValue(matrix[3])}, ${formatValue(matrix[7])}, ${formatValue(matrix[11])}, ${formatValue(matrix[15])}]`, 10, height - 40);
        }
        
        // Draw transformation type
        ctx.fillStyle = "#333";
        ctx.font = "12px sans-serif";
        ctx.textAlign = "left";
        ctx.textBaseline = "top";
        
        // Determine transformation type
        let transformationType = "Linear Transformation";
        
        if (transformation.type) {
          transformationType = transformation.type;
        } else if (is2D) {
          // For 2D transformations, try to identify common types
          const det = is2D && matrix.length === 4 ? 
            matrix[0] * matrix[3] - matrix[1] * matrix[2] : 
            matrix[0] * matrix[4] - matrix[1] * matrix[3];
            
          if (Math.abs(det - 1) < 0.001) {
            if (matrix[0] === 1 && matrix[1] === 0 && matrix[2] === 0 && matrix[3] === 1) {
              transformationType = "Identity";
            } else if (matrix[0] * matrix[3] - matrix[1] * matrix[2] > 0) {
              transformationType = "Rotation/Reflection";
            }
          } else if (det === 0) {
            transformationType = "Singular (Projection/Collapse)";
          } else {
            transformationType = `Scaling (det=${det.toFixed(2)})`;
          }
        }
        
        ctx.fillText(`Type: ${transformationType}`, 10, height - 20);
      } else {
        // No matrix representation available, just show the JSON
        ctx.fillStyle = "#333";
        ctx.font = "12px monospace";
        ctx.textAlign = "left";
        ctx.textBaseline = "top";
        ctx.fillText(`Transformation: ${JSON.stringify(transformation)}`, 10, 40);
      }
      
      return ctx;
    },

    _renderObject: function (object, element, options) {
      if (options.mode === "table") {
        const table = document.createElement("table");
        const tbody = document.createElement("tbody");

        Object.entries(object).forEach(([key, value]) => {
          const row = document.createElement("tr");
          const keyCell = document.createElement("td");
          keyCell.textContent = key;
          row.appendChild(keyCell);

          const valueCell = document.createElement("td");
          valueCell.textContent = String(value);
          row.appendChild(valueCell);

          tbody.appendChild(row);
        });

        table.appendChild(tbody);
        element.innerHTML = "";
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
  Prime.EventBus.publish("module:loaded", { name: "component-rendering" });
})(Prime);

// CommonJS export (no ES module export to avoid circular dependency)
if (typeof module !== "undefined" && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== "undefined") {
  window.Prime = Prime;
}
