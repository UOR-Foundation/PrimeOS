/**
 * PrimeOS JavaScript Library - Components Part 2
 * Rendering, performance, documentation, and analytical tools
 * Version 1.0.0
 */

// Import extended Prime
import { Prime } from './components-1.js';

(function(Prime) {
  'use strict';
  
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
      theme: 'light'
    },
    
    /**
     * Render an object to a DOM element
     * @param {*} object - Object to render
     * @param {Element} element - DOM element
     * @param {Object} options - Rendering options
     * @returns {Element} Updated element
     */
    toDOM: function(object, element, options = {}) {
      if (!element) {
        throw new Prime.ValidationError('DOM element is required');
      }
      
      // Merge options with defaults
      const mergedOptions = { ...this.defaultOptions, ...options };
      
      // If object is a component, use its renderer if available
      if (object && object.meta && object.invariant && object.invariant.render) {
        return object.invariant.render(element, mergedOptions);
      }
      
      // Check if we have a specific renderer for this object type
      const objectType = this._getObjectType(object);
      const renderer = this.renderers.get(`dom:${objectType}`);
      
      if (renderer) {
        return renderer(object, element, mergedOptions);
      }
      
      // Handle different object types
      if (Prime.Clifford && Prime.Clifford.isMultivector && Prime.Clifford.isMultivector(object)) {
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
    toCanvas: function(object, ctx, options = {}) {
      if (!ctx) {
        throw new Prime.ValidationError('Canvas context is required');
      }
      
      // Merge options with defaults
      const mergedOptions = { ...this.defaultOptions, ...options };
      
      // Set up dimensions
      const width = mergedOptions.dimensions[0] || ctx.canvas.width;
      const height = mergedOptions.dimensions[1] || ctx.canvas.height;
      
      // Clear canvas
      ctx.clearRect(0, 0, width, height);
      
      // If object is a component, use its renderer if available
      if (object && object.meta && object.invariant && object.invariant.renderCanvas) {
        return object.invariant.renderCanvas(ctx, mergedOptions);
      }
      
      // Check if we have a specific renderer for this object type
      const objectType = this._getObjectType(object);
      const renderer = this.renderers.get(`canvas:${objectType}`);
      
      if (renderer) {
        return renderer(object, ctx, mergedOptions);
      }
      
      // Handle different object types
      if (Prime.Clifford && Prime.Clifford.isMultivector && Prime.Clifford.isMultivector(object)) {
        return this._renderMultivectorCanvas(object, ctx, mergedOptions);
      }
      
      if (Prime.Utils.isArray(object)) {
        return this._renderArrayCanvas(object, ctx, mergedOptions);
      }
      
      if (Prime.Lie && Prime.Lie.isGroupElement && Prime.Lie.isGroupElement(object)) {
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
    toWebGL: function(object, gl, options = {}) {
      if (!gl) {
        throw new Prime.ValidationError('WebGL context is required');
      }
      
      // Merge options with defaults
      const mergedOptions = { ...this.defaultOptions, ...options };
      
      // Clear the context
      gl.clearColor(0.0, 0.0, 0.0, 1.0);
      gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
      
      // If object is a component, use its renderer if available
      if (object && object.meta && object.invariant && object.invariant.renderWebGL) {
        return object.invariant.renderWebGL(gl, mergedOptions);
      }
      
      // Check if we have a specific renderer for this object type
      const objectType = this._getObjectType(object);
      const renderer = this.renderers.get(`webgl:${objectType}`);
      
      if (renderer) {
        return renderer(object, gl, mergedOptions);
      }
      
      // Handle different object types
      if (Prime.Clifford && Prime.Clifford.isMultivector && Prime.Clifford.isMultivector(object)) {
        return this._renderMultivectorWebGL(object, gl, mergedOptions);
      }
      
      // Fallback - do nothing and return the context
      Prime.Logger.warn('No WebGL renderer available for object', {
        objectType
      });
      
      return gl;
    },
    
    /**
     * Render to SVG
     * @param {*} object - Object to render
     * @param {Object} options - Rendering options
     * @returns {string} SVG markup
     */
    toSVG: function(object, options = {}) {
      // Merge options with defaults
      const mergedOptions = { ...this.defaultOptions, ...options };
      
      // If object is a component, use its renderer if available
      if (object && object.meta && object.invariant && object.invariant.renderSVG) {
        return object.invariant.renderSVG(mergedOptions);
      }
      
      // Check if we have a specific renderer for this object type
      const objectType = this._getObjectType(object);
      const renderer = this.renderers.get(`svg:${objectType}`);
      
      if (renderer) {
        return renderer(object, mergedOptions);
      }
      
      // Handle different object types
      if (Prime.Clifford && Prime.Clifford.isMultivector && Prime.Clifford.isMultivector(object)) {
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
    registerRenderer: function(targetType, objectType, rendererFn) {
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
     * Create animation frames
     * @param {Function} renderFn - Render function
     * @param {Object} options - Animation options
     * @returns {Object} Animation controller
     */
    animate: function(renderFn, options = {}) {
      if (!Prime.Utils.isFunction(renderFn)) {
        throw new Prime.ValidationError('Render function is required');
      }
      
      const mergedOptions = {
        duration: options.duration || 1000,
        fps: options.fps || 60,
        easing: options.easing || (t => t),
        onComplete: options.onComplete || (() => {}),
        onFrame: options.onFrame || (() => {})
      };
      
      let startTime = null;
      let animationId = null;
      let isRunning = false;
      
      const controller = {
        start: function() {
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
        
        stop: function() {
          if (!isRunning) return;
          
          if (animationId) {
            cancelAnimationFrame(animationId);
            animationId = null;
          }
          
          isRunning = false;
          return this;
        },
        
        isRunning: function() {
          return isRunning;
        },
        
        restart: function() {
          this.stop();
          this.start();
          return this;
        }
      };
      
      return controller;
    },
    
    /**
     * Get object type for rendering
     * @private
     * @param {*} object - Object to render
     * @returns {string} Object type
     */
    _getObjectType: function(object) {
      if (object === null) return 'null';
      if (object === undefined) return 'undefined';
      
      // Check for components
      if (object && object.meta && object.variant && object.lifecycle) {
        return `component:${object.meta.type || 'generic'}`;
      }
      
      // Check for specialized types
      if (Prime.Clifford && Prime.Clifford.isMultivector && Prime.Clifford.isMultivector(object)) {
        return 'multivector';
      }
      
      if (Prime.Lie && Prime.Lie.isGroupElement && Prime.Lie.isGroupElement(object)) {
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
      if (object instanceof HTMLElement) return 'htmlElement';
      if (object instanceof SVGElement) return 'svgElement';
      
      // Primitive types
      if (typeof object === 'string') return 'string';
      if (typeof object === 'number') return 'number';
      if (typeof object === 'boolean') return 'boolean';
      if (typeof object === 'function') return 'function';
      if (typeof object === 'object') return 'object';
      
      return typeof object;
    },
    
    /**
     * Render a multivector to DOM
     * @private
     * @param {Object} multivector - Multivector to render
     * @param {Element} element - DOM element
     * @param {Object} options - Rendering options
     * @returns {Element} Updated element
     */
    _renderMultivector: function(multivector, element, options) {
      const mode = options.mode || '2d';
      
      element.innerHTML = '';
      
      if (mode === '2d') {
        // Create canvas for 2D representation
        const canvas = document.createElement('canvas');
        canvas.width = options.dimensions[0] || 300;
        canvas.height = options.dimensions[1] || 300;
        element.appendChild(canvas);
        
        const ctx = canvas.getContext('2d');
        this._renderMultivectorCanvas(multivector, ctx, options);
      } else if (mode === '3d') {
        // Create canvas for WebGL representation
        const canvas = document.createElement('canvas');
        canvas.width = options.dimensions[0] || 300;
        canvas.height = options.dimensions[1] || 300;
        element.appendChild(canvas);
        
        try {
          const gl = canvas.getContext('webgl') || canvas.getContext('experimental-webgl');
          
          if (gl) {
            this._renderMultivectorWebGL(multivector, gl, options);
          } else {
            // Fallback to 2D if WebGL not available
            const ctx = canvas.getContext('2d');
            this._renderMultivectorCanvas(multivector, ctx, options);
          }
        } catch (error) {
          // Fallback to 2D if WebGL fails
          const ctx = canvas.getContext('2d');
          this._renderMultivectorCanvas(multivector, ctx, options);
        }
      } else if (mode === 'text') {
        // Text representation
        const pre = document.createElement('pre');
        pre.textContent = multivector.toString();
        element.appendChild(pre);
      } else if (mode === 'math') {
        // Mathematical representation
        const mathDiv = document.createElement('div');
        mathDiv.innerHTML = this._generateMathML(multivector);
        element.appendChild(mathDiv);
      }
      
      // Add interactive controls if requested
      if (options.interactive) {
        const controls = document.createElement('div');
        controls.className = 'controls';
        
        // Add controls for different grades
        const grades = Object.keys(multivector.components).sort();
        
        if (grades.length > 0) {
          const gradeSelector = document.createElement('select');
          gradeSelector.addEventListener('change', function() {
            const selectedGrade = this.value;
            const gradeComponent = multivector.grade(parseInt(selectedGrade));
            
            // Re-render with only the selected grade
            if (mode === '2d') {
              const ctx = element.querySelector('canvas').getContext('2d');
              ctx.clearRect(0, 0, ctx.canvas.width, ctx.canvas.height);
              render._renderMultivectorCanvas(gradeComponent, ctx, options);
            }
          });
          
          // Add options for each grade
          const allOption = document.createElement('option');
          allOption.value = 'all';
          allOption.textContent = 'All grades';
          gradeSelector.appendChild(allOption);
          
          for (const grade of grades) {
            const option = document.createElement('option');
            option.value = grade;
            option.textContent = `Grade ${grade}`;
            gradeSelector.appendChild(option);
          }
          
          controls.appendChild(gradeSelector);
        }
        
        element.appendChild(controls);
      }
      
      return element;
    },
    
    /**
     * Render a multivector to canvas
     * @private
     * @param {Object} multivector - Multivector to render
     * @param {CanvasRenderingContext2D} ctx - Canvas context
     * @param {Object} options - Rendering options
     * @returns {CanvasRenderingContext2D} Updated context
     */
    _renderMultivectorCanvas: function(multivector, ctx, options) {
      const width = ctx.canvas.width;
      const height = ctx.canvas.height;
      const center = { x: width / 2, y: height / 2 };
      const scale = Math.min(width, height) / 4;
      
      // Clear canvas
      ctx.clearRect(0, 0, width, height);
      
      // Draw coordinate axes
      ctx.strokeStyle = '#ccc';
      ctx.beginPath();
      ctx.moveTo(0, center.y);
      ctx.lineTo(width, center.y);
      ctx.moveTo(center.x, 0);
      ctx.lineTo(center.x, height);
      ctx.stroke();
      
      // Draw vector part if present
      if (multivector.components[1]) {
        const vector = multivector.toArray();
        
        if (vector.length >= 2) {
          ctx.strokeStyle = '#f00';
          ctx.beginPath();
          ctx.moveTo(center.x, center.y);
          ctx.lineTo(
            center.x + vector[0] * scale,
            center.y - vector[1] * scale
          );
          ctx.stroke();
          
          // Draw arrowhead
          const angle = Math.atan2(-vector[1], vector[0]);
          ctx.beginPath();
          ctx.moveTo(
            center.x + vector[0] * scale,
            center.y - vector[1] * scale
          );
          ctx.lineTo(
            center.x + vector[0] * scale - 10 * Math.cos(angle - Math.PI / 6),
            center.y - vector[1] * scale + 10 * Math.sin(angle - Math.PI / 6)
          );
          ctx.moveTo(
            center.x + vector[0] * scale,
            center.y - vector[1] * scale
          );
          ctx.lineTo(
            center.x + vector[0] * scale - 10 * Math.cos(angle + Math.PI / 6),
            center.y - vector[1] * scale + 10 * Math.sin(angle + Math.PI / 6)
          );
          ctx.stroke();
          
          // Label coordinates
          ctx.fillStyle = '#000';
          ctx.font = '12px sans-serif';
          ctx.fillText(
            `(${vector[0].toFixed(2)}, ${vector[1].toFixed(2)})`,
            center.x + vector[0] * scale + 5,
            center.y - vector[1] * scale - 5
          );
        }
      }
      
      // Draw bivector part if present
      if (multivector.components[2]) {
        ctx.strokeStyle = '#00f';
        ctx.fillStyle = 'rgba(0, 0, 255, 0.2)';
        
        // Simple representation for now - a parallelogram for each bivector component
        for (const basis in multivector.components[2]) {
          const value = multivector.components[2][basis];
          const magnitude = Math.min(Math.abs(value), 3) * scale / 3;
          
          if (basis === 'e1e2') {
            // Draw e1∧e2 bivector as a parallelogram in the x-y plane
            ctx.beginPath();
            ctx.moveTo(center.x, center.y);
            ctx.lineTo(center.x + magnitude, center.y);
            ctx.lineTo(center.x + magnitude, center.y - magnitude);
            ctx.lineTo(center.x, center.y - magnitude);
            ctx.closePath();
            ctx.fill();
            ctx.stroke();
          } else {
            // For other bivectors, draw a simple indicator
            const basisElements = basis.match(/e\d+/g);
            if (basisElements && basisElements.length === 2) {
              const idx1 = parseInt(basisElements[0].substring(1)) - 1;
              const idx2 = parseInt(basisElements[1].substring(1)) - 1;
              
              // Represent as a small circle with label
              ctx.beginPath();
              ctx.arc(center.x + 30 * idx1, center.y - 30 * idx2, magnitude, 0, 2 * Math.PI);
              ctx.fill();
              ctx.stroke();
              
              // Label
              ctx.fillStyle = '#000';
              ctx.font = '12px sans-serif';
              ctx.fillText(
                `${basis}: ${value.toFixed(2)}`,
                center.x + 30 * idx1 + magnitude + 5,
                center.y - 30 * idx2
              );
            }
          }
        }
      }
      
      // Draw scalar part if present
      if (multivector.components[0]) {
        const scalar = multivector.components[0]["1"] || 0;
        
        if (scalar !== 0) {
          ctx.fillStyle = '#000';
          ctx.font = '14px sans-serif';
          ctx.fillText(
            `Scalar: ${scalar.toFixed(2)}`,
            10, 20
          );
        }
      }
      
      return ctx;
    },
    
    /**
     * Render a multivector to WebGL
     * @private
     * @param {Object} multivector - Multivector to render
     * @param {WebGLRenderingContext} gl - WebGL context
     * @param {Object} options - Rendering options
     * @returns {WebGLRenderingContext} Updated context
     */
    _renderMultivectorWebGL: function(multivector, gl, options) {
      // This is a placeholder for a proper WebGL implementation
      // In a full implementation, this would create 3D visualization of the multivector
      
      // Clear the context
      gl.clearColor(0.9, 0.9, 0.9, 1.0);
      gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
      
      return gl;
    },
    
    /**
     * Generate MathML representation of a multivector
     * @private
     * @param {Object} multivector - Multivector to represent
     * @returns {string} MathML markup
     */
    _generateMathML: function(multivector) {
      // This is a placeholder for a proper MathML implementation
      // In a full implementation, this would generate proper MathML
      
      return `<math xmlns="http://www.w3.org/1998/Math/MathML">
        <mrow>
          <mi>${multivector.toString()}</mi>
        </mrow>
      </math>`;
    },
    
    /**
     * Render a multivector to SVG
     * @private
     * @param {Object} multivector - Multivector to render
     * @param {Object} options - Rendering options
     * @returns {string} SVG markup
     */
    _renderMultivectorSVG: function(multivector, options) {
      const width = options.dimensions[0] || 300;
      const height = options.dimensions[1] || 300;
      const centerX = width / 2;
      const centerY = height / 2;
      const scale = Math.min(width, height) / 4;
      
      let svg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${width} ${height}" width="${width}" height="${height}">
        <!-- Coordinate axes -->
        <line x1="0" y1="${centerY}" x2="${width}" y2="${centerY}" stroke="#ccc" />
        <line x1="${centerX}" y1="0" x2="${centerX}" y2="${height}" stroke="#ccc" />`;
      
      // Draw vector part if present
      if (multivector.components[1]) {
        const vector = multivector.toArray();
        
        if (vector.length >= 2) {
          const endX = centerX + vector[0] * scale;
          const endY = centerY - vector[1] * scale;
          
          // Vector line
          svg += `
          <!-- Vector part -->
          <line x1="${centerX}" y1="${centerY}" x2="${endX}" y2="${endY}" stroke="#f00" stroke-width="2" />`;
          
          // Arrowhead
          const angle = Math.atan2(-vector[1], vector[0]);
          const arrowX1 = endX - 10 * Math.cos(angle - Math.PI / 6);
          const arrowY1 = endY + 10 * Math.sin(angle - Math.PI / 6);
          const arrowX2 = endX - 10 * Math.cos(angle + Math.PI / 6);
          const arrowY2 = endY + 10 * Math.sin(angle + Math.PI / 6);
          
          svg += `
          <line x1="${endX}" y1="${endY}" x2="${arrowX1}" y2="${arrowY1}" stroke="#f00" stroke-width="2" />
          <line x1="${endX}" y1="${endY}" x2="${arrowX2}" y2="${arrowY2}" stroke="#f00" stroke-width="2" />`;
          
          // Label
          svg += `
          <text x="${endX + 5}" y="${endY - 5}" font-family="sans-serif" font-size="12">(${vector[0].toFixed(2)}, ${vector[1].toFixed(2)})</text>`;
        }
      }
      
      // Draw bivector part if present
      if (multivector.components[2]) {
        svg += `
        <!-- Bivector part -->`;
        
        // Simple representation for each bivector component
        for (const basis in multivector.components[2]) {
          const value = multivector.components[2][basis];
          const magnitude = Math.min(Math.abs(value), 3) * scale / 3;
          
          if (basis === 'e1e2') {
            // Draw e1∧e2 bivector as a parallelogram in the x-y plane
            svg += `
            <polygon points="${centerX},${centerY} ${centerX + magnitude},${centerY} ${centerX + magnitude},${centerY - magnitude} ${centerX},${centerY - magnitude}"
              fill="rgba(0, 0, 255, 0.2)" stroke="#00f" />`;
          } else {
            // For other bivectors, draw a simple indicator
            const basisElements = basis.match(/e\d+/g);
            if (basisElements && basisElements.length === 2) {
              const idx1 = parseInt(basisElements[0].substring(1)) - 1;
              const idx2 = parseInt(basisElements[1].substring(1)) - 1;
              
              const circleX = centerX + 30 * idx1;
              const circleY = centerY - 30 * idx2;
              
              svg += `
              <circle cx="${circleX}" cy="${circleY}" r="${magnitude}" fill="rgba(0, 0, 255, 0.2)" stroke="#00f" />
              <text x="${circleX + magnitude + 5}" y="${circleY}" font-family="sans-serif" font-size="12">${basis}: ${value.toFixed(2)}</text>`;
            }
          }
        }
      }
      
      // Draw scalar part if present
      if (multivector.components[0]) {
        const scalar = multivector.components[0]["1"] || 0;
        
        if (scalar !== 0) {
          svg += `
          <!-- Scalar part -->
          <text x="10" y="20" font-family="sans-serif" font-size="14">Scalar: ${scalar.toFixed(2)}</text>`;
        }
      }
      
      svg += `
      </svg>`;
      
      return svg;
    },
    
    /**
     * Render an array to DOM
     * @private
     * @param {Array} array - Array to render
     * @param {Element} element - DOM element
     * @param {Object} options - Rendering options
     * @returns {Element} Updated element
     */
    _renderArray: function(array, element, options) {
      element.innerHTML = '';
      
      const mode = options.mode || 'default';
      
      if (mode === 'table') {
        // Render as a table
        const table = document.createElement('table');
        table.style.borderCollapse = 'collapse';
        
        // Add header if array has objects
        if (array.length > 0 && Prime.Utils.isObject(array[0])) {
          const thead = document.createElement('thead');
          const headerRow = document.createElement('tr');
          
          // Get all unique keys from the objects
          const keys = array.reduce((allKeys, obj) => {
            Object.keys(obj).forEach(key => {
              if (!allKeys.includes(key)) {
                allKeys.push(key);
              }
            });
            return allKeys;
          }, []);
          
          // Create header cells
          keys.forEach(key => {
            const th = document.createElement('th');
            th.textContent = key;
            th.style.border = '1px solid #ccc';
            th.style.padding = '5px 10px';
            headerRow.appendChild(th);
          });
          
          thead.appendChild(headerRow);
          table.appendChild(thead);
          
          // Add data rows
          const tbody = document.createElement('tbody');
          
          array.forEach(obj => {
            const row = document.createElement('tr');
            
            keys.forEach(key => {
              const td = document.createElement('td');
              td.textContent = obj[key] !== undefined ? String(obj[key]) : '';
              td.style.border = '1px solid #ccc';
              td.style.padding = '5px 10px';
              row.appendChild(td);
            });
            
            tbody.appendChild(row);
          });
          
          table.appendChild(tbody);
        } else {
          // Simple array - render as single column
          const tbody = document.createElement('tbody');
          
          array.forEach((item, index) => {
            const row = document.createElement('tr');
            
            // Index cell
            const indexCell = document.createElement('td');
            indexCell.textContent = String(index);
            indexCell.style.border = '1px solid #ccc';
            indexCell.style.padding = '5px 10px';
            indexCell.style.backgroundColor = '#f0f0f0';
            row.appendChild(indexCell);
            
            // Value cell
            const valueCell = document.createElement('td');
            valueCell.textContent = String(item);
            valueCell.style.border = '1px solid #ccc';
            valueCell.style.padding = '5px 10px';
            row.appendChild(valueCell);
            
            tbody.appendChild(row);
          });
          
          table.appendChild(tbody);
        }
        
        element.appendChild(table);
      } else if (mode === 'list') {
        // Render as a list
        const ul = document.createElement('ul');
        
        array.forEach(item => {
          const li = document.createElement('li');
          li.textContent = String(item);
          ul.appendChild(li);
        });
        
        element.appendChild(ul);
      } else if (mode === 'plot' && array.every(item => Prime.Utils.isNumber(item))) {
        // Render as a simple line plot
        const canvas = document.createElement('canvas');
        canvas.width = options.dimensions[0] || 300;
        canvas.height = options.dimensions[1] || 150;
        element.appendChild(canvas);
        
        const ctx = canvas.getContext('2d');
        this._renderArrayCanvas(array, ctx, { ...options, mode: 'plot' });
      } else {
        // Default rendering - simply display as text
        const pre = document.createElement('pre');
        pre.textContent = JSON.stringify(array, null, 2);
        element.appendChild(pre);
      }
      
      return element;
    },
    
    /**
     * Render an array to canvas
     * @private
     * @param {Array} array - Array to render
     * @param {CanvasRenderingContext2D} ctx - Canvas context
     * @param {Object} options - Rendering options
     * @returns {CanvasRenderingContext2D} Updated context
     */
    _renderArrayCanvas: function(array, ctx, options) {
      const width = ctx.canvas.width;
      const height = ctx.canvas.height;
      
      // Clear canvas
      ctx.clearRect(0, 0, width, height);
      
      const mode = options.mode || 'default';
      
      if (mode === 'plot' && array.every(item => Prime.Utils.isNumber(item))) {
        // Render as a line plot
        const padding = 20;
        const plotWidth = width - 2 * padding;
        const plotHeight = height - 2 * padding;
        
        // Find min and max values
        const minValue = Math.min(...array);
        const maxValue = Math.max(...array);
        const valueRange = maxValue - minValue;
        
        // Draw axes
        ctx.strokeStyle = '#000';
        ctx.beginPath();
        ctx.moveTo(padding, padding);
        ctx.lineTo(padding, height - padding);
        ctx.lineTo(width - padding, height - padding);
        ctx.stroke();
        
        // Draw data line
        ctx.strokeStyle = '#00f';
        ctx.beginPath();
        
        array.forEach((value, index) => {
          const x = padding + (index / (array.length - 1)) * plotWidth;
          const normalizedValue = valueRange === 0 ? 0.5 : (value - minValue) / valueRange;
          const y = height - padding - normalizedValue * plotHeight;
          
          if (index === 0) {
            ctx.moveTo(x, y);
          } else {
            ctx.lineTo(x, y);
          }
        });
        
        ctx.stroke();
        
        // Draw axis labels
        ctx.fillStyle = '#000';
        ctx.font = '12px sans-serif';
        ctx.fillText('0', padding - 15, height - padding + 15);
        ctx.fillText(String(array.length - 1), width - padding, height - padding + 15);
        ctx.fillText(String(maxValue.toFixed(2)), padding - 40, padding);
        ctx.fillText(String(minValue.toFixed(2)), padding - 40, height - padding);
      } else if (mode === 'bar' && array.every(item => Prime.Utils.isNumber(item))) {
        // Render as a bar chart
        const padding = 20;
        const plotWidth = width - 2 * padding;
        const plotHeight = height - 2 * padding;
        const barWidth = plotWidth / array.length * 0.8;
        const barSpacing = plotWidth / array.length * 0.2;
        
        // Find min and max values
        const minValue = Math.min(0, ...array);
        const maxValue = Math.max(...array);
        const valueRange = maxValue - minValue;
        
        // Draw axes
        ctx.strokeStyle = '#000';
        ctx.beginPath();
        ctx.moveTo(padding, padding);
        ctx.lineTo(padding, height - padding);
        ctx.lineTo(width - padding, height - padding);
        ctx.stroke();
        
        // Draw bars
        ctx.fillStyle = '#00f';
        
        array.forEach((value, index) => {
          const normalizedValue = valueRange === 0 ? 0 : (value - minValue) / valueRange;
          const barHeight = normalizedValue * plotHeight;
          
          const x = padding + (index / array.length) * plotWidth + barSpacing / 2;
          const y = height - padding - barHeight;
          
          ctx.fillRect(x, y, barWidth, barHeight);
        });
        
        // Draw axis labels
        ctx.fillStyle = '#000';
        ctx.font = '12px sans-serif';
        ctx.fillText('0', padding - 15, height - padding + 15);
        ctx.fillText(String(array.length - 1), width - padding, height - padding + 15);
        ctx.fillText(String(maxValue.toFixed(2)), padding - 40, padding);
        ctx.fillText(String(minValue.toFixed(2)), padding - 40, height - padding);
      } else {
        // Default rendering - just display array as text
        ctx.fillStyle = '#000';
        ctx.font = '12px monospace';
        ctx.fillText(JSON.stringify(array), 10, 20);
      }
      
      return ctx;
    },
    
    /**
     * Render an array to SVG
     * @private
     * @param {Array} array - Array to render
     * @param {Object} options - Rendering options
     * @returns {string} SVG markup
     */
    _renderArraySVG: function(array, options) {
      const width = options.dimensions[0] || 300;
      const height = options.dimensions[1] || 150;
      
      const mode = options.mode || 'default';
      
      if (mode === 'plot' && array.every(item => Prime.Utils.isNumber(item))) {
        // Render as a line plot
        const padding = 20;
        const plotWidth = width - 2 * padding;
        const plotHeight = height - 2 * padding;
        
        // Find min and max values
        const minValue = Math.min(...array);
        const maxValue = Math.max(...array);
        const valueRange = maxValue - minValue;
        
        // Generate SVG
        let svg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${width} ${height}" width="${width}" height="${height}">
          <!-- Axes -->
          <line x1="${padding}" y1="${padding}" x2="${padding}" y2="${height - padding}" stroke="#000" />
          <line x1="${padding}" y1="${height - padding}" x2="${width - padding}" y2="${height - padding}" stroke="#000" />`;
        
        // Generate data line points
        let points = '';
        
        array.forEach((value, index) => {
          const x = padding + (index / (array.length - 1)) * plotWidth;
          const normalizedValue = valueRange === 0 ? 0.5 : (value - minValue) / valueRange;
          const y = height - padding - normalizedValue * plotHeight;
          
          points += `${x},${y} `;
        });
        
        // Add data line
        svg += `
          <!-- Data line -->
          <polyline points="${points.trim()}" fill="none" stroke="#00f" stroke-width="2" />`;
        
        // Add axis labels
        svg += `
          <!-- Axis labels -->
          <text x="${padding - 15}" y="${height - padding + 15}" font-family="sans-serif" font-size="12">0</text>
          <text x="${width - padding}" y="${height - padding + 15}" font-family="sans-serif" font-size="12">${array.length - 1}</text>
          <text x="${padding - 40}" y="${padding}" font-family="sans-serif" font-size="12">${maxValue.toFixed(2)}</text>
          <text x="${padding - 40}" y="${height - padding}" font-family="sans-serif" font-size="12">${minValue.toFixed(2)}</text>
        </svg>`;
        
        return svg;
      } else if (mode === 'bar' && array.every(item => Prime.Utils.isNumber(item))) {
        // Render as a bar chart
        const padding = 20;
        const plotWidth = width - 2 * padding;
        const plotHeight = height - 2 * padding;
        const barWidth = plotWidth / array.length * 0.8;
        const barSpacing = plotWidth / array.length * 0.2;
        
        // Find min and max values
        const minValue = Math.min(0, ...array);
        const maxValue = Math.max(...array);
        const valueRange = maxValue - minValue;
        
        // Generate SVG
        let svg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${width} ${height}" width="${width}" height="${height}">
          <!-- Axes -->
          <line x1="${padding}" y1="${padding}" x2="${padding}" y2="${height - padding}" stroke="#000" />
          <line x1="${padding}" y1="${height - padding}" x2="${width - padding}" y2="${height - padding}" stroke="#000" />`;
        
        // Add bars
        svg += `
          <!-- Bars -->`;
        
        array.forEach((value, index) => {
          const normalizedValue = valueRange === 0 ? 0 : (value - minValue) / valueRange;
          const barHeight = normalizedValue * plotHeight;
          
          const x = padding + (index / array.length) * plotWidth + barSpacing / 2;
          const y = height - padding - barHeight;
          
          svg += `
          <rect x="${x}" y="${y}" width="${barWidth}" height="${barHeight}" fill="#00f" />`;
        });
        
        // Add axis labels
        svg += `
          <!-- Axis labels -->
          <text x="${padding - 15}" y="${height - padding + 15}" font-family="sans-serif" font-size="12">0</text>
          <text x="${width - padding}" y="${height - padding + 15}" font-family="sans-serif" font-size="12">${array.length - 1}</text>
          <text x="${padding - 40}" y="${padding}" font-family="sans-serif" font-size="12">${maxValue.toFixed(2)}</text>
          <text x="${padding - 40}" y="${height - padding}" font-family="sans-serif" font-size="12">${minValue.toFixed(2)}</text>
        </svg>`;
        
        return svg;
      } else {
        // Default rendering
        return `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${width} ${height}" width="${width}" height="${height}">
          <rect width="${width}" height="${height}" fill="#f0f0f0" />
          <text x="10" y="20" font-family="monospace" font-size="12">${JSON.stringify(array)}</text>
        </svg>`;
      }
    },
    
    /**
     * Render a transformation to canvas
     * @private
     * @param {Object} transformation - Transformation to render
     * @param {CanvasRenderingContext2D} ctx - Canvas context
     * @param {Object} options - Rendering options
     * @returns {CanvasRenderingContext2D} Updated context
     */
    _renderTransformationCanvas: function(transformation, ctx, options) {
      const width = ctx.canvas.width;
      const height = ctx.canvas.height;
      const center = { x: width / 2, y: height / 2 };
      
      // Clear canvas
      ctx.clearRect(0, 0, width, height);
      
      // Draw grid before transformation
      this._drawGrid(ctx, center, width, height, '#ccc');
      
      // Draw transformed grid
      this._drawTransformedGrid(ctx, center, width, height, transformation, '#00f');
      
      // Draw transformation matrix
      this._drawMatrix(ctx, transformation.matrix, 10, 20);
      
      return ctx;
    },
    
    /**
     * Draw a grid on canvas
     * @private
     * @param {CanvasRenderingContext2D} ctx - Canvas context
     * @param {Object} center - Grid center
     * @param {number} width - Canvas width
     * @param {number} height - Canvas height
     * @param {string} color - Grid color
     */
    _drawGrid: function(ctx, center, width, height, color) {
      const spacing = 40;
      const halfWidth = width / 2;
      const halfHeight = height / 2;
      
      ctx.strokeStyle = color;
      ctx.lineWidth = 1;
      
      // Draw vertical gridlines
      for (let x = center.x % spacing; x < width; x += spacing) {
        ctx.beginPath();
        ctx.moveTo(x, 0);
        ctx.lineTo(x, height);
        ctx.stroke();
      }
      
      // Draw horizontal gridlines
      for (let y = center.y % spacing; y < height; y += spacing) {
        ctx.beginPath();
        ctx.moveTo(0, y);
        ctx.lineTo(width, y);
        ctx.stroke();
      }
      
      // Draw axes
      ctx.strokeStyle = '#000';
      ctx.lineWidth = 2;
      
      ctx.beginPath();
      ctx.moveTo(center.x, 0);
      ctx.lineTo(center.x, height);
      ctx.stroke();
      
      ctx.beginPath();
      ctx.moveTo(0, center.y);
      ctx.lineTo(width, center.y);
      ctx.stroke();
    },
    
    /**
     * Draw a transformed grid on canvas
     * @private
     * @param {CanvasRenderingContext2D} ctx - Canvas context
     * @param {Object} center - Grid center
     * @param {number} width - Canvas width
     * @param {number} height - Canvas height
     * @param {Object} transformation - Transformation to apply
     * @param {string} color - Grid color
     */
    _drawTransformedGrid: function(ctx, center, width, height, transformation, color) {
      const spacing = 40;
      const halfWidth = width / 2;
      const halfHeight = height / 2;
      
      ctx.strokeStyle = color;
      ctx.lineWidth = 1;
      
      // Draw transformed vertical gridlines
      for (let x = -halfWidth; x <= halfWidth; x += spacing) {
        ctx.beginPath();
        
        for (let y = -halfHeight; y <= halfHeight; y += 10) {
          const point = [x, y, 0];
          const transformed = transformation.apply(point);
          
          const tx = center.x + transformed[0];
          const ty = center.y - transformed[1];
          
          if (y === -halfHeight) {
            ctx.moveTo(tx, ty);
          } else {
            ctx.lineTo(tx, ty);
          }
        }
        
        ctx.stroke();
      }
      
      // Draw transformed horizontal gridlines
      for (let y = -halfHeight; y <= halfHeight; y += spacing) {
        ctx.beginPath();
        
        for (let x = -halfWidth; x <= halfWidth; x += 10) {
          const point = [x, y, 0];
          const transformed = transformation.apply(point);
          
          const tx = center.x + transformed[0];
          const ty = center.y - transformed[1];
          
          if (x === -halfWidth) {
            ctx.moveTo(tx, ty);
          } else {
            ctx.lineTo(tx, ty);
          }
        }
        
        ctx.stroke();
      }
    },
    
    /**
     * Draw a matrix on canvas
     * @private
     * @param {CanvasRenderingContext2D} ctx - Canvas context
     * @param {Array} matrix - Matrix to draw
     * @param {number} x - X position
     * @param {number} y - Y position
     */
    _drawMatrix: function(ctx, matrix, x, y) {
      ctx.fillStyle = '#000';
      ctx.font = '14px monospace';
      
      for (let i = 0; i < matrix.length; i++) {
        let row = '';
        
        for (let j = 0; j < matrix[i].length; j++) {
          const value = matrix[i][j].toFixed(2);
          row += value.padStart(7, ' ');
        }
        
        if (i === 0) {
          row = '⎡' + row + '⎤';
        } else if (i === matrix.length - 1) {
          row = '⎣' + row + '⎦';
        } else {
          row = '⎢' + row + '⎥';
        }
        
        ctx.fillText(row, x, y + i * 20);
      }
    },
    
    /**
     * Render an object to DOM
     * @private
     * @param {Object} object - Object to render
     * @param {Element} element - DOM element
     * @param {Object} options - Rendering options
     * @returns {Element} Updated element
     */
    _renderObject: function(object, element, options) {
      element.innerHTML = '';
      
      const mode = options.mode || 'default';
      
      if (mode === 'table') {
        // Render as a table
        const table = document.createElement('table');
        table.style.borderCollapse = 'collapse';
        
        const tbody = document.createElement('tbody');
        
        Object.entries(object).forEach(([key, value]) => {
          const row = document.createElement('tr');
          
          // Key cell
          const keyCell = document.createElement('td');
          keyCell.textContent = key;
          keyCell.style.border = '1px solid #ccc';
          keyCell.style.padding = '5px 10px';
          keyCell.style.fontWeight = 'bold';
          keyCell.style.backgroundColor = '#f0f0f0';
          row.appendChild(keyCell);
          
          // Value cell
          const valueCell = document.createElement('td');
          valueCell.textContent = String(value);
          valueCell.style.border = '1px solid #ccc';
          valueCell.style.padding = '5px 10px';
          row.appendChild(valueCell);
          
          tbody.appendChild(row);
        });
        
        table.appendChild(tbody);
        element.appendChild(table);
      } else if (mode === 'list') {
        // Render as a definition list
        const dl = document.createElement('dl');
        
        Object.entries(object).forEach(([key, value]) => {
          const dt = document.createElement('dt');
          dt.textContent = key;
          dt.style.fontWeight = 'bold';
          dl.appendChild(dt);
          
          const dd = document.createElement('dd');
          dd.textContent = String(value);
          dd.style.marginBottom = '10px';
          dl.appendChild(dd);
        });
        
        element.appendChild(dl);
      } else {
        // Default rendering - simply display as JSON
        const pre = document.createElement('pre');
        pre.textContent = JSON.stringify(object, null, 2);
        element.appendChild(pre);
      }
      
      return element;
    }
  };

  /**
   * Performance optimization and benchmarking
   */
  const performance = {
    /**
     * Current configuration
     */
    config: {
      useWebAssembly: false,
      useWorkers: false,
      memoizationLimit: 1000,
      precision: 'double',
      optimizationLevel: 'balanced',
      preferredRenderer: 'auto',
      logPerformance: false
    },
    
    /**
     * Cache for performance measurements
     */
    _cache: new Map(),
    
    /**
     * Performance history
     */
    _history: [],
    
    /**
     * Configure performance options
     * @param {Object} options - Performance options
     * @returns {Object} Updated configuration
     */
    configure: function(options) {
      if (!options) {
        return this.config;
      }
      
      this.config = { ...this.config, ...options };
      
      // Apply configuration changes
      if (options.memoizationLimit !== undefined) {
        this._pruneCache();
      }
      
      return this.config;
    },
    
    /**
     * Run a benchmark
     * @param {Function} operation - Operation to benchmark
     * @param {Object} options - Benchmark options
     * @returns {Object} Benchmark results
     */
    benchmark: async function(operation, options = {}) {
      if (!Prime.Utils.isFunction(operation)) {
        throw new Prime.ValidationError('Operation must be a function');
      }
      
      const iterations = options.iterations || 100;
      const warmup = options.warmup || 10;
      const name = options.name || operation.name || 'anonymous';
      const args = options.args || [];
      
      // Track all timings
      const timings = [];
      
      // Run warmup iterations
      for (let i = 0; i < warmup; i++) {
        try {
          await operation(...args);
        } catch (error) {
          Prime.Logger.warn(`Error during warmup iteration ${i}`, {
            error: error.message,
            stack: error.stack
          });
        }
      }
      
      // Run benchmark iterations
      for (let i = 0; i < iterations; i++) {
        try {
          const start = performance.now ? performance.now() : Date.now();
          await operation(...args);
          const end = performance.now ? performance.now() : Date.now();
          
          timings.push(end - start);
        } catch (error) {
          Prime.Logger.warn(`Error during benchmark iteration ${i}`, {
            error: error.message,
            stack: error.stack
          });
          
          // Add a high timing value to indicate error
          timings.push(Number.MAX_SAFE_INTEGER);
        }
      }
      
      // Calculate statistics
      const validTimings = timings.filter(t => t !== Number.MAX_SAFE_INTEGER);
      const sum = validTimings.reduce((a, b) => a + b, 0);
      const mean = sum / validTimings.length;
      
      const squaredDifferences = validTimings.map(t => Math.pow(t - mean, 2));
      const variance = squaredDifferences.reduce((a, b) => a + b, 0) / validTimings.length;
      const stdDev = Math.sqrt(variance);
      
      // Calculate percentiles
      const sortedTimings = [...validTimings].sort((a, b) => a - b);
      const median = this._calculatePercentile(sortedTimings, 50);
      const p95 = this._calculatePercentile(sortedTimings, 95);
      const p99 = this._calculatePercentile(sortedTimings, 99);
      
      // Create result object
      const result = {
        name,
        iterations: validTimings.length,
        failedIterations: timings.length - validTimings.length,
        mean,
        median,
        stdDev,
        min: Math.min(...validTimings),
        max: Math.max(...validTimings),
        p95,
        p99,
        total: sum,
        timings: options.keepTimings ? validTimings : undefined,
        timestamp: Date.now()
      };
      
      // Save to history
      this._history.push({
        name,
        mean,
        median,
        stdDev,
        timestamp: Date.now()
      });
      
      // Prune history if needed
      if (this._history.length > 1000) {
        this._history = this._history.slice(-1000);
      }
      
      // Log results if configured
      if (this.config.logPerformance) {
        Prime.Logger.info(`Benchmark results for ${name}`, result);
      }
      
      return result;
    },
    
    /**
     * Run comparative benchmark of multiple operations
     * @param {Array} operations - Operations to benchmark
     * @param {Object} options - Benchmark options
     * @returns {Object} Comparison results
     */
    compare: async function(operations, options = {}) {
      if (!Prime.Utils.isArray(operations)) {
        throw new Prime.ValidationError('Operations must be an array');
      }
      
      // Add names if not provided
      const namedOperations = operations.map((op, index) => {
        if (Prime.Utils.isFunction(op)) {
          return {
            name: op.name || `Operation ${index + 1}`,
            fn: op
          };
        }
        return op;
      });
      
      // Run benchmarks for each operation
      const results = [];
      
      for (const op of namedOperations) {
        const result = await this.benchmark(op.fn, {
          ...options,
          name: op.name,
          args: op.args
        });
        
        results.push(result);
      }
      
      // Calculate relative performance
      const sorted = [...results].sort((a, b) => a.mean - b.mean);
      const fastest = sorted[0];
      
      // Add relative speed
      const withRelative = results.map(result => ({
        ...result,
        relative: result.mean / fastest.mean
      }));
      
      return {
        results: withRelative,
        fastest: fastest.name,
        slowest: sorted[sorted.length - 1].name,
        timestamp: Date.now()
      };
    },
    
    /**
     * Create a function optimized for performance
     * @param {Function} fn - Function to optimize
     * @param {Object} options - Optimization options
     * @returns {Function} Optimized function
     */
    optimize: function(fn, options = {}) {
      if (!Prime.Utils.isFunction(fn)) {
        throw new Prime.ValidationError('Function is required');
      }
      
      const mergedOptions = {
        memoize: options.memoize !== false,
        memoizeLimit: options.memoizeLimit || this.config.memoizationLimit,
        async: options.async !== false && fn.constructor.name === 'AsyncFunction',
        monitor: options.monitor !== false,
        validateInput: options.validateInput,
        validateOutput: options.validateOutput
      };
      
      // Start with the original function
      let optimized = fn;
      
      // Add input validation if provided
      if (mergedOptions.validateInput) {
        const originalFn = optimized;
        optimized = function(...args) {
          if (!mergedOptions.validateInput(...args)) {
            throw new Prime.ValidationError('Input validation failed');
          }
          return originalFn.apply(this, args);
        };
      }
      
      // Add output validation if provided
      if (mergedOptions.validateOutput) {
        const originalFn = optimized;
        optimized = function(...args) {
          const result = originalFn.apply(this, args);
          
          if (!mergedOptions.validateOutput(result, ...args)) {
            throw new Prime.ValidationError('Output validation failed');
          }
          
          return result;
        };
      }
      
      // Add memoization if requested
      if (mergedOptions.memoize) {
        optimized = Prime.Utils.memoize(optimized, {
          maxSize: mergedOptions.memoizeLimit
        });
      }
      
      // Add performance monitoring if requested
      if (mergedOptions.monitor) {
        const name = fn.name || 'anonymous';
        const monitoredFn = optimized;
        
        if (mergedOptions.async) {
          optimized = async function(...args) {
            const start = performance.now ? performance.now() : Date.now();
            
            try {
              const result = await monitoredFn.apply(this, args);
              
              const end = performance.now ? performance.now() : Date.now();
              performance._recordExecution(name, end - start);
              
              return result;
            } catch (error) {
              const end = performance.now ? performance.now() : Date.now();
              performance._recordExecution(name, end - start, error);
              
              throw error;
            }
          };
        } else {
          optimized = function(...args) {
            const start = performance.now ? performance.now() : Date.now();
            
            try {
              const result = monitoredFn.apply(this, args);
              
              const end = performance.now ? performance.now() : Date.now();
              performance._recordExecution(name, end - start);
              
              return result;
            } catch (error) {
              const end = performance.now ? performance.now() : Date.now();
              performance._recordExecution(name, end - start, error);
              
              throw error;
            }
          };
        }
      }
      
      return optimized;
    },
    
    /**
     * Get performance statistics
     * @param {string} [name] - Function name filter
     * @returns {Object} Performance statistics
     */
    getStatistics: function(name) {
      if (name) {
        // Filter history by name
        const filtered = this._history.filter(entry => entry.name === name);
        
        if (filtered.length === 0) {
          return {
            name,
            calls: 0,
            totalTime: 0,
            averageTime: 0
          };
        }
        
        // Calculate statistics
        const totalTime = filtered.reduce((sum, entry) => sum + entry.mean, 0);
        
        return {
          name,
          calls: filtered.length,
          totalTime,
          averageTime: totalTime / filtered.length,
          history: filtered
        };
      }
      
      // Group by name
      const stats = {};
      
      for (const entry of this._history) {
        if (!stats[entry.name]) {
          stats[entry.name] = {
            calls: 0,
            totalTime: 0,
            history: []
          };
        }
        
        stats[entry.name].calls++;
        stats[entry.name].totalTime += entry.mean;
        stats[entry.name].history.push(entry);
      }
      
      // Calculate averages
      for (const name in stats) {
        stats[name].averageTime = stats[name].totalTime / stats[name].calls;
      }
      
      return stats;
    },
    
    /**
     * Clear performance history
     * @returns {number} Number of entries cleared
     */
    clearHistory: function() {
      const count = this._history.length;
      this._history = [];
      return count;
    },
    
    /**
     * Check if WebAssembly is supported
     * @returns {boolean} True if WebAssembly is supported
     */
    isWebAssemblySupported: function() {
      return typeof WebAssembly === 'object' && 
             typeof WebAssembly.compile === 'function';
    },
    
    /**
     * Check if Web Workers are supported
     * @returns {boolean} True if Web Workers are supported
     */
    isWorkersSupported: function() {
      return typeof Worker === 'function';
    },
    
    /**
     * Prune the memoization cache
     * @private
     */
    _pruneCache: function() {
      // Implementation would depend on the memoization system
      // This is a placeholder for now
    },
    
    /**
     * Record a function execution
     * @private
     * @param {string} name - Function name
     * @param {number} time - Execution time
     * @param {Error} [error] - Error if execution failed
     */
    _recordExecution: function(name, time, error) {
      const key = `${name}:${Date.now()}`;
      
      this._cache.set(key, {
        name,
        time,
        error: error ? error.message : undefined,
        timestamp: Date.now()
      });
      
      // Prune cache if needed
      if (this._cache.size > this.config.memoizationLimit) {
        // Remove oldest entries
        const entries = Array.from(this._cache.entries());
        const oldest = entries.slice(0, entries.length - this.config.memoizationLimit);
        
        for (const [key] of oldest) {
          this._cache.delete(key);
        }
      }
    },
    
    /**
     * Calculate a percentile from sorted values
     * @private
     * @param {Array} sorted - Sorted array of values
     * @param {number} percentile - Percentile to calculate
     * @returns {number} Percentile value
     */
    _calculatePercentile: function(sorted, percentile) {
      if (sorted.length === 0) return 0;
      
      const index = Math.ceil((percentile / 100) * sorted.length) - 1;
      return sorted[Math.min(index, sorted.length - 1)];
    }
  };
  
  /**
   * Framework structure documentation generator
   */
  const generateDocumentation = function(options = {}) {
    const docOptions = {
      format: options.format || 'markdown',
      includePrivate: options.includePrivate === true,
      includeInternal: options.includeInternal === true,
      depth: options.depth || Infinity
    };
    
    /**
     * Generate documentation for Prime object
     * @returns {string} Generated documentation
     */
    const generatePrimeDocumentation = function() {
      if (docOptions.format === 'markdown') {
        return generateMarkdownDocumentation();
      } else if (docOptions.format === 'html') {
        return generateHtmlDocumentation();
      } else if (docOptions.format === 'json') {
        return generateJsonDocumentation();
      }
      
      throw new Prime.ValidationError(`Unsupported documentation format: ${docOptions.format}`);
    };
    
    /**
     * Generate Markdown documentation
     * @returns {string} Markdown documentation
     */
    const generateMarkdownDocumentation = function() {
      let md = `# PrimeOS JavaScript Library Documentation\n\n`;
      
      // Add version
      md += `**Version:** ${Prime.version}\n\n`;
      
      // Add overview
      md += `## Overview\n\n`;
      md += `The PrimeOS JavaScript Library provides a robust implementation of the Prime Framework `;
      md += `in JavaScript, enabling developers to create mathematically coherent applications based `;
      md += `on the Universal Object Reference (UOR) framework.\n\n`;
      
      // Add TOC
      md += `## Table of Contents\n\n`;
      
      if (Prime.Clifford) {
        md += `* [Clifford Algebra](#clifford-algebra)\n`;
      }
      
      if (Prime.coherence) {
        md += `* [Coherence System](#coherence-system)\n`;
      }
      
      if (Prime.UOR) {
        md += `* [Universal Object Reference (UOR)](#universal-object-reference-uor)\n`;
      }
      
      if (Prime.Lie) {
        md += `* [Lie Groups](#lie-groups)\n`;
      }
      
      if (Prime.Base0) {
        md += `* [Base 0: Neural Network Specification](#base-0-neural-network-specification)\n`;
      }
      
      if (Prime.Base1) {
        md += `* [Base 1: Resource](#base-1-resource)\n`;
      }
      
      if (Prime.Base2) {
        md += `* [Base 2: Kernel](#base-2-kernel)\n`;
      }
      
      if (Prime.Base3) {
        md += `* [Base 3: Application](#base-3-application)\n`;
      }
      
      md += `* [Component Model](#component-model)\n`;
      md += `* [Rendering System](#rendering-system)\n`;
      md += `* [Performance Optimization](#performance-optimization)\n`;
      
      // Add sections based on available modules
      if (Prime.Clifford) {
        md += `\n## Clifford Algebra\n\n`;
        md += `The Clifford Algebra implementation provides a complete framework for geometric algebra `;
        md += `operations, enabling powerful geometric computations with multivectors.\n\n`;
        
        md += `### Key Classes and Functions\n\n`;
        md += `- \`Prime.Clifford.create(config)\`: Create a new Clifford algebra\n`;
        md += `- \`Prime.Clifford.fromArray(arr)\`: Create a multivector from an array\n`;
        
        if (Prime.Clifford.isMultivector) {
          md += `- \`Prime.Clifford.isMultivector(obj)\`: Check if an object is a multivector\n`;
        }
        
        if (Prime.Clifford.isAlgebra) {
          md += `- \`Prime.Clifford.isAlgebra(obj)\`: Check if an object is a Clifford algebra\n`;
        }
        
        md += `\n### Multivector Operations\n\n`;
        md += `- \`add(other)\`: Add two multivectors\n`;
        md += `- \`subtract(other)\`: Subtract two multivectors\n`;
        md += `- \`multiply(other)\`: Geometric product of two multivectors\n`;
        md += `- \`dot(other)\`: Inner product of two multivectors\n`;
        md += `- \`wedge(other)\`: Outer product of two multivectors\n`;
        md += `- \`reverse()\`: Compute the reverse of a multivector\n`;
        md += `- \`conjugate()\`: Compute the conjugate of a multivector\n`;
        md += `- \`norm()\`: Compute the norm of a multivector\n`;
      }
      
      if (Prime.coherence) {
        md += `\n## Coherence System\n\n`;
        md += `The Coherence System provides a mathematical framework for measuring and optimizing `;
        md += `the self-consistency of objects within the system.\n\n`;
        
        md += `### Key Functions\n\n`;
        md += `- \`Prime.coherence.innerProduct(a, b, options)\`: Calculate inner product between two objects\n`;
        md += `- \`Prime.coherence.norm(obj, options)\`: Calculate coherence norm of an object\n`;
        md += `- \`Prime.coherence.isCoherent(obj, tolerance)\`: Check if an object is coherent\n`;
        md += `- \`Prime.coherence.optimize(obj, constraints)\`: Optimize an object for coherence\n`;
        md += `- \`Prime.coherence.createConstraint(predicate, options)\`: Create a coherence constraint\n`;
        md += `- \`Prime.coherence.createState(initialValue, constraints)\`: Create a coherence-constrained state\n`;
        
        md += `\n### System-wide Coherence Tracking\n\n`;
        md += `- \`Prime.coherence.systemCoherence.register(component, weight)\`: Register a component\n`;
        md += `- \`Prime.coherence.systemCoherence.unregister(component)\`: Unregister a component\n`;
        md += `- \`Prime.coherence.systemCoherence.calculateGlobalCoherence()\`: Calculate global coherence\n`;
        md += `- \`Prime.coherence.systemCoherence.optimizeGlobal(options)\`: Optimize global coherence\n`;
      }
      
      // Continue with other sections...
      
      // Component Model section
      md += `\n## Component Model\n\n`;
      md += `The PrimeOS Component Model provides a robust framework for creating reusable UI and `;
      md += `logical components with proper lifecycle management.\n\n`;
      
      md += `### Creating Components\n\n`;
      md += `\`\`\`javascript\n`;
      md += `const component = Prime.createComponent({\n`;
      md += `  meta: {\n`;
      md += `    name: 'MyComponent',\n`;
      md += `    id: 'my-component-1'\n`;
      md += `  },\n`;
      md += `  invariant: {\n`;
      md += `    // Methods that don't change\n`;
      md += `    initialize: function() { /* ... */ },\n`;
      md += `    render: function(element) { /* ... */ }\n`;
      md += `  },\n`;
      md += `  variant: {\n`;
      md += `    // State that changes\n`;
      md += `    count: 0,\n`;
      md += `    items: []\n`;
      md += `  }\n`;
      md += `});\n`;
      md += `\`\`\`\n\n`;
      
      md += `### Component Lifecycle\n\n`;
      md += `- \`component.lifecycle.initialize()\`: Initialize component\n`;
      md += `- \`component.lifecycle.mount(parent)\`: Mount component to parent\n`;
      md += `- \`component.lifecycle.update(newState)\`: Update component state\n`;
      md += `- \`component.lifecycle.unmount()\`: Unmount component\n`;
      md += `- \`component.lifecycle.destroy()\`: Destroy component and clean up resources\n\n`;
      
      md += `### Component Registry\n\n`;
      md += `- \`Prime.ComponentRegistry.register(component)\`: Register a component\n`;
      md += `- \`Prime.ComponentRegistry.unregister(component)\`: Unregister a component\n`;
      md += `- \`Prime.ComponentRegistry.get(id)\`: Get a component by ID\n`;
      md += `- \`Prime.ComponentRegistry.find(predicate)\`: Find components by criteria\n\n`;
      
      md += `### Component Factory\n\n`;
      md += `- \`Prime.ComponentFactory.register(type, factory)\`: Register a component type\n`;
      md += `- \`Prime.ComponentFactory.create(type, config)\`: Create a component of the specified type\n`;
      md += `- \`Prime.ComponentFactory.hasType(type)\`: Check if a component type is registered\n\n`;
      
      // Rendering System section
      md += `\n## Rendering System\n\n`;
      md += `The PrimeOS Rendering System provides a unified interface for rendering objects to `;
      md += `different targets, including DOM, Canvas, WebGL, and SVG.\n\n`;
      
      md += `### Rendering to Different Targets\n\n`;
      md += `- \`Prime.render.toDOM(object, element, options)\`: Render to DOM element\n`;
      md += `- \`Prime.render.toCanvas(object, ctx, options)\`: Render to Canvas context\n`;
      md += `- \`Prime.render.toWebGL(object, gl, options)\`: Render to WebGL context\n`;
      md += `- \`Prime.render.toSVG(object, options)\`: Render to SVG markup\n\n`;
      
      md += `### Animation\n\n`;
      md += `\`\`\`javascript\n`;
      md += `const animation = Prime.render.animate(\n`;
      md += `  progress => {\n`;
      md += `    // Render frame based on progress (0-1)\n`;
      md += `  },\n`;
      md += `  {\n`;
      md += `    duration: 1000, // milliseconds\n`;
      md += `    fps: 60,\n`;
      md += `    easing: t => t, // linear easing\n`;
      md += `    onComplete: () => console.log('Animation complete')\n`;
      md += `  }\n`;
      md += `);\n\n`;
      md += `animation.start(); // Start animation\n`;
      md += `animation.stop();  // Stop animation\n`;
      md += `animation.restart(); // Restart animation\n`;
      md += `\`\`\`\n\n`;
      
      // Performance Optimization section
      md += `\n## Performance Optimization\n\n`;
      md += `The PrimeOS Performance module provides tools for benchmarking and optimizing `;
      md += `application performance.\n\n`;
      
      md += `### Benchmarking\n\n`;
      md += `\`\`\`javascript\n`;
      md += `const results = await Prime.performance.benchmark(\n`;
      md += `  () => {\n`;
      md += `    // Code to benchmark\n`;
      md += `  },\n`;
      md += `  {\n`;
      md += `    iterations: 100,\n`;
      md += `    warmup: 10,\n`;
      md += `    name: 'MyOperation'\n`;
      md += `  }\n`;
      md += `);\n\n`;
      md += `console.log(results.mean); // Average execution time\n`;
      md += `console.log(results.median); // Median execution time\n`;
      md += `console.log(results.stdDev); // Standard deviation\n`;
      md += `\`\`\`\n\n`;
      
      md += `### Comparing Performance\n\n`;
      md += `\`\`\`javascript\n`;
      md += `const comparison = await Prime.performance.compare([\n`;
      md += `  {\n`;
      md += `    name: 'Implementation A',\n`;
      md += `    fn: implementationA\n`;
      md += `  },\n`;
      md += `  {\n`;
      md += `    name: 'Implementation B',\n`;
      md += `    fn: implementationB\n`;
      md += `  }\n`;
      md += `]);\n\n`;
      md += `console.log('Fastest implementation:', comparison.fastest);\n`;
      md += `\`\`\`\n\n`;
      
      md += `### Function Optimization\n\n`;
      md += `\`\`\`javascript\n`;
      md += `const optimizedFn = Prime.performance.optimize(myFunction, {\n`;
      md += `  memoize: true,\n`;
      md += `  memoizeLimit: 1000,\n`;
      md += `  monitor: true,\n`;
      md += `  validateInput: args => args.length > 0,\n`;
      md += `  validateOutput: result => result !== null\n`;
      md += `});\n`;
      md += `\`\`\`\n\n`;
      
      return md;
    };
    
    /**
     * Generate HTML documentation
     * @returns {string} HTML documentation
     */
    const generateHtmlDocumentation = function() {
      // Convert markdown to HTML (simplified version)
      const md = generateMarkdownDocumentation();
      
      // Create HTML wrapper
      let html = `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>PrimeOS JavaScript Library Documentation</title>
  <style>
    body { 
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Oxygen, Ubuntu, Cantarell, "Open Sans", "Helvetica Neue", sans-serif;
      line-height: 1.6;
      color: #333;
      max-width: 800px;
      margin: 0 auto;
      padding: 20px;
    }
    code, pre {
      font-family: SFMono-Regular, Consolas, "Liberation Mono", Menlo, monospace;
      background-color: #f6f8fa;
      border-radius: 3px;
    }
    code {
      padding: 2px 4px;
    }
    pre {
      padding: 16px;
      overflow: auto;
    }
    h1, h2, h3, h4 {
      margin-top: 24px;
      margin-bottom: 16px;
      font-weight: 600;
      line-height: 1.25;
    }
    h1 { font-size: 2em; border-bottom: 1px solid #eaecef; padding-bottom: 0.3em; }
    h2 { font-size: 1.5em; border-bottom: 1px solid #eaecef; padding-bottom: 0.3em; }
    h3 { font-size: 1.25em; }
    h4 { font-size: 1em; }
    a { color: #0366d6; text-decoration: none; }
    a:hover { text-decoration: underline; }
    table { border-collapse: collapse; width: 100%; margin-bottom: 16px; }
    th, td { padding: 8px; border: 1px solid #dfe2e5; }
    th { background-color: #f6f8fa; }
  </style>
</head>
<body>
`;
      
      // Simple markdown to HTML conversion (this is a placeholder - would need a proper markdown parser)
      const htmlContent = md
        .replace(/^# (.*$)/gm, '<h1>$1</h1>')
        .replace(/^## (.*$)/gm, '<h2 id="$1">$1</h2>')
        .replace(/^### (.*$)/gm, '<h3>$1</h3>')
        .replace(/\*\*(.*?)\*\*/g, '<strong>$1</strong>')
        .replace(/\*(.*?)\*/g, '<em>$1</em>')
        .replace(/```javascript\n([\s\S]*?)```/g, '<pre><code class="language-javascript">$1</code></pre>')
        .replace(/```([\s\S]*?)```/g, '<pre><code>$1</code></pre>')
        .replace(/`(.*?)`/g, '<code>$1</code>')
        .replace(/\[(.*?)\]\(#(.*?)\)/g, '<a href="#$2">$1</a>')
        .replace(/\n\n/g, '</p><p>')
        .replace(/^\* (.*$)/gm, '<li>$1</li>')
        .replace(/<\/li><li>/g, '</li>\n<li>')
        .replace(/<li>(.*)<\/li>/gm, '<ul><li>$1</li></ul>')
        .replace(/<\/ul><ul>/g, '');
      
      html += `<p>${htmlContent}</p>`;
      html += `
</body>
</html>`;
      
      return html;
    };
    
    /**
     * Generate JSON documentation
     * @returns {Object} JSON documentation
     */
    const generateJsonDocumentation = function() {
      // Create a structured JSON representation of the Prime Framework
      const doc = {
        name: 'PrimeOS JavaScript Library',
        version: Prime.version,
        modules: []
      };
      
      // Add mathematical modules
      if (Prime.Clifford) {
        doc.modules.push({
          name: 'Clifford Algebra',
          description: 'Complete implementation of geometric algebra with multivectors',
          methods: [
            { name: 'create', description: 'Create a new Clifford algebra' },
            { name: 'fromArray', description: 'Create a multivector from an array' }
          ],
          classes: [
            {
              name: 'Multivector',
              description: 'Representation of an element in a Clifford algebra',
              methods: [
                { name: 'add', description: 'Add two multivectors' },
                { name: 'subtract', description: 'Subtract two multivectors' },
                { name: 'multiply', description: 'Geometric product of two multivectors' },
                { name: 'dot', description: 'Inner product of two multivectors' },
                { name: 'wedge', description: 'Outer product of two multivectors' }
              ]
            },
            {
              name: 'CliffordAlgebra',
              description: 'Implementation of a Clifford algebra with specific dimension and signature',
              methods: [
                { name: 'scalar', description: 'Create a scalar multivector' },
                { name: 'vector', description: 'Create a vector multivector' },
                { name: 'bivector', description: 'Create a bivector multivector' }
              ]
            }
          ]
        });
      }
      
      if (Prime.coherence) {
        doc.modules.push({
          name: 'Coherence System',
          description: 'Mathematical framework for measuring and optimizing object coherence',
          methods: [
            { name: 'innerProduct', description: 'Calculate inner product between two objects' },
            { name: 'norm', description: 'Calculate coherence norm of an object' },
            { name: 'isCoherent', description: 'Check if an object is coherent' },
            { name: 'optimize', description: 'Optimize an object for coherence' },
            { name: 'createConstraint', description: 'Create a coherence constraint' },
            { name: 'createState', description: 'Create a coherence-constrained state' }
          ],
          submodules: [
            {
              name: 'systemCoherence',
              description: 'System-wide coherence tracking',
              methods: [
                { name: 'register', description: 'Register a component for coherence tracking' },
                { name: 'unregister', description: 'Unregister a component from coherence tracking' },
                { name: 'calculateGlobalCoherence', description: 'Calculate global coherence' },
                { name: 'optimizeGlobal', description: 'Optimize global coherence' }
              ]
            }
          ]
        });
      }
      
      // Add component modules
      doc.modules.push({
        name: 'Component Model',
        description: 'Robust framework for creating reusable components with lifecycle management',
        methods: [
          { name: 'createComponent', description: 'Create a new component' }
        ],
        submodules: [
          {
            name: 'ComponentRegistry',
            description: 'System for registering and managing components',
            methods: [
              { name: 'register', description: 'Register a component' },
              { name: 'unregister', description: 'Unregister a component' },
              { name: 'get', description: 'Get a component by ID' },
              { name: 'find', description: 'Find components by criteria' }
            ]
          },
          {
            name: 'ComponentFactory',
            description: 'Factory for creating specialized components',
            methods: [
              { name: 'register', description: 'Register a component type' },
              { name: 'create', description: 'Create a component of the specified type' },
              { name: 'hasType', description: 'Check if a component type is registered' }
            ]
          },
          {
            name: 'ComponentTemplate',
            description: 'Template for creating reusable component templates',
            methods: [
              { name: 'create', description: 'Create a component from this template' },
              { name: 'extend', description: 'Extend this template with additional properties' },
              { name: 'registerType', description: 'Register this template as a component type' }
            ]
          }
        ]
      });
      
      doc.modules.push({
        name: 'Rendering System',
        description: 'Unified interface for rendering objects to different targets',
        methods: [
          { name: 'toDOM', description: 'Render to DOM element' },
          { name: 'toCanvas', description: 'Render to Canvas context' },
          { name: 'toWebGL', description: 'Render to WebGL context' },
          { name: 'toSVG', description: 'Render to SVG markup' },
          { name: 'animate', description: 'Create animation frames' },
          { name: 'registerRenderer', description: 'Register a custom renderer' }
        ]
      });
      
      doc.modules.push({
        name: 'Performance Optimization',
        description: 'Tools for benchmarking and optimizing application performance',
        methods: [
          { name: 'benchmark', description: 'Run a benchmark' },
          { name: 'compare', description: 'Run comparative benchmark of multiple operations' },
          { name: 'optimize', description: 'Create a function optimized for performance' },
          { name: 'getStatistics', description: 'Get performance statistics' },
          { name: 'clearHistory', description: 'Clear performance history' }
        ]
      });
      
      return doc;
    };
    
    // Generate documentation
    return generatePrimeDocumentation();
  };
  
  /**
   * Analytical tools for the Prime Framework
   */
  const analytic = {
    /**
     * Calculate the prime counting function π(x)
     * @param {number} x - Upper limit
     * @returns {number} Number of primes less than or equal to x
     */
    primeCountingFunction: function(x) {
      if (!Prime.Utils.isNumber(x) || x < 0) {
        throw new Prime.ValidationError('Input must be a non-negative number');
      }
      
      if (x < 2) return 0;
      
      // Implementation using the Sieve of Eratosthenes
      const limit = Math.floor(x);
      const sieve = new Array(limit + 1).fill(true);
      sieve[0] = sieve[1] = false;
      
      for (let i = 2; i * i <= limit; i++) {
        if (sieve[i]) {
          for (let j = i * i; j <= limit; j += i) {
            sieve[j] = false;
          }
        }
      }
      
      return sieve.filter(Boolean).length;
    },
    
    /**
     * Estimate the nth prime number
     * @param {number} n - Position of the prime
     * @returns {number} Approximate value of the nth prime
     */
    nthPrimeEstimate: function(n) {
      if (!Prime.Utils.isNumber(n) || n < 1 || !Number.isInteger(n)) {
        throw new Prime.ValidationError('Input must be a positive integer');
      }
      
      if (n === 1) return 2;
      if (n === 2) return 3;
      if (n === 3) return 5;
      
      // Use the approximation p_n ≈ n ln(n) + n ln(ln(n)) - n
      const logn = Math.log(n);
      return Math.floor(n * logn + n * Math.log(logn) - n);
    },
    
    /**
     * Calculate the logarithmic integral Li(x)
     * @param {number} x - Upper limit
     * @returns {number} Logarithmic integral value
     */
    logarithmicIntegral: function(x) {
      if (!Prime.Utils.isNumber(x) || x <= 1) {
        throw new Prime.ValidationError('Input must be greater than 1');
      }
      
      // Numerical integration using the trapezoid rule
      const steps = 1000;
      const start = 2; // Avoid singularity at t=1
      const stepSize = (x - start) / steps;
      
      let sum = 0;
      
      for (let i = 0; i <= steps; i++) {
        const t = start + i * stepSize;
        const weight = (i === 0 || i === steps) ? 0.5 : 1;
        sum += weight * (1 / Math.log(t));
      }
      
      return sum * stepSize;
    },
    
    /**
     * Calculate the Riemann zeta function ζ(s)
     * @param {number} s - Input value
     * @returns {number} Zeta function value
     */
    zetaFunction: function(s) {
      if (!Prime.Utils.isNumber(s)) {
        throw new Prime.ValidationError('Input must be a number');
      }
      
      if (s <= 1) {
        throw new Prime.MathematicalError('Zeta function is undefined for s ≤ 1');
      }
      
      // Simple approximation using a finite sum
      const terms = 1000;
      let sum = 0;
      
      for (let n = 1; n <= terms; n++) {
        sum += 1 / Math.pow(n, s);
      }
      
      return sum;
    },
    
    /**
     * Calculate the Möbius function μ(n)
     * @param {number} n - Input value
     * @returns {number} Möbius function value (-1, 0, or 1)
     */
    mobiusFunction: function(n) {
      if (!Prime.Utils.isNumber(n) || n < 1 || !Number.isInteger(n)) {
        throw new Prime.ValidationError('Input must be a positive integer');
      }
      
      if (n === 1) return 1;
      
      // Factorize n
      let primeFactors = 0;
      let hasDuplicateFactor = false;
      
      for (let i = 2; i * i <= n; i++) {
        if (n % i === 0) {
          // Count how many times i divides n
          let count = 0;
          while (n % i === 0) {
            n /= i;
            count++;
          }
          
          if (count > 1) {
            hasDuplicateFactor = true;
            break;
          }
          
          primeFactors++;
        }
      }
      
      // If n > 1, it's a prime factor itself
      if (n > 1) {
        primeFactors++;
      }
      
      if (hasDuplicateFactor) {
        return 0;
      }
      
      // Return (-1)^primeFactors
      return primeFactors % 2 === 0 ? 1 : -1;
    },
    
    /**
     * Calculate the Euler's totient function φ(n)
     * @param {number} n - Input value
     * @returns {number} Number of integers coprime to n
     */
    totientFunction: function(n) {
      if (!Prime.Utils.isNumber(n) || n < 1 || !Number.isInteger(n)) {
        throw new Prime.ValidationError('Input must be a positive integer');
      }
      
      if (n === 1) return 1;
      
      let result = n;
      
      // For each prime factor, apply φ(n) = n * (1 - 1/p)
      for (let i = 2; i * i <= n; i++) {
        if (n % i === 0) {
          while (n % i === 0) {
            n /= i;
          }
          result -= result / i;
        }
      }
      
      // If n > 1, it's a prime factor itself
      if (n > 1) {
        result -= result / n;
      }
      
      return result;
    },
    
    /**
     * Determine if a number is prime
     * @param {number} n - Number to check
     * @returns {boolean} True if the number is prime
     */
    isPrime: function(n) {
      if (!Prime.Utils.isNumber(n) || !Number.isInteger(n)) {
        throw new Prime.ValidationError('Input must be an integer');
      }
      
      if (n <= 1) return false;
      if (n <= 3) return true;
      if (n % 2 === 0 || n % 3 === 0) return false;
      
      // Check all potential factors of form 6k±1 up to sqrt(n)
      for (let i = 5; i * i <= n; i += 6) {
        if (n % i === 0 || n % (i + 2) === 0) {
          return false;
        }
      }
      
      return true;
    }
  };
  
  // Extend Prime with rendering capabilities
  Prime.render = render;
  
  // Extend Prime with performance capabilities
  Prime.performance = performance;
  
  // Extend Prime with documentation generator
  Prime.generateDocumentation = generateDocumentation;
  
  // Extend Prime with analytical tools
  Prime.analytic = analytic;
  
  // Publish component module loaded event
  Prime.EventBus.publish('module:loaded', { name: 'components-2' });
  
})(Prime);

// Export extended Prime
export { Prime };

// For CommonJS compatibility
if (typeof module !== 'undefined' && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== 'undefined') {
  window.Prime = Prime;
}