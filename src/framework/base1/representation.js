/**
 * PrimeOS JavaScript Library - Framework
 * Base 1 Representation Model
 */

// Import core
const Prime = require('../../core.js');
const MathUtils = require('../math');

/**
 * Representation Model - Handles output formatting and visualization
 */
const RepresentationModel = {
  /**
   * Create a representation model
   * @param {Object} config - Configuration object
   * @returns {Object} Representation model
   */
  create: function (config = {}) {
    return {
      type: 'representation',
      renderers: config.renderers || [],
      name: config.name || 'RepresentationModel',

      // Added security features for safer HTML and XML generation
      security: {
        allowedHtmlTags: config.allowedHtmlTags || [
          'div',
          'span',
          'p',
          'ul',
          'ol',
          'li',
          'dl',
          'dt',
          'dd',
          'table',
          'tr',
          'td',
          'th',
          'thead',
          'tbody',
          'tfoot',
          'h1',
          'h2',
          'h3',
          'h4',
          'h5',
          'h6',
          'pre',
          'code',
          'a',
          'img',
          'time',
        ],
        allowedHtmlAttributes: config.allowedHtmlAttributes || [
          'id',
          'class',
          'href',
          'src',
          'alt',
          'title',
          'datetime',
          'width',
          'height',
          'target',
        ],
      },

      /**
       * Present an object in a specified format
       * @param {*} object - Object to present
       * @param {string} format - Format name
       * @param {Object} [options] - Presentation options
       * @param {boolean} [options.backwardsCompatible] - Use simpler formatting for backwards compatibility (default: true)
       * @returns {*} Presented object
       */
      present: function (object, format, options = {}) {
        // Default to backwards compatible mode for tests
        const backwardsCompatible = options.backwardsCompatible !== false;

        // Validate inputs
        if (object === undefined) {
          return options.undefinedPlaceholder || '';
        }

        // Check if this model has a Base 0 representation model
        if (this._base0 && this._base0.representation) {
          // Use the Base 0 representation model if it supports this format
          if (
            this._base0.representation.formats &&
            this._base0.representation.formats[format]
          ) {
            try {
              return this._base0.representation.represent(object, format);
            } catch (error) {
              Prime.Logger.error(
                `Error using Base0 representation for ${format}:`,
                error,
              );
              // Fall through to default implementations
            }
          }
        }

        // For backwards compatibility with tests
        if (backwardsCompatible) {
          // Simple implementations for backwards compatibility
          if (format === 'string') {
            if (typeof object === 'object' && object !== null) {
              // Ensure object properties are included in the string representation
              try {
                return JSON.stringify(object);
              } catch (e) {
                // Handle circular references
                return (
                  Object.prototype.toString.call(object) +
                  ' ' +
                  Object.keys(object).join(', ')
                );
              }
            }
            return String(object);
          } else if (format === 'json') {
            return JSON.stringify(object);
          } else if (format === 'html') {
            // Simple HTML representation
            if (typeof object === 'string') {
              return `<div>${this._escapeHtml(object)}</div>`;
            } else if (Array.isArray(object)) {
              return `<ul>${object.map((item) => `<li>${this._escapeHtml(this.present(item, 'string'))}</li>`).join('')}</ul>`;
            } else if (typeof object === 'object' && object !== null) {
              return `<dl>${Object.entries(object)
                .map(
                  ([key, value]) =>
                    `<dt>${this._escapeHtml(key)}</dt><dd>${this._escapeHtml(this.present(value, 'string'))}</dd>`,
                )
                .join('')}</dl>`;
            } else {
              return `<div>${this._escapeHtml(String(object))}</div>`;
            }
          }
        }

        // Advanced implementations with proper escaping, validation, and error handling
        try {
          switch (format) {
            case 'string':
              return this._presentAsString(object, options);

            case 'json':
              return this._presentAsJson(object, options);

            case 'html':
              return this._presentAsHtml(object, options);

            case 'xml':
              return this._presentAsXml(object, options);

            case 'csv':
              if (Array.isArray(object)) {
                return this._presentAsCsv(object, options);
              }
              throw new Prime.InvalidOperationError(
                'CSV format requires an array input',
              );

            default:
              throw new Prime.InvalidOperationError(
                `Format ${format} not supported`,
                {
                  context: {
                    availableFormats: ['string', 'json', 'html', 'xml', 'csv'],
                    requestedFormat: format,
                  },
                },
              );
          }
        } catch (error) {
          Prime.Logger.error(
            `Error presenting object in ${format} format:`,
            error,
          );

          // Fallback to simple string conversion on error
          try {
            return String(object);
          } catch (fallbackError) {
            return '[Error presenting object]';
          }
        }
      },

      /**
       * Present object as string with enhanced handling for various types
       * @private
       * @param {*} object - Object to present
       * @param {Object} options - Presentation options
       * @returns {string} String representation
       */
      _presentAsString: function (object, options = {}) {
        if (object === null) {
          return options.nullPlaceholder || 'null';
        }

        if (typeof object === 'function') {
          return options.functionPlaceholder || '[Function]';
        }

        if (typeof object === 'symbol') {
          return object.toString();
        }

        if (typeof object !== 'object') {
          return String(object);
        }

        // Handle circular references in objects
        try {
          const maxDepth = options.maxDepth || 2;
          const cache = new Set();

          const stringify = (obj, depth = 0) => {
            if (obj === null) return 'null';
            if (obj === undefined) return 'undefined';

            if (typeof obj !== 'object') {
              return String(obj);
            }

            if (depth >= maxDepth) {
              return options.depthExceededPlaceholder || '[Object]';
            }

            if (cache.has(obj)) {
              return options.circularReferencePlaceholder || '[Circular]';
            }

            cache.add(obj);

            // Handle arrays
            if (Array.isArray(obj)) {
              const items = obj.map((item) => stringify(item, depth + 1));
              return `[${items.join(', ')}]`;
            }

            // Handle Date objects
            if (obj instanceof Date) {
              return obj.toISOString();
            }

            // Handle other objects
            const pairs = [];
            for (const key in obj) {
              if (Object.prototype.hasOwnProperty.call(obj, key)) {
                pairs.push(`${key}: ${stringify(obj[key], depth + 1)}`);
              }
            }

            return `{${pairs.join(', ')}}`;
          };

          return stringify(object);
        } catch (error) {
          // Fallback on error
          Prime.Logger.warn('Error converting object to string:', error);
          return Object.prototype.toString.call(object);
        }
      },

      /**
       * Present object as JSON with enhanced handling for circular references
       * @private
       * @param {*} object - Object to present
       * @param {Object} options - Presentation options
       * @returns {string} JSON representation
       */
      _presentAsJson: function (object, options = {}) {
        const circularReplacer = () => {
          const seen = new WeakSet();
          return (key, value) => {
            // Handle non-object values
            if (typeof value !== 'object' || value === null) {
              return value;
            }

            // Handle circular references
            if (seen.has(value)) {
              return options.circularReferencePlaceholder || '[Circular]';
            }

            seen.add(value);
            return value;
          };
        };

        // Use try-catch to handle any JSON.stringify errors
        try {
          // Safely stringify with circular reference handling
          return JSON.stringify(
            object,
            circularReplacer(),
            options.pretty ? 2 : undefined,
          );
        } catch (error) {
          // If stringification fails, try a more robust approach
          Prime.Logger.warn('Error in JSON.stringify:', error);

          // Fallback implementation for problematic objects
          const cache = new Set();
          const safeObject = (obj) => {
            if (obj === null || typeof obj !== 'object') {
              return obj;
            }

            if (cache.has(obj)) {
              return options.circularReferencePlaceholder || '[Circular]';
            }

            cache.add(obj);

            if (Array.isArray(obj)) {
              return obj.map((item) => safeObject(item));
            }

            const result = {};
            for (const key of Object.keys(obj)) {
              try {
                result[key] = safeObject(obj[key]);
              } catch (e) {
                result[key] = '[Error]';
              }
            }

            return result;
          };

          // Try again with the sanitized object
          return JSON.stringify(
            safeObject(object),
            null,
            options.pretty ? 2 : undefined,
          );
        }
      },

      /**
       * Present object as HTML with enhanced security and cross-site scripting protection
       * @private
       * @param {*} object - Object to present
       * @param {Object} options - Presentation options
       * @returns {string} HTML representation
       */
      _presentAsHtml: function (object, options = {}) {
        const maxDepth = options.maxDepth || 3;
        const classes = options.classes || {};

        // Recursive function to convert objects to HTML with depth tracking
        const objectToHtml = (obj, depth = 0) => {
          // Check depth limit
          if (depth >= maxDepth) {
            return this._createSafeHtml(
              'div',
              this._escapeHtml(options.depthExceededPlaceholder || '[Object]'),
              {
                class: classes.depthExceeded || 'depth-exceeded',
              },
            );
          }

          // Handle null and undefined
          if (obj === null) {
            return this._createSafeHtml(
              'span',
              this._escapeHtml(options.nullPlaceholder || 'null'),
              {
                class: classes.null || 'null-value',
              },
            );
          }

          if (obj === undefined) {
            return this._createSafeHtml(
              'span',
              this._escapeHtml(options.undefinedPlaceholder || 'undefined'),
              {
                class: classes.undefined || 'undefined-value',
              },
            );
          }

          // Handle primitives
          if (typeof obj !== 'object') {
            const value = this._escapeHtml(String(obj));
            const type = typeof obj;
            return this._createSafeHtml('span', value, {
              class: classes[type] || `${type}-value`,
            });
          }

          // Handle arrays
          if (Array.isArray(obj)) {
            let itemsHtml = '';
            for (let i = 0; i < obj.length; i++) {
              const item = obj[i];
              itemsHtml += this._createSafeHtml(
                'li',
                objectToHtml(item, depth + 1),
              );
            }

            return this._createSafeHtml('ul', itemsHtml, {
              class: classes.array || 'array-list',
            });
          }

          // Handle dates
          if (obj instanceof Date) {
            return this._createSafeHtml(
              'time',
              this._escapeHtml(obj.toISOString()),
              {
                datetime: obj.toISOString(),
                class: classes.date || 'date-value',
              },
            );
          }

          // Handle objects
          let entriesHtml = '';
          for (const [key, value] of Object.entries(obj)) {
            const keyHtml = this._createSafeHtml('dt', this._escapeHtml(key), {
              class: classes.key || 'object-key',
            });
            const valueHtml = this._createSafeHtml(
              'dd',
              objectToHtml(value, depth + 1),
              {
                class: classes.value || 'object-value',
              },
            );
            entriesHtml += keyHtml + valueHtml;
          }

          return this._createSafeHtml('dl', entriesHtml, {
            class: classes.object || 'object-list',
          });
        };

        // Convert the object to HTML
        return objectToHtml(object);
      },

      /**
       * Present object as XML with improved security and validation
       * @private
       * @param {*} object - Object to present
       * @param {Object} options - Presentation options
       * @returns {string} XML representation
       */
      _presentAsXml: function (object, options = {}) {
        // XML representation with proper escaping
        const createXmlElement = (name, value, attributes = {}) => {
          // Validate element name (XML requires valid names)
          const safeName = /^[a-zA-Z_][\w.-]*$/.test(name) ? name : 'element';

          // Create attributes string with proper escaping
          let attributesStr = '';
          for (const [key, attrValue] of Object.entries(attributes)) {
            if (/^[a-zA-Z_][\w.-]*$/.test(key)) {
              attributesStr += ` ${key}="${this._escapeXml(String(attrValue))}"`;
            }
          }

          // Handle different value types
          if (value === null || value === undefined) {
            return `<${safeName}${attributesStr}/>`;
          } else if (typeof value !== 'object') {
            return `<${safeName}${attributesStr}>${this._escapeXml(String(value))}</${safeName}>`;
          } else {
            // For objects, recursively convert properties to elements
            let childElements = '';

            if (Array.isArray(value)) {
              // For arrays, create item elements
              childElements = value
                .map((item) => createXmlElement('item', item))
                .join('');
            } else if (value instanceof Date) {
              // Handle Date objects specially
              return `<${safeName}${attributesStr} type="datetime">${this._escapeXml(value.toISOString())}</${safeName}>`;
            } else {
              // For objects, create property elements
              for (const [propName, propValue] of Object.entries(value)) {
                childElements += createXmlElement(propName, propValue);
              }
            }

            return `<${safeName}${attributesStr}>${childElements}</${safeName}>`;
          }
        };

        // Generate proper XML header with optional encoding
        const xmlHeader = `<?xml version="1.0" encoding="${options.encoding || 'UTF-8'}"?>`;

        // Convert the root object to XML with a well-defined root element name
        const rootName = options.rootElement || 'root';
        const xmlContent = createXmlElement(rootName, object);

        return `${xmlHeader}\n${xmlContent}`;
      },

      /**
       * Present array of objects as CSV with improved handling of special characters
       * @private
       * @param {Array} array - Array of objects to present
       * @param {Object} options - Presentation options
       * @returns {string} CSV representation
       */
      _presentAsCsv: function (array, options = {}) {
        // CSV format for arrays of objects
        if (array.length === 0) {
          return '';
        }

        // Get headers from the first object or from options
        const headers = options.headers || Object.keys(array[0] || {});

        // Proper CSV escaping function
        const escapeCsvValue = (value) => {
          if (value === null || value === undefined) {
            return '';
          }

          const stringValue =
            typeof value === 'string'
              ? value
              : typeof value === 'object'
                ? JSON.stringify(value)
                : String(value);

          // According to RFC 4180, fields containing line breaks, double quotes, or commas
          // should be enclosed in double quotes, and double quotes should be escaped with double quotes
          if (
            stringValue.includes('"') ||
            stringValue.includes(',') ||
            stringValue.includes('\n') ||
            stringValue.includes('\r')
          ) {
            return `"${stringValue.replace(/"/g, '""')}"`;
          }

          return stringValue;
        };

        // Create CSV header row
        let csv =
          headers.map((header) => escapeCsvValue(header)).join(',') + '\n';

        // Create data rows
        for (const row of array) {
          const values = headers.map((header) => {
            const value = row[header];
            return escapeCsvValue(value);
          });

          csv += values.join(',') + '\n';
        }

        return csv;
      },

      /**
       * Render an object to a target
       * @param {*} object - Object to render
       * @param {*} target - Render target
       * @returns {*} Render result
       */
      render: function (object, target) {
        // Find a suitable renderer
        const renderer = this.renderers.find((r) =>
          r.canRender(object, target),
        );

        if (!renderer) {
          throw new Prime.InvalidOperationError('No suitable renderer found', {
            context: {
              objectType: typeof object,
              targetType: typeof target,
            },
          });
        }

        return renderer.render(object, target);
      },

      /**
       * Add a renderer
       * @param {Object} renderer - Renderer to add
       * @returns {Object} Updated representation model
       */
      addRenderer: function (renderer) {
        if (
          typeof renderer.canRender !== 'function' ||
          typeof renderer.render !== 'function'
        ) {
          throw new Prime.ValidationError(
            'Renderer must have canRender and render methods',
          );
        }

        this.renderers.push(renderer);
        return this;
      },

      /**
       * Escape HTML special characters
       * @private
       * @param {string} str - String to escape
       * @returns {string} Escaped string
       */
      _escapeHtml: function (str) {
        if (typeof str !== 'string') {
          str = String(str);
        }

        return str
          .replace(/&/g, '&amp;')
          .replace(/</g, '&lt;')
          .replace(/>/g, '&gt;')
          .replace(/"/g, '&quot;')
          .replace(/'/g, '&#039;');
      },

      /**
       * Escape XML special characters
       * @private
       * @param {string} str - String to escape
       * @returns {string} Escaped string
       */
      _escapeXml: function (str) {
        if (typeof str !== 'string') {
          str = String(str);
        }

        return str
          .replace(/&/g, '&amp;')
          .replace(/</g, '&lt;')
          .replace(/>/g, '&gt;')
          .replace(/"/g, '&quot;')
          .replace(/'/g, '&apos;');
      },

      /**
       * Create safe HTML with strict tag and attribute validation
       * @private
       * @param {string} tagName - HTML tag name
       * @param {string} content - HTML content
       * @param {Object} attributes - HTML attributes
       * @returns {string} Safe HTML
       */
      _createSafeHtml: function (tagName, content, attributes = {}) {
        // Validate tag name against allowed list
        const safeTagName = this.security.allowedHtmlTags.includes(tagName)
          ? tagName
          : 'div';

        // Create attributes string with proper escaping and validation
        let attributesStr = '';
        for (const [key, value] of Object.entries(attributes)) {
          // Only allow valid attribute names from allowed list
          if (this.security.allowedHtmlAttributes.includes(key)) {
            attributesStr += ` ${key}="${this._escapeHtml(String(value))}"`;
          }
        }

        // Create the HTML with proper structure
        return `<${safeTagName}${attributesStr}>${content}</${safeTagName}>`;
      },

      /**
       * Connect to Base 0 components
       * @param {Object} base0 - Base 0 components
       * @returns {Object} Connected representation model
       */
      connectToBase0: function (base0) {
        this._base0 = base0;
        return this;
      },
    };
  },
};

module.exports = RepresentationModel;
