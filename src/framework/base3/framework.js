/**
 * Base3 - Framework Module
 * 
 * Provides enhanced UI framework utilities:
 * - Styling with precise numerical transformations
 * - Layout utilities with mathematical precision
 * - Animation framework with physics-based calculations
 * - Formatting utilities for different output targets
 */

const Prime = require('../../core');
const { Utils } = Prime;

/**
 * Create a framework utility object
 * @param {Object} options - Framework options
 * @returns {Object} Framework utilities
 */
function createFramework(options = {}) {
  // Unit conversion utilities with precise calculations
  const units = {
    // Pixel density for device-independent calculations
    pixelDensity: options.pixelDensity || 1,
    
    // Convert between units with Kahan summation for accuracy
    convert: function(value, fromUnit, toUnit) {
      if (!Prime.Utils.isNumber(value)) {
        throw new Prime.ValidationError('Value must be a number', {
          context: { value, fromUnit, toUnit }
        });
      }
      
      const unitFactors = {
        px: 1,
        em: options.emSize || 16,
        rem: options.rootEmSize || 16,
        vw: options.viewportWidth ? options.viewportWidth / 100 : 0,
        vh: options.viewportHeight ? options.viewportHeight / 100 : 0,
        vmin: options.viewportMin ? options.viewportMin / 100 : 0,
        vmax: options.viewportMax ? options.viewportMax / 100 : 0,
        pct: 0.01 // Percentage as factor
      };
      
      if (!unitFactors[fromUnit] || !unitFactors[toUnit]) {
        throw new Prime.ValidationError('Invalid units specified', {
          context: { 
            value, 
            fromUnit, 
            toUnit,
            supportedUnits: Object.keys(unitFactors)
          }
        });
      }
      
      // Convert to base unit (pixels) then to target unit
      const pxValue = Prime.KahanProduct(value, unitFactors[fromUnit]);
      return Prime.KahanQuotient(pxValue, unitFactors[toUnit]);
    }
  };
  
  // Style utilities with mathematical precision
  const style = {
    /**
     * Create a style object with precise mathematical transformations
     * @param {Object} baseStyle - Base style properties
     * @param {Object} [transformations] - Style transformations to apply
     * @returns {Object} Computed style
     */
    compute: function(baseStyle, transformations = {}) {
      if (!Prime.Utils.isObject(baseStyle)) {
        throw new Prime.ValidationError('Base style must be an object', {
          context: { baseStyle }
        });
      }
      
      // Start with a clone of the base style
      const computedStyle = Prime.Utils.deepClone(baseStyle);
      
      // Apply transformations
      if (transformations.scale && Prime.Utils.isNumber(transformations.scale)) {
        // Scale numerical dimensions
        for (const prop of ['width', 'height', 'top', 'left', 'right', 'bottom', 'margin', 'padding']) {
          if (typeof computedStyle[prop] === 'number') {
            computedStyle[prop] = Prime.KahanProduct(computedStyle[prop], transformations.scale);
          }
        }
      }
      
      if (transformations.rotate && Prime.Utils.isNumber(transformations.rotate)) {
        // Store rotation angle with precise calculation
        const currentRotate = computedStyle.transform?.rotate || 0;
        const newRotate = Prime.KahanSum(currentRotate, transformations.rotate);
        
        computedStyle.transform = computedStyle.transform || {};
        computedStyle.transform.rotate = newRotate;
      }
      
      if (transformations.opacity && Prime.Utils.isNumber(transformations.opacity)) {
        // Apply opacity with clamping
        const currentOpacity = computedStyle.opacity !== undefined ? computedStyle.opacity : 1;
        computedStyle.opacity = Math.max(0, Math.min(1, 
          Prime.KahanProduct(currentOpacity, transformations.opacity)
        ));
      }
      
      // Apply custom transforms if specified
      if (transformations.custom && Prime.Utils.isFunction(transformations.custom)) {
        return transformations.custom(computedStyle);
      }
      
      return computedStyle;
    },
    
    /**
     * Interpolate between two style objects
     * @param {Object} styleA - Starting style
     * @param {Object} styleB - Ending style
     * @param {number} progress - Interpolation progress (0-1)
     * @returns {Object} Interpolated style
     */
    interpolate: function(styleA, styleB, progress) {
      if (!Prime.Utils.isObject(styleA) || !Prime.Utils.isObject(styleB)) {
        throw new Prime.ValidationError('Styles must be objects', {
          context: { styleA, styleB }
        });
      }
      
      if (!Prime.Utils.isNumber(progress)) {
        throw new Prime.ValidationError('Progress must be a number', {
          context: { progress }
        });
      }
      
      // Clamp progress to 0-1 range
      const t = Math.max(0, Math.min(1, progress));
      const result = {};
      
      // Get all properties from both styles
      const allProps = new Set([
        ...Object.keys(styleA),
        ...Object.keys(styleB)
      ]);
      
      for (const prop of allProps) {
        // If property exists in both objects and both values are numbers, interpolate
        if (prop in styleA && prop in styleB && 
            typeof styleA[prop] === 'number' && typeof styleB[prop] === 'number') {
          // Use cubic bezier interpolation for smoother transitions
          const diff = styleB[prop] - styleA[prop];
          result[prop] = Prime.KahanSum(styleA[prop], Prime.KahanProduct(diff, this._cubicBezier(t)));
        }
        // If nested objects exist in both, recursively interpolate
        else if (prop in styleA && prop in styleB && 
                Prime.Utils.isObject(styleA[prop]) && Prime.Utils.isObject(styleB[prop])) {
          result[prop] = this.interpolate(styleA[prop], styleB[prop], t);
        }
        // Otherwise use the value from the appropriate style based on progress
        else {
          result[prop] = t < 0.5 ? styleA[prop] : styleB[prop];
        }
      }
      
      return result;
    },
    
    /**
     * Cubic bezier easing function for smooth interpolation
     * @private
     * @param {number} t - Input parameter (0-1)
     * @returns {number} Eased value
     */
    _cubicBezier: function(t) {
      // Use a smooth ease-in-out curve by default
      const x1 = 0.42;
      const y1 = 0;
      const x2 = 0.58;
      const y2 = 1;
      
      // Newton-Raphson method for solving cubic bezier
      let x = t;
      for (let i = 0; i < 5; i++) {
        const currentX = this._cubicValue(x, 0, x1, x2, 1);
        const currentSlope = this._cubicSlope(x, 0, x1, x2, 1);
        
        if (Math.abs(currentX - t) < 1e-6) {
          break;
        }
        
        x = Prime.KahanDifference(x, Prime.KahanQuotient(currentX - t, currentSlope));
        x = Math.max(0, Math.min(1, x)); // Clamp to 0-1
      }
      
      return this._cubicValue(x, 0, y1, y2, 1);
    },
    
    /**
     * Calculate value of cubic Bezier at parameter t
     * @private
     * @param {number} t - Parameter (0-1)
     * @param {number} p0 - Start point
     * @param {number} p1 - Control point 1
     * @param {number} p2 - Control point 2
     * @param {number} p3 - End point
     * @returns {number} Value at parameter t
     */
    _cubicValue: function(t, p0, p1, p2, p3) {
      const oneMinusT = 1 - t;
      const oneMinusTSquared = oneMinusT * oneMinusT;
      const oneMinusTCubed = oneMinusTSquared * oneMinusT;
      const tSquared = t * t;
      const tCubed = tSquared * t;
      
      return Prime.KahanSum(
        Prime.KahanSum(
          Prime.KahanProduct(p0, oneMinusTCubed),
          Prime.KahanProduct(3 * p1, Prime.KahanProduct(oneMinusTSquared, t))
        ),
        Prime.KahanSum(
          Prime.KahanProduct(3 * p2, Prime.KahanProduct(oneMinusT, tSquared)),
          Prime.KahanProduct(p3, tCubed)
        )
      );
    },
    
    /**
     * Calculate slope of cubic Bezier at parameter t
     * @private
     * @param {number} t - Parameter (0-1)
     * @param {number} p0 - Start point
     * @param {number} p1 - Control point 1
     * @param {number} p2 - Control point 2
     * @param {number} p3 - End point
     * @returns {number} Slope at parameter t
     */
    _cubicSlope: function(t, p0, p1, p2, p3) {
      const oneMinusT = 1 - t;
      return Prime.KahanSum(
        Prime.KahanSum(
          Prime.KahanProduct(3 * (p1 - p0), oneMinusT * oneMinusT),
          Prime.KahanProduct(6 * (p2 - p1), oneMinusT * t)
        ),
        Prime.KahanProduct(3 * (p3 - p2), t * t)
      );
    }
  };
  
  // Layout utilities with mathematical precision
  const layout = {
    /**
     * Calculate grid layout with precise dimensions
     * @param {Object} container - Container dimensions
     * @param {number} itemCount - Number of items
     * @param {Object} options - Layout options
     * @returns {Array} Array of item dimensions
     */
    grid: function(container, itemCount, options = {}) {
      if (!Prime.Utils.isObject(container) || 
          !Prime.Utils.isNumber(container.width) || 
          !Prime.Utils.isNumber(container.height)) {
        throw new Prime.ValidationError('Container must have width and height', {
          context: { container }
        });
      }
      
      if (!Prime.Utils.isNumber(itemCount) || itemCount <= 0) {
        throw new Prime.ValidationError('Item count must be a positive number', {
          context: { itemCount }
        });
      }
      
      // Apply defaults with type checking
      const gap = Prime.Utils.isNumber(options.gap) ? options.gap : 8;
      const aspectRatio = Prime.Utils.isNumber(options.aspectRatio) ? options.aspectRatio : 1;
      
      // Calculate optimal grid dimensions using golden ratio
      const optimalRatio = options.preferHorizontal ? 1.618 : 1 / 1.618;
      let columns = Math.round(Math.sqrt(itemCount * optimalRatio));
      columns = Math.max(1, Math.min(itemCount, columns));
      
      let rows = Math.ceil(itemCount / columns);
      
      // Recalculate to fit container aspect ratio more precisely
      const containerRatio = container.width / container.height;
      
      if (containerRatio > 1 && rows > 1) {
        // Wider container - may need more columns
        const adjustedColumns = Math.min(itemCount, columns + 1);
        const adjustedRows = Math.ceil(itemCount / adjustedColumns);
        
        if (adjustedRows < rows) {
          columns = adjustedColumns;
          rows = adjustedRows;
        }
      } else if (containerRatio < 1 && columns > 1) {
        // Taller container - may need more rows
        const adjustedColumns = Math.max(1, columns - 1);
        const adjustedRows = Math.ceil(itemCount / adjustedColumns);
        
        if (adjustedRows <= itemCount) {
          columns = adjustedColumns;
          rows = adjustedRows;
        }
      }
      
      // Calculate item size with precise math
      const totalGapWidth = gap * (columns - 1);
      const totalGapHeight = gap * (rows - 1);
      
      const itemWidth = Prime.KahanQuotient(
        Prime.KahanDifference(container.width, totalGapWidth),
        columns
      );
      
      const itemHeight = options.maintainAspectRatio ?
        Prime.KahanQuotient(itemWidth, aspectRatio) :
        Prime.KahanQuotient(
          Prime.KahanDifference(container.height, totalGapHeight),
          rows
        );
      
      // Generate item positions
      const items = [];
      
      for (let i = 0; i < itemCount; i++) {
        const col = i % columns;
        const row = Math.floor(i / columns);
        
        const x = Prime.KahanSum(
          Prime.KahanProduct(col, itemWidth),
          Prime.KahanProduct(col, gap)
        );
        
        const y = Prime.KahanSum(
          Prime.KahanProduct(row, itemHeight),
          Prime.KahanProduct(row, gap)
        );
        
        items.push({
          index: i,
          x, 
          y,
          width: itemWidth,
          height: itemHeight
        });
      }
      
      return items;
    },
    
    /**
     * Arrange items in a flex-like layout
     * @param {Object} container - Container dimensions
     * @param {Array} items - Items with dimensions
     * @param {Object} options - Layout options
     * @returns {Array} Arranged items
     */
    flex: function(container, items, options = {}) {
      if (!Prime.Utils.isObject(container) || 
          !Prime.Utils.isNumber(container.width) || 
          !Prime.Utils.isNumber(container.height)) {
        throw new Prime.ValidationError('Container must have width and height', {
          context: { container }
        });
      }
      
      if (!Array.isArray(items)) {
        throw new Prime.ValidationError('Items must be an array', {
          context: { items }
        });
      }
      
      // Apply defaults with type checking
      const direction = options.direction || 'row';
      const gap = Prime.Utils.isNumber(options.gap) ? options.gap : 8;
      const align = options.align || 'start';
      const justify = options.justify || 'start';
      
      const isHorizontal = direction === 'row';
      const mainSize = isHorizontal ? container.width : container.height;
      const crossSize = isHorizontal ? container.height : container.width;
      
      // Calculate flex layout
      let mainPosition = 0;
      const arrangedItems = [];
      
      for (let i = 0; i < items.length; i++) {
        const item = items[i];
        
        if (!Prime.Utils.isObject(item) ||
            !Prime.Utils.isNumber(item.width) ||
            !Prime.Utils.isNumber(item.height)) {
          throw new Prime.ValidationError(`Item at index ${i} must have width and height`, {
            context: { item }
          });
        }
        
        const itemMainSize = isHorizontal ? item.width : item.height;
        const itemCrossSize = isHorizontal ? item.height : item.width;
        
        // Calculate cross position based on alignment
        let crossPosition;
        
        switch (align) {
          case 'center':
            crossPosition = Prime.KahanQuotient(
              Prime.KahanDifference(crossSize, itemCrossSize),
              2
            );
            break;
          case 'end':
            crossPosition = Prime.KahanDifference(crossSize, itemCrossSize);
            break;
          case 'stretch':
            crossPosition = 0;
            // Adjust item cross size if stretch is specified
            if (isHorizontal) {
              item.height = crossSize;
            } else {
              item.width = crossSize;
            }
            break;
          case 'start':
          default:
            crossPosition = 0;
            break;
        }
        
        // Add arranged item with precise position calculation
        const arrangedItem = {
          ...item,
          x: isHorizontal ? mainPosition : crossPosition,
          y: isHorizontal ? crossPosition : mainPosition
        };
        
        arrangedItems.push(arrangedItem);
        
        // Update main position for next item
        mainPosition = Prime.KahanSum(
          mainPosition,
          Prime.KahanSum(itemMainSize, gap)
        );
      }
      
      // Apply justification if needed
      if (justify !== 'start' && mainPosition < mainSize) {
        const totalSpace = Prime.KahanDifference(mainSize, mainPosition) + gap; // Add gap back from last item
        
        if (justify === 'center') {
          const offset = Prime.KahanQuotient(totalSpace, 2);
          
          for (const item of arrangedItems) {
            if (isHorizontal) {
              item.x = Prime.KahanSum(item.x, offset);
            } else {
              item.y = Prime.KahanSum(item.y, offset);
            }
          }
        } else if (justify === 'end') {
          for (const item of arrangedItems) {
            if (isHorizontal) {
              item.x = Prime.KahanSum(item.x, totalSpace);
            } else {
              item.y = Prime.KahanSum(item.y, totalSpace);
            }
          }
        } else if (justify === 'space-between' && arrangedItems.length > 1) {
          const spacePerGap = Prime.KahanQuotient(
            totalSpace,
            arrangedItems.length - 1
          );
          
          for (let i = 1; i < arrangedItems.length; i++) {
            const offset = Prime.KahanProduct(i, spacePerGap);
            
            if (isHorizontal) {
              arrangedItems[i].x = Prime.KahanSum(arrangedItems[i].x, offset);
            } else {
              arrangedItems[i].y = Prime.KahanSum(arrangedItems[i].y, offset);
            }
          }
        } else if (justify === 'space-around' && arrangedItems.length > 0) {
          const spacePerItem = Prime.KahanQuotient(
            totalSpace,
            arrangedItems.length
          );
          
          for (let i = 0; i < arrangedItems.length; i++) {
            const offset = Prime.KahanProduct(
              Prime.KahanSum(i, 0.5),
              spacePerItem
            );
            
            if (isHorizontal) {
              arrangedItems[i].x = Prime.KahanSum(arrangedItems[i].x, offset);
            } else {
              arrangedItems[i].y = Prime.KahanSum(arrangedItems[i].y, offset);
            }
          }
        }
      }
      
      return arrangedItems;
    }
  };
  
  // Animation utilities with physics-based calculations
  const animation = {
    /**
     * Create a physics-based spring animation
     * @param {Object} options - Animation options
     * @returns {Object} Spring animation controller
     */
    spring: function(options = {}) {
      const config = {
        stiffness: Prime.Utils.isNumber(options.stiffness) ? options.stiffness : 100,
        damping: Prime.Utils.isNumber(options.damping) ? options.damping : 10,
        mass: Prime.Utils.isNumber(options.mass) ? options.mass : 1,
        precision: Prime.Utils.isNumber(options.precision) ? options.precision : 0.01,
        maxSteps: Prime.Utils.isNumber(options.maxSteps) ? options.maxSteps : 100
      };
      
      return {
        /**
         * Animate a value with spring physics
         * @param {number} from - Starting value
         * @param {number} to - Target value
         * @param {Function} callback - Progress callback
         * @returns {Promise} Animation promise
         */
        animate: function(from, to, callback) {
          if (!Prime.Utils.isNumber(from) || !Prime.Utils.isNumber(to)) {
            throw new Prime.ValidationError('From and to values must be numbers', {
              context: { from, to }
            });
          }
          
          if (!Prime.Utils.isFunction(callback)) {
            throw new Prime.ValidationError('Callback must be a function', {
              context: { callback }
            });
          }
          
          return new Promise((resolve) => {
            let value = from;
            let velocity = 0;
            let step = 0;
            
            const animate = () => {
              // Calculate spring force with high precision
              const distance = Prime.KahanDifference(to, value);
              const springForce = Prime.KahanProduct(distance, config.stiffness);
              const dampingForce = Prime.KahanProduct(velocity, config.damping);
              
              // Calculate acceleration with Newton's second law (F = ma)
              const netForce = Prime.KahanDifference(springForce, dampingForce);
              const acceleration = Prime.KahanQuotient(netForce, config.mass);
              
              // Update velocity with integration (Verlet)
              const prevVelocity = velocity;
              velocity = Prime.KahanSum(velocity, 
                Prime.KahanProduct(acceleration, 1/60) // Assuming 60fps
              );
              
              // Average velocity for better energy conservation
              const avgVelocity = Prime.KahanQuotient(
                Prime.KahanSum(prevVelocity, velocity),
                2
              );
              
              // Update position
              value = Prime.KahanSum(value, 
                Prime.KahanProduct(avgVelocity, 1/60)
              );
              
              // Report progress
              callback(value);
              
              // Check for completion
              const isComplete = (
                Math.abs(distance) < config.precision && 
                Math.abs(velocity) < config.precision
              ) || (step >= config.maxSteps);
              
              if (isComplete) {
                // Ensure target value is reached exactly
                callback(to);
                resolve();
              } else {
                step++;
                requestAnimationFrame(animate);
              }
            };
            
            // Start animation
            animate();
          });
        }
      };
    },
    
    /**
     * Create a physics-based particle system
     * @param {Object} options - Particle system options
     * @returns {Object} Particle system controller
     */
    particles: function(options = {}) {
      const config = {
        count: Prime.Utils.isNumber(options.count) ? options.count : 50,
        gravity: Prime.Utils.isNumber(options.gravity) ? options.gravity : 9.8,
        drag: Prime.Utils.isNumber(options.drag) ? options.drag : 0.02,
        lifespan: Prime.Utils.isNumber(options.lifespan) ? options.lifespan : 2000
      };
      
      // Initialize particles with precise positions
      const particles = [];
      let isRunning = false;
      
      // System controller
      return {
        /**
         * Start the particle system
         * @param {Object} origin - Emission origin point
         * @param {Function} renderer - Particle rendering function
         * @returns {Function} Stop function
         */
        start: function(origin, renderer) {
          if (!Prime.Utils.isObject(origin) || 
              !Prime.Utils.isNumber(origin.x) || 
              !Prime.Utils.isNumber(origin.y)) {
            throw new Prime.ValidationError('Origin must have x and y coordinates', {
              context: { origin }
            });
          }
          
          if (!Prime.Utils.isFunction(renderer)) {
            throw new Prime.ValidationError('Renderer must be a function', {
              context: { renderer }
            });
          }
          
          // Reset particles
          particles.length = 0;
          
          // Initialize particles
          for (let i = 0; i < config.count; i++) {
            // Calculate emission angle with precise distribution
            const angle = Prime.KahanProduct(
              Prime.KahanQuotient(i, config.count),
              Math.PI * 2
            );
            
            // Add some controlled randomness
            const speed = 2 + (Math.random() * 2);
            const randomizedAngle = Prime.KahanSum(angle, 
              Prime.KahanProduct((Math.random() - 0.5), 0.5)
            );
            
            particles.push({
              x: origin.x,
              y: origin.y,
              vx: Prime.KahanProduct(Math.cos(randomizedAngle), speed),
              vy: Prime.KahanProduct(Math.sin(randomizedAngle), speed),
              life: 1.0,
              decay: 0.5 + (Math.random() * 0.5) // Controlled randomness
            });
          }
          
          isRunning = true;
          let lastTime = Date.now();
          
          const update = () => {
            if (!isRunning) return;
            
            const now = Date.now();
            const deltaTime = (now - lastTime) / 1000; // Convert to seconds
            lastTime = now;
            
            // Update all particles
            for (let i = particles.length - 1; i >= 0; i--) {
              const p = particles[i];
              
              // Update life
              p.life = Prime.KahanDifference(p.life, 
                Prime.KahanProduct(p.decay, 
                  Prime.KahanQuotient(deltaTime, config.lifespan / 1000)
                )
              );
              
              if (p.life <= 0) {
                // Respawn particle at origin
                p.x = origin.x;
                p.y = origin.y;
                p.life = 1.0;
                
                const angle = Math.random() * Math.PI * 2;
                const speed = 2 + (Math.random() * 2);
                
                p.vx = Prime.KahanProduct(Math.cos(angle), speed);
                p.vy = Prime.KahanProduct(Math.sin(angle), speed);
              } else {
                // Apply physics with precise calculations
                // Apply gravity
                p.vy = Prime.KahanSum(p.vy, 
                  Prime.KahanProduct(config.gravity, deltaTime)
                );
                
                // Apply drag
                p.vx = Prime.KahanProduct(p.vx, 
                  Prime.KahanDifference(1, Prime.KahanProduct(config.drag, deltaTime))
                );
                p.vy = Prime.KahanProduct(p.vy, 
                  Prime.KahanDifference(1, Prime.KahanProduct(config.drag, deltaTime))
                );
                
                // Update position
                p.x = Prime.KahanSum(p.x, Prime.KahanProduct(p.vx, deltaTime));
                p.y = Prime.KahanSum(p.y, Prime.KahanProduct(p.vy, deltaTime));
              }
            }
            
            // Render particles
            renderer(particles);
            
            // Schedule next frame
            requestAnimationFrame(update);
          };
          
          // Start animation
          update();
          
          // Return stop function
          return () => {
            isRunning = false;
          };
        }
      };
    }
  };
  
  return {
    units,
    style,
    layout,
    animation,
    
    /**
     * Format text with secure handling of special characters
     * @param {string} text - Input text
     * @param {string} format - Output format (html, xml, plain, csv)
     * @returns {string} Formatted text
     */
    formatText: function(text, format = 'plain') {
      if (typeof text !== 'string') {
        throw new Prime.ValidationError('Text must be a string', {
          context: { text, format }
        });
      }
      
      switch (format.toLowerCase()) {
        case 'html':
          return text
            .replace(/&/g, '&amp;')
            .replace(/</g, '&lt;')
            .replace(/>/g, '&gt;')
            .replace(/"/g, '&quot;')
            .replace(/'/g, '&#039;');
          
        case 'xml':
          return text
            .replace(/&/g, '&amp;')
            .replace(/</g, '&lt;')
            .replace(/>/g, '&gt;')
            .replace(/"/g, '&quot;')
            .replace(/'/g, '&apos;');
          
        case 'csv':
          // RFC 4180 compliant CSV escaping
          if (text.includes('"') || text.includes(',') || text.includes('\n') || text.includes('\r')) {
            return '"' + text.replace(/"/g, '""') + '"';
          }
          return text;
          
        case 'plain':
        default:
          return text;
      }
    }
  };
}

module.exports = createFramework;