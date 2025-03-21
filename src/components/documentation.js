/**
 * PrimeOS JavaScript Library - Component Documentation
 * Documentation generation utilities
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
   * Framework structure documentation generator
   */
  const generateDocumentation = function (options = {}) {
    const docOptions = {
      format: options.format || "markdown",
      includePrivate: options.includePrivate === true,
      includeInternal: options.includeInternal === true,
      depth: options.depth || Infinity,
    };

    /**
     * Generate documentation for Prime object
     * @returns {string} Generated documentation
     */
    const generatePrimeDocumentation = function () {
      if (docOptions.format === "markdown") {
        return generateMarkdownDocumentation();
      } else if (docOptions.format === "html") {
        return generateHtmlDocumentation();
      } else if (docOptions.format === "json") {
        return generateJsonDocumentation();
      }

      throw new Prime.ValidationError(
        `Unsupported documentation format: ${docOptions.format}`,
      );
    };

    /**
     * Generate Markdown documentation
     * @returns {string} Markdown documentation
     */
    const generateMarkdownDocumentation = function () {
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
      md += `const result = await Prime.performance.benchmark(\n`;
      md += `  () => {\n`;
      md += `    // Code to benchmark\n`;
      md += `  },\n`;
      md += `  {\n`;
      md += `    iterations: 100,\n`;
      md += `    warmup: 10,\n`;
      md += `    name: 'MyFunction'\n`;
      md += `  }\n`;
      md += `);\n\n`;
      md += `console.log(result);\n`;
      md += `// {\n`;
      md += `//   name: 'MyFunction',\n`;
      md += `//   iterations: 100,\n`;
      md += `//   mean: 1.25,\n`;
      md += `//   median: 1.2,\n`;
      md += `//   min: 1.0,\n`;
      md += `//   max: 1.9,\n`;
      md += `//   ...\n`;
      md += `// }\n`;
      md += `\`\`\`\n\n`;

      md += `### Function Optimization\n\n`;
      md += `\`\`\`javascript\n`;
      md += `const slowFn = x => x * x;\n\n`;
      md += `const fastFn = Prime.performance.optimize(slowFn, {\n`;
      md += `  memoize: true,\n`;
      md += `  memoizeLimit: 1000,\n`;
      md += `  monitor: true,\n`;
      md += `  validateInput: x => typeof x === 'number',\n`;
      md += `  validateOutput: (result, x) => result >= 0\n`;
      md += `});\n\n`;
      md += `// The optimized function is memoized, monitored, and validated\n`;
      md += `const result = fastFn(10); // Returns 100\n`;
      md += `\`\`\`\n\n`;

      return md;
    };

    /**
     * Generate HTML documentation
     * @returns {string} HTML documentation
     */
    const generateHtmlDocumentation = function () {
      // This is a simplified placeholder
      const md = generateMarkdownDocumentation();

      // Very basic markdown to HTML converter
      const html = md
        .replace(/^# (.*?)$/gm, "<h1>$1</h1>")
        .replace(/^## (.*?)$/gm, "<h2>$1</h2>")
        .replace(/^### (.*?)$/gm, "<h3>$1</h3>")
        .replace(/\n\n/g, "</p><p>")
        .replace(/\*\*(.*?)\*\*/g, "<strong>$1</strong>")
        .replace(/\*(.*?)\*/g, "<em>$1</em>")
        .replace(/`(.*?)`/g, "<code>$1</code>")
        .replace(/```(\w*)\n([\s\S]*?)\n```/g, "<pre><code>$2</code></pre>");

      return `<!DOCTYPE html>
      <html>
      <head>
        <title>PrimeOS JavaScript Library Documentation</title>
        <meta charset="utf-8">
        <style>
          body { font-family: Arial, sans-serif; line-height: 1.6; }
          code { background: #f0f0f0; padding: 2px 4px; }
          pre { background: #f0f0f0; padding: 16px; overflow: auto; }
          table { border-collapse: collapse; }
          th, td { border: 1px solid #ddd; padding: 8px; }
          th { background: #f0f0f0; }
        </style>
      </head>
      <body>
        <p>${html}</p>
      </body>
      </html>`;
    };

    /**
     * Generate JSON documentation
     * @returns {Object} JSON documentation
     */
    const generateJsonDocumentation = function () {
      // This is a simplified placeholder
      // In a full implementation, this would generate a detailed JSON representation

      return {
        name: "PrimeOS JavaScript Library",
        version: Prime.version,
        description:
          "The PrimeOS JavaScript Library provides a robust implementation of the Prime Framework in JavaScript.",
        modules: [
          {
            name: "Core",
            description: "Core utilities and structures",
            exports: ["Utils", "EventBus", "Logger"],
          },
          {
            name: "Components",
            description: "Component system",
            exports: [
              "createComponent",
              "ComponentRegistry",
              "ComponentFactory",
              "ComponentTemplate",
            ],
          },
          {
            name: "Framework",
            description: "Four-tier framework architecture",
            exports: ["Base0", "Base1", "Base2", "Base3"],
          },
          {
            name: "Rendering",
            description: "Rendering system",
            exports: ["render"],
          },
          {
            name: "Performance",
            description: "Performance tools",
            exports: ["performance"],
          },
        ],
      };
    };

    // Run the main documentation generator
    return generatePrimeDocumentation();
  };

  // Export generateDocumentation to Prime
  Prime.generateDocumentation = generateDocumentation;

  // Publish component module loaded event
  Prime.EventBus.publish("module:loaded", { name: "component-documentation" });
})(Prime);

// CommonJS export (no ES module export to avoid circular dependency)
if (typeof module !== "undefined" && module.exports) {
  module.exports = Prime;
}

// For browser global scope
if (typeof window !== "undefined") {
  window.Prime = Prime;
}
