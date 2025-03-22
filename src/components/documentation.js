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

      throw new Error(`Unsupported documentation format: ${docOptions.format}`);
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

      return md;
    };

    /**
     * Generate HTML documentation
     * @returns {string} HTML documentation
     */
    const generateHtmlDocumentation = function () {
      const md = generateMarkdownDocumentation();
      
      // Basic conversion from markdown to HTML
      const html = md
        .replace(/^# (.*?)$/gm, '<h1>$1</h1>')
        .replace(/^## (.*?)$/gm, '<h2>$1</h2>')
        .replace(/\*\*(.*?)\*\*/g, '<strong>$1</strong>');
      
      return `<!DOCTYPE html>
      <html>
      <head>
        <title>PrimeOS Documentation</title>
      </head>
      <body>
        ${html}
      </body>
      </html>`;
    };

    /**
     * Generate JSON documentation
     * @returns {Object} JSON documentation
     */
    const generateJsonDocumentation = function () {
      // Basic documentation structure
      return {
        name: "PrimeOS JavaScript Library",
        version: Prime.version || "1.0.0",
        description: "PrimeOS JavaScript Framework",
        modules: []
      };
    };

    // Run the main documentation generator
    return generatePrimeDocumentation();
  };

  // Export to Prime
  Prime.generateDocumentation = generateDocumentation;

  // Event notification
  if (Prime.EventBus && Prime.EventBus.publish) {
    Prime.EventBus.publish("module:loaded", { name: "component-documentation" });
  }
})(Prime);

// CommonJS export
module.exports = Prime;