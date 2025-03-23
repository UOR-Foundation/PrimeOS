#!/usr/bin/env node
/**
 * PrimeApp Packager
 * Utility for packaging PrimeOS applications
 */

const fs = require("fs").promises;
const path = require("path");
const archiver = require("archiver");
const semver = require("semver");
const { promisify } = require("util");
const { execFile } = require("child_process");
const execFileAsync = promisify(execFile);

// Define command line arguments
const argv = require("yargs")
  .usage("Usage: $0 <command> [options]")
  .command("pack", "Package a PrimeApp", {
    dir: {
      alias: "d",
      describe: "Directory containing the PrimeApp",
      demandOption: true,
      type: "string",
    },
    output: {
      alias: "o",
      describe: "Output file",
      type: "string",
    },
    format: {
      alias: "f",
      describe: "Output format (zip, npm)",
      choices: ["zip", "npm"],
      default: "zip",
    },
  })
  .command("validate", "Validate a PrimeApp package", {
    path: {
      alias: "p",
      describe: "Path to PrimeApp package or directory",
      demandOption: true,
      type: "string",
    },
  })
  .command("init", "Initialize a new PrimeApp project", {
    name: {
      alias: "n",
      describe: "Application name",
      demandOption: true,
      type: "string",
    },
    directory: {
      alias: "d",
      describe: "Directory to create the project in",
      type: "string",
      default: ".",
    },
    template: {
      alias: "t",
      describe: "Template to use",
      choices: ["basic", "storage", "compute", "full"],
      default: "basic",
    },
  })
  .demandCommand(1, "You need to specify a command")
  .help().argv;

/**
 * Main function
 */
async function main() {
  const command = argv._[0];

  try {
    switch (command) {
      case "pack":
        await packApp(argv.dir, argv.output, argv.format);
        break;
      case "validate":
        await validateApp(argv.path);
        break;
      case "init":
        await initApp(argv.name, argv.directory, argv.template);
        break;
      default:
        console.error(`Unknown command: ${command}`);
        process.exit(1);
    }
  } catch (error) {
    console.error(`Error: ${error.message}`);
    if (error.details) {
      console.error("Details:", error.details);
    }
    process.exit(1);
  }
}

/**
 * Package a PrimeApp
 * @param {string} directory - Directory containing the PrimeApp
 * @param {string} outputFile - Output file
 * @param {string} format - Output format (zip, npm)
 */
async function packApp(directory, outputFile, format) {
  console.log(`Packaging PrimeApp from ${directory}...`);

  // Check if directory exists
  try {
    const stats = await fs.stat(directory);
    if (!stats.isDirectory()) {
      throw new Error(`${directory} is not a directory`);
    }
  } catch (error) {
    throw new Error(`Directory not found: ${directory}`);
  }

  // Check for manifest.json
  const manifestPath = path.join(directory, "manifest.json");
  let manifest;

  try {
    const manifestContent = await fs.readFile(manifestPath, "utf8");
    manifest = JSON.parse(manifestContent);
  } catch (error) {
    throw new Error(`Failed to read manifest.json: ${error.message}`);
  }

  // Validate manifest
  validateManifest(manifest);

  // Generate output filename if not provided
  if (!outputFile) {
    outputFile = `${manifest.name}-${manifest.version}`;
    switch (format) {
      case "zip":
        outputFile += ".primeapp";
        break;
      case "npm":
        outputFile = directory; // Use the directory as is for npm packaging
        break;
    }
  }

  // Package based on format
  switch (format) {
    case "zip":
      await packZip(directory, outputFile, manifest);
      break;
    case "npm":
      await packNpm(directory, outputFile, manifest);
      break;
    default:
      throw new Error(`Unknown format: ${format}`);
  }
}

/**
 * Package a PrimeApp as a ZIP file
 * @param {string} directory - Directory containing the PrimeApp
 * @param {string} outputFile - Output file
 * @param {Object} manifest - App manifest
 */
async function packZip(directory, outputFile, manifest) {
  // Create a file to stream archive data to
  const output = require("fs").createWriteStream(outputFile);
  const archive = archiver("zip", {
    zlib: { level: 9 }, // Maximum compression
  });

  // Listen for all archive data to be written
  const archiveClosedPromise = new Promise((resolve, reject) => {
    output.on("close", () => {
      resolve();
    });

    archive.on("error", (err) => {
      reject(err);
    });
  });

  // Pipe archive data to the file
  archive.pipe(output);

  // Add files from directory to the archive
  archive.directory(directory, false);

  // Finalize the archive
  await archive.finalize();

  // Wait for the archive to be fully written
  await archiveClosedPromise;

  console.log(`PrimeApp packaged successfully: ${outputFile}`);
  console.log(`Size: ${(archive.pointer() / 1024).toFixed(2)} KB`);
}

/**
 * Package a PrimeApp as an NPM package
 * @param {string} directory - Directory containing the PrimeApp
 * @param {string} outputDir - Output directory
 * @param {Object} manifest - App manifest
 */
async function packNpm(directory, outputDir, manifest) {
  // Create package.json if it doesn't exist
  const packageJsonPath = path.join(directory, "package.json");
  let packageJson;

  try {
    const packageJsonContent = await fs.readFile(packageJsonPath, "utf8");
    packageJson = JSON.parse(packageJsonContent);
  } catch (error) {
    // Create a new package.json
    packageJson = {
      name: manifest.name,
      version: manifest.version,
      description: manifest.description || `PrimeOS App: ${manifest.name}`,
      main: manifest.entry || "./app/index.js",
      author: manifest.author || "",
      license: manifest.license || "UNLICENSED",
      primeos: {
        type: "app",
        apiVersion: manifest.primeOS?.apiVersion || "1",
      },
      dependencies: manifest.dependencies || {},
    };

    // Write package.json
    await fs.writeFile(packageJsonPath, JSON.stringify(packageJson, null, 2));
  }

  // Ensure primeos field exists
  if (!packageJson.primeos) {
    packageJson.primeos = {
      type: "app",
      apiVersion: manifest.primeOS?.apiVersion || "1",
    };

    // Update package.json
    await fs.writeFile(packageJsonPath, JSON.stringify(packageJson, null, 2));
  }

  // Run npm pack
  try {
    const { stdout } = await execFileAsync("npm", ["pack"], { cwd: directory });
    console.log(
      `PrimeApp packaged successfully as NPM package: ${stdout.trim()}`,
    );
  } catch (error) {
    throw new Error(`Failed to run npm pack: ${error.message}`);
  }
}

/**
 * Validate a PrimeApp package
 * @param {string} packagePath - Path to PrimeApp package or directory
 */
async function validateApp(packagePath) {
  console.log(`Validating PrimeApp at ${packagePath}...`);

  // Check if path exists
  try {
    await fs.access(packagePath);
  } catch (error) {
    throw new Error(`Path not found: ${packagePath}`);
  }

  // Check if it's a directory or a file
  const stats = await fs.stat(packagePath);

  if (stats.isDirectory()) {
    // Validate directory
    await validateDirectory(packagePath);
  } else {
    // Validate file (ZIP or NPM package)
    const ext = path.extname(packagePath).toLowerCase();

    if (ext === ".primeapp" || ext === ".zip") {
      await validateZip(packagePath);
    } else if (ext === ".tgz" || ext === ".tar.gz") {
      await validateNpmPackage(packagePath);
    } else {
      throw new Error(`Unsupported file type: ${ext}`);
    }
  }

  console.log("Validation succeeded!");
}

/**
 * Validate a PrimeApp directory
 * @param {string} directory - Directory to validate
 */
async function validateDirectory(directory) {
  // Check for required files and directories
  const requiredFiles = ["manifest.json"];
  const errors = [];

  for (const file of requiredFiles) {
    try {
      await fs.access(path.join(directory, file));
    } catch (error) {
      errors.push(`Missing required file: ${file}`);
    }
  }

  if (errors.length > 0) {
    throw new Error(`Validation failed:\n${errors.join("\n")}`);
  }

  // Read and validate manifest
  const manifestPath = path.join(directory, "manifest.json");
  let manifest;

  try {
    const manifestContent = await fs.readFile(manifestPath, "utf8");
    manifest = JSON.parse(manifestContent);
  } catch (error) {
    throw new Error(`Failed to read manifest.json: ${error.message}`);
  }

  validateManifest(manifest);

  // Check entry point
  const entryPath = path.resolve(directory, manifest.entry || "./app/index.js");

  try {
    await fs.access(entryPath);
  } catch (error) {
    throw new Error(`Entry point not found: ${entryPath}`);
  }

  // Check coherence files if specified
  if (manifest.coherence) {
    if (manifest.coherence.boundaries) {
      const boundariesPath = path.resolve(
        directory,
        manifest.coherence.boundaries,
      );

      try {
        await fs.access(boundariesPath);
      } catch (error) {
        throw new Error(
          `Coherence boundaries file not found: ${boundariesPath}`,
        );
      }
    }

    if (manifest.coherence.validators) {
      const validatorsPath = path.resolve(
        directory,
        manifest.coherence.validators,
      );

      try {
        await fs.access(validatorsPath);
      } catch (error) {
        throw new Error(
          `Coherence validators file not found: ${validatorsPath}`,
        );
      }
    }

    if (manifest.coherence.resolvers) {
      const resolversPath = path.resolve(
        directory,
        manifest.coherence.resolvers,
      );

      try {
        await fs.access(resolversPath);
      } catch (error) {
        throw new Error(`Coherence resolvers file not found: ${resolversPath}`);
      }
    }
  }

  // Check schema registry if specified
  if (manifest.schemas && manifest.schemas.registry) {
    const registryPath = path.resolve(directory, manifest.schemas.registry);

    try {
      await fs.access(registryPath);
    } catch (error) {
      throw new Error(`Schema registry file not found: ${registryPath}`);
    }
  }
}

/**
 * Validate a PrimeApp ZIP package
 * @param {string} zipFile - Path to ZIP file
 */
async function validateZip(zipFile) {
  // In a real implementation, we would:
  // 1. Extract the ZIP to a temporary directory
  // 2. Call validateDirectory with the extracted directory
  // 3. Clean up the temporary directory when done

  console.log("ZIP validation not implemented in this demo.");
  console.log(
    "In a real implementation, we would extract the ZIP and validate its contents.",
  );
}

/**
 * Validate a PrimeApp NPM package
 * @param {string} npmPackage - Path to NPM package
 */
async function validateNpmPackage(npmPackage) {
  // In a real implementation, we would:
  // 1. Extract the NPM package to a temporary directory
  // 2. Call validateDirectory with the extracted directory
  // 3. Clean up the temporary directory when done

  console.log("NPM package validation not implemented in this demo.");
  console.log(
    "In a real implementation, we would extract the package and validate its contents.",
  );
}

/**
 * Validate a PrimeApp manifest
 * @param {Object} manifest - Manifest to validate
 */
function validateManifest(manifest) {
  const errors = [];

  // Check required fields
  const requiredFields = ["name", "version"];

  for (const field of requiredFields) {
    if (!manifest[field]) {
      errors.push(`Missing required field: ${field}`);
    }
  }

  // Check name format
  if (manifest.name && !/^[a-z0-9_\-]+$/.test(manifest.name)) {
    errors.push(
      `Invalid app name format: ${manifest.name} (must contain only lowercase letters, numbers, underscore, and hyphen)`,
    );
  }

  // Check version format (semver)
  if (manifest.version && !semver.valid(manifest.version)) {
    errors.push(
      `Invalid version format: ${manifest.version} (must be a valid semver version)`,
    );
  }

  // Check permissions if they exist
  if (manifest.permissions && Array.isArray(manifest.permissions)) {
    const validPermissions = [
      "storage",
      "network",
      "compute",
      "memory",
      "notification",
      "background",
      "system",
      "user",
      "gpu",
    ];

    for (const permission of manifest.permissions) {
      if (!validPermissions.includes(permission)) {
        errors.push(`Unknown permission requested: ${permission}`);
      }
    }
  }

  // Check interfaces
  if (manifest.interfaces) {
    if (
      manifest.interfaces.provides &&
      !Array.isArray(manifest.interfaces.provides)
    ) {
      errors.push("interfaces.provides must be an array");
    }

    if (
      manifest.interfaces.consumes &&
      !Array.isArray(manifest.interfaces.consumes)
    ) {
      errors.push("interfaces.consumes must be an array");
    }
  }

  // Check resources format
  if (manifest.resources) {
    if (manifest.resources.storage) {
      if (
        manifest.resources.storage.persistent !== undefined &&
        typeof manifest.resources.storage.persistent !== "boolean"
      ) {
        errors.push("resources.storage.persistent must be a boolean");
      }

      if (
        manifest.resources.storage.temporary &&
        typeof manifest.resources.storage.temporary !== "string"
      ) {
        errors.push(
          'resources.storage.temporary must be a string (e.g., "10MB")',
        );
      }

      if (
        manifest.resources.storage.persistent &&
        typeof manifest.resources.storage.persistent !== "string" &&
        typeof manifest.resources.storage.persistent !== "boolean"
      ) {
        errors.push(
          'resources.storage.persistent must be a string (e.g., "1MB") or boolean',
        );
      }
    }

    if (manifest.resources.compute) {
      if (
        manifest.resources.compute.priority &&
        !["low", "normal", "high"].includes(manifest.resources.compute.priority)
      ) {
        errors.push(
          "resources.compute.priority must be one of: low, normal, high",
        );
      }

      if (
        manifest.resources.compute.background !== undefined &&
        typeof manifest.resources.compute.background !== "boolean"
      ) {
        errors.push("resources.compute.background must be a boolean");
      }
    }

    if (
      manifest.resources.memory &&
      manifest.resources.memory.max &&
      typeof manifest.resources.memory.max !== "string"
    ) {
      errors.push('resources.memory.max must be a string (e.g., "50MB")');
    }
  }

  // Report validation errors
  if (errors.length > 0) {
    throw new Error(`Manifest validation failed:\n${errors.join("\n")}`);
  }
}

/**
 * Initialize a new PrimeApp project
 * @param {string} name - Application name
 * @param {string} directory - Directory to create the project in
 * @param {string} template - Template to use
 */
async function initApp(name, directory, template) {
  console.log(`Initializing new PrimeApp: ${name} (${template} template)...`);

  // Create directory if it doesn't exist
  const appDirectory = path.resolve(directory, name);

  try {
    await fs.mkdir(appDirectory, { recursive: true });
  } catch (error) {
    throw new Error(`Failed to create directory: ${error.message}`);
  }

  // Create basic structure
  await createBasicStructure(appDirectory, name, template);

  console.log(`PrimeApp ${name} initialized successfully in ${appDirectory}`);
  console.log("Next steps:");
  console.log("  1. cd", appDirectory);
  console.log("  2. Implement your application logic in app/index.js");
  console.log("  3. Run the packager to create a distributable package:");
  console.log(
    `     node ${path.relative(appDirectory, __filename)} pack -d . -f zip`,
  );
}

/**
 * Create basic PrimeApp structure
 * @param {string} directory - Directory to create the structure in
 * @param {string} name - Application name
 * @param {string} template - Template to use
 */
async function createBasicStructure(directory, name, template) {
  // Create directories
  const directories = [
    "app",
    "app/components",
    "app/resources",
    "schema",
    "schema/types",
    "coherence",
    "styles",
    "docs",
  ];

  for (const dir of directories) {
    await fs.mkdir(path.join(directory, dir), { recursive: true });
  }

  // Create manifest.json
  const manifest = {
    name,
    displayName:
      name.charAt(0).toUpperCase() +
      name.slice(1).replace(/-([a-z])/g, (g) => " " + g[1].toUpperCase()),
    version: "1.0.0",
    primeOS: {
      version: ">=1.0.0",
      apiVersion: "1",
    },
    entry: "./app/index.js",
    description: `A PrimeOS ${template} application`,
    author: "",
    license: "MIT",
    dependencies: {},
    resources: {
      storage: {
        persistent: "1MB",
        temporary: "10MB",
      },
      compute: {
        priority: "normal",
        background: true,
      },
      memory: {
        max: "50MB",
      },
    },
    permissions: ["storage"],
    interfaces: {
      provides: [],
      consumes: [],
    },
    coherence: {
      boundaries: "./coherence/boundaries.json",
      validators: "./coherence/validators.js",
      resolvers: "./coherence/resolvers.js",
      minThreshold: 0.7,
    },
    schemas: {
      registry: "./schema/index.js",
    },
  };

  // Adjust manifest based on template
  switch (template) {
    case "storage":
      manifest.interfaces.provides.push("data-storage");
      manifest.permissions.push("storage");
      break;
    case "compute":
      manifest.interfaces.provides.push("data-processor");
      manifest.permissions.push("compute");
      break;
    case "full":
      manifest.interfaces.provides.push(
        "data-storage",
        "data-processor",
        "visualization",
      );
      manifest.permissions.push("storage", "compute", "network");
      break;
  }

  await fs.writeFile(
    path.join(directory, "manifest.json"),
    JSON.stringify(manifest, null, 2),
  );

  // Create app/index.js
  const appClass = `/**
 * ${manifest.displayName}
 * A PrimeOS ${template} application
 */

import { PrimeApplication } from 'primeos/veneer';

export default class ${toPascalCase(name)} extends PrimeApplication {
  async init() {
    // Initialize application resources
    console.log('Initializing ${manifest.displayName}');
    
    // Request storage if needed
    this.storage = await this.getResource('storage', {
      persistent: true
    });
    
    // Initialize application state
    this.state = {
      initialized: false,
      data: {}
    };
  }
  
  async start() {
    // Start the application
    console.log('Starting ${manifest.displayName}');
    
    // Initialize components
    
    // Set initialized state
    this.state.initialized = true;
  }
  
  async pause() {
    // Pause application activities
    console.log('Pausing ${manifest.displayName}');
  }
  
  async resume() {
    // Resume application activities
    console.log('Resuming ${manifest.displayName}');
  }
  
  async stop() {
    // Stop and clean up resources
    console.log('Stopping ${manifest.displayName}');
    
    // Release resources
    await this.releaseResource('storage');
  }
  
  // Application-specific methods
  async processData(data) {
    // Example method
    return data;
  }
  
  calculateCoherence() {
    // Custom coherence calculation
    return 0.9;
  }
}
`;

  await fs.writeFile(path.join(directory, "app", "index.js"), appClass);

  // Create coherence/boundaries.json
  const boundaries = {
    internal: {
      modules: [],
      threshold: 0.85,
    },
    external: {
      inputs: {},
      outputs: {},
    },
  };

  // Adjust boundaries based on template
  switch (template) {
    case "storage":
      boundaries.internal.modules.push("dataStorage");
      boundaries.external.inputs.data = {
        type: "rawData",
        validators: ["dataValidator"],
      };
      boundaries.external.outputs.storedData = {
        type: "storedData",
        coherence: {
          preserves: ["data.integrity"],
          enhances: ["data.accessibility"],
        },
      };
      break;
    case "compute":
      boundaries.internal.modules.push("dataProcessor");
      boundaries.external.inputs.data = {
        type: "dataStream",
        validators: ["dataStreamValidator"],
      };
      boundaries.external.outputs.processedData = {
        type: "dataResult",
        coherence: {
          preserves: ["data.integrity", "data.dimensions"],
          enhances: ["data.precision"],
        },
      };
      break;
    case "full":
      boundaries.internal.modules.push(
        "dataStorage",
        "dataProcessor",
        "visualizer",
      );
      boundaries.external.inputs.data = {
        type: "dataStream",
        validators: ["dataStreamValidator"],
      };
      boundaries.external.outputs.processedData = {
        type: "dataResult",
        coherence: {
          preserves: ["data.integrity", "data.dimensions"],
          enhances: ["data.precision", "data.visualization"],
        },
      };
      break;
  }

  await fs.writeFile(
    path.join(directory, "coherence", "boundaries.json"),
    JSON.stringify(boundaries, null, 2),
  );

  // Create coherence/validators.js
  const validators = `/**
 * ${manifest.displayName} Coherence Validators
 */

import { Validator } from 'primeos/coherence';

export class DataValidator extends Validator {
  validate(data) {
    // Custom validation logic
    const isValid = data !== null && data !== undefined;
    const coherenceScore = isValid ? 0.9 : 0;
    
    return {
      valid: isValid,
      score: coherenceScore,
      details: isValid ? null : "Invalid data format"
    };
  }
}

export class DataStreamValidator extends Validator {
  validate(dataStream) {
    // Custom validation logic for data streams
    const isValid = dataStream && Array.isArray(dataStream.points);
    const coherenceScore = isValid ? this.calculateCoherence(dataStream) : 0;
    
    return {
      valid: isValid,
      score: coherenceScore,
      details: isValid ? null : "Invalid data stream format"
    };
  }
  
  calculateCoherence(dataStream) {
    // Example coherence calculation logic
    // A real implementation would analyze the data properties
    return 0.9;
  }
}
`;

  await fs.writeFile(
    path.join(directory, "coherence", "validators.js"),
    validators,
  );

  // Create coherence/resolvers.js
  const resolvers = `/**
 * ${manifest.displayName} Coherence Resolvers
 */

import { Resolver } from 'primeos/coherence';

export class DataConflictResolver extends Resolver {
  async resolve(conflict) {
    // Conflict resolution strategy
    const { local, remote, path } = conflict;
    
    // Example: merge strategies based on data type
    if (Array.isArray(local) && Array.isArray(remote)) {
      return this.mergeArrays(local, remote);
    }
    
    // Default to most recent version
    return conflict.timestamps.local > conflict.timestamps.remote 
      ? local 
      : remote;
  }
  
  mergeArrays(local, remote) {
    // Custom array merging logic
    // This is a simple example - real implementations would be more sophisticated
    return [...new Set([...local, ...remote])];
  }
}
`;

  await fs.writeFile(
    path.join(directory, "coherence", "resolvers.js"),
    resolvers,
  );

  // Create schema/index.js
  const schema = `/**
 * ${manifest.displayName} Schema Registry
 */

import { SchemaRegistry, Type } from 'primeos/schema';

const registry = new SchemaRegistry({
  namespace: '${name}',
  version: '1.0.0'
});

// Define application data schemas
registry.define('DataPoint', {
  type: Type.Object,
  properties: {
    timestamp: { type: Type.Number },
    value: { type: Type.Number },
    label: { type: Type.String, optional: true }
  }
});

registry.define('DataSeries', {
  type: Type.Array,
  items: { type: Type.Reference, ref: 'DataPoint' }
});

export default registry;
`;

  await fs.writeFile(path.join(directory, "schema", "index.js"), schema);

  // Create a README.md
  const readme = `# ${manifest.displayName}

${manifest.description}

## Overview

This is a PrimeOS application built using the PrimeApp format.

## Getting Started

1. Install dependencies:
   \`\`\`
   npm install
   \`\`\`

2. Build the application:
   \`\`\`
   npm run build
   \`\`\`

3. Package the application:
   \`\`\`
   node ${path.relative(directory, __filename)} pack -d . -f zip
   \`\`\`

## License

${manifest.license}
`;

  await fs.writeFile(path.join(directory, "README.md"), readme);
}

/**
 * Convert a string to PascalCase
 * @param {string} str - String to convert
 * @returns {string} - PascalCase string
 */
function toPascalCase(str) {
  return str
    .replace(/[-_](.)/g, (_, c) => c.toUpperCase())
    .replace(/^(.)/, (_, c) => c.toUpperCase());
}

// Run the main function
main();
