# PrimeOS Repository Structure and Management

## Overview

The PrimeOS repository is structured as a self-referential system where the tools used to manage and interact with the system are themselves defined by PrimeOS models. This document outlines the repository organization, documentation approach, and the recursive implementation pattern that enables the system to be self-documenting and self-verifying.

## Repository Organization

### MCP Server and Management API

- **Repository MCP Server**: Located in the `.github/mcp` directory, this serves as the main API for managing PrimeOS within the local-repo context. The MCP server provides an LLM interface to interact with the repository's management API.

- **Management API**: Located in the `.github/scripts` directory (to be renamed to `.github/lib`), this hosts the repository's management API that the MCP server provides the LLM interface for.

- **Recursive Implementation Pattern**: The MCP server implementation is declared in the repository using PrimeOS models, but implemented in the hidden GitHub directory. The scripts in the GitHub namespace are validated and defined by their PrimeOS models, creating a self-referential system.

- **Local Platform Implementation**: The `.github` directory serves as an implementation of PrimeOS for local platforms, demonstrating how the abstract models can be concretely realized.

### Obsidian Vault Integration

The entire repository is intended to be initialized as an Obsidian vault, providing a knowledge management system that enhances documentation and navigation:

- **Note Indexing**: The vault indexes notes in each directory in the repository (outside of the `.github` folder).

- **Templated Content**: Each directory contains the same templated content structure, ensuring consistency across the repository.

- **Interconnected Documentation**: Notes link to other notes and artifacts within the repo, creating a web of relationships that mirrors the system's architecture.

## Documentation Structure

### Note Organization

Each note in the repository serves multiple purposes:

1. **Feature Definition**: Defines the features of its directory
2. **Implementation Links**: Links to the implementation code
3. **Dependency Tracking**: Documents the implementation's dependencies
4. **Test References**: Links to the tests for the implementation
5. **Cross-References**: Links to other related notes and artifacts

### Feature Documentation

- **Gherkin Syntax**: Note features are written in Gherkin syntax, providing a structured way to describe behavior in a human-readable format while maintaining machine parseability.

- **Schema-Defined Components**: All schemas used for features, tests, notes, and other components are defined in the repository's schema, ensuring consistency and validation.

## Testing Approach

- **JSON-Based Testing**: Tests are written in JSON format, maintaining the declarative nature of the entire system.

- **MCP Server Execution**: Tests are called and executed through the MCP server, providing a consistent interface for test execution.

## Self-Referential System Architecture

The PrimeOS repository implements a recursive meta-architecture where:

1. **Models Define Tools**: The tools used to manage the system (MCP server, management API) are themselves defined by PrimeOS models.

2. **Tools Implement Models**: The implementation of these tools in the `.github` directory follows the specifications defined by their models.

3. **Tools Validate Against Models**: The scripts and server implementations are validated against their corresponding PrimeOS models, ensuring consistency.

4. **Tools Manage Models**: These same tools are used to manage, validate, and interact with the rest of the PrimeOS models in the repository.

This creates a closed loop where the system can validate and manage itself, embodying the principle of recursive self-description mentioned in the core PrimeOS concepts.

## Benefits of This Approach

- **Consistency**: Ensures alignment between the tools and the system they manage
- **Validation**: Provides a clear validation path for the MCP server and management scripts
- **Self-Documentation**: The system documents itself through its interconnected notes and models
- **Clean Separation**: Maintains separation between model definitions and implementations while preserving their relationship
- **Extensibility**: New components can be added by following the same pattern of model definition and implementation

## Conclusion

The PrimeOS repository structure demonstrates a practical application of the core principles outlined in the UOR framework. By implementing a self-referential system where tools are defined by the same models they manage, PrimeOS achieves a high degree of consistency, validation, and self-documentation. The integration with Obsidian as a knowledge management system further enhances these capabilities, creating a comprehensive environment for developing, documenting, and managing the PrimeOS ecosystem.

---

© UOR Foundation - MIT License
