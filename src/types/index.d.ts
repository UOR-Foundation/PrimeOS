/**
 * PrimeOS TypeScript Type Definitions
 * Version 1.0.0
 */

declare module '@uor-foundation/primeos' {
  /**
   * Main Prime object
   */
  const Prime: PrimeInstance;

  /**
   * Prime instance type
   */
  interface PrimeInstance {
    /**
     * Library version
     */
    VERSION: string;

    /**
     * Utility functions
     */
    Utils: UtilsModule;

    /**
     * Event bus for publish/subscribe patterns
     */
    EventBus: EventBusModule;

    /**
     * Logging functionality
     */
    ModuleLogger: ModuleLoggerModule;

    /**
     * Clifford algebra implementation
     */
    Clifford: CliffordModule;

    /**
     * Lie groups implementation
     */
    Lie: LieModule;

    /**
     * Coherence system
     */
    coherence: CoherenceModule;

    /**
     * Universal Object Reference system
     */
    UOR: UORModule;

    /**
     * Base0 layer of the framework architecture
     */
    Base0: Base0Module;

    /**
     * Base1 layer of the framework architecture
     */
    Base1: Base1Module;

    /**
     * Base2 layer of the framework architecture
     */
    Base2: Base2Module;

    /**
     * Base3 layer of the framework architecture
     */
    Base3: Base3Module;

    /**
     * Create a Prime framework instance
     */
    createPrimeFramework(config?: any): FrameworkInstance;

    /**
     * Create a component
     */
    createComponent(config: ComponentConfig): ComponentInstance;

    /**
     * Component registry
     */
    ComponentRegistry: ComponentRegistryModule;

    /**
     * Component factory
     */
    ComponentFactory: ComponentFactoryModule;

    /**
     * Component template
     */
    ComponentTemplate: ComponentTemplateModule;

    /**
     * Rendering functionality
     */
    render: RenderFunction;

    /**
     * Performance monitoring
     */
    performance: PerformanceModule;

    /**
     * Analytics functionality
     */
    analytic: AnalyticModule;

    /**
     * Documentation generation
     */
    generateDocumentation: GenerateDocumentationFunction;

    /**
     * Component collection
     */
    Components: ComponentsCollection;
  }

  // Placeholder for utility modules - to be expanded
  interface UtilsModule {
    isFunction(value: any): boolean;
    isObject(value: any): boolean;
    isArray(value: any): boolean;
    isString(value: any): boolean;
    isNumber(value: any): boolean;
    uuid(): string;
    deepClone<T>(obj: T): T;
    deepMerge<T, U>(target: T, source: U): T & U;
    debounce<T extends (...args: any[]) => any>(func: T, wait: number): T;
    throttle<T extends (...args: any[]) => any>(func: T, limit: number): T;
  }

  // Placeholder for event bus
  interface EventBusModule {
    publish(topic: string, data?: any): void;
    subscribe(topic: string, callback: (data: any) => void): string;
    unsubscribe(token: string): boolean;
  }

  // Placeholder for logger
  interface ModuleLoggerModule {
    create(name: string): LoggerInstance;
  }

  // Placeholder for logger instance
  interface LoggerInstance {
    debug(message: string, context?: any): void;
    info(message: string, context?: any): void;
    warn(message: string, context?: any): void;
    error(message: string, context?: any): void;
  }

  // Placeholder types - to be expanded in future versions
  type CliffordModule = any;
  type LieModule = any;
  type CoherenceModule = any;
  type UORModule = any;
  type Base0Module = any;
  type Base1Module = any;
  type Base2Module = any;
  type Base3Module = any;
  type FrameworkInstance = any;
  type ComponentConfig = any;
  type ComponentInstance = any;
  type ComponentRegistryModule = any;
  type ComponentFactoryModule = any;
  type ComponentTemplateModule = any;
  type RenderFunction = any;
  type PerformanceModule = any;
  type AnalyticModule = any;
  type GenerateDocumentationFunction = any;
  type ComponentsCollection = any;
}

// Export as ES module
export = Prime;
export as namespace Prime;