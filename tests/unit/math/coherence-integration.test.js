/**
 * PrimeOS Unit Tests - Coherence Integration
 * 
 * Tests for the CoherenceIntegration functionality that bridges 
 * mathematical components with the system-wide coherence tracking.
 */

const Prime = require('../../../src/core/prime.js');
const { CoherenceIntegration, integration } = require('../../../src/framework/math/coherence-integration.js');
const { CliffordAlgebraFiber, CoherenceGradientDescent } = require('../../../src/framework/math/coherence.js');
const { FiberAlgebraPatternRecognition } = require('../../../src/framework/math/patternRecognition.js');

// Mock Prime.coherence if needed
let originalCoherence;
beforeAll(() => {
  originalCoherence = Prime.coherence;
  
  // Create a mock systemCoherence
  Prime.coherence = {
    systemCoherence: {
      register: jest.fn().mockReturnValue(() => {}),
      calculateGlobalCoherence: jest.fn().mockReturnValue(0.75),
      optimizeGlobal: jest.fn()
    }
  };
});

afterAll(() => {
  Prime.coherence = originalCoherence;
});

describe('CoherenceIntegration', () => {
  describe('Instantiation and initialization', () => {
    test('should instantiate with default options', () => {
      const integrationInstance = new CoherenceIntegration();
      
      expect(integrationInstance).toBeDefined();
      expect(integrationInstance.registeredComponents).toEqual([]);
      expect(integrationInstance.systemCoherenceEnabled).toBe(true);
    });

    test('should handle custom options', () => {
      const integrationInstance = new CoherenceIntegration({
        enableSystemCoherence: false
      });
      
      expect(integrationInstance.systemCoherenceEnabled).toBe(false);
    });
    
    test('should detect system coherence availability', () => {
      const integrationInstance = new CoherenceIntegration();
      expect(integrationInstance.systemCoherenceAvailable).toBe(true);
      
      // Test with system coherence unavailable
      const originalSystemCoherence = Prime.coherence.systemCoherence;
      Prime.coherence.systemCoherence = undefined;
      
      const noSystemInstance = new CoherenceIntegration();
      expect(noSystemInstance.systemCoherenceAvailable).toBe(false);
      
      // Restore
      Prime.coherence.systemCoherence = originalSystemCoherence;
    });
  });
  
  describe('Component registration', () => {
    let integrationInstance;
    let mockFiber;
    let mockOptimizer;
    let mockPatternSystem;
    
    beforeEach(() => {
      integrationInstance = new CoherenceIntegration();
      
      // Create mock components
      mockFiber = {
        constructor: { name: 'CliffordAlgebraFiber' },
        computeNorm: jest.fn().mockReturnValue(0.8)
      };
      
      mockOptimizer = {
        constructor: { name: 'CoherenceGradientDescent' },
        bestCoherence: 0.2,
        encodedProblem: { constraints: [] },
        solve: jest.fn()
      };
      
      mockPatternSystem = {
        constructor: { name: 'FiberAlgebraPatternRecognition' },
        analyzeData: jest.fn().mockReturnValue({
          patterns: [{ coherence: 0.7 }],
          features: [],
          labels: [],
          nPatternsFound: 1
        })
      };
    });
    
    test('should register a fiber', () => {
      const unregister = integrationInstance.registerFiber(mockFiber);
      
      // Should have registered with system coherence
      expect(Prime.coherence.systemCoherence.register).toHaveBeenCalled();
      
      // Should have added to local tracking
      expect(integrationInstance.registeredComponents.length).toBe(1);
      expect(integrationInstance.registeredComponents[0].type).toBe('fiber');
      
      // Unregister should be a function
      expect(typeof unregister).toBe('function');
      
      // Unregister should remove from local tracking
      unregister();
      expect(integrationInstance.registeredComponents.length).toBe(0);
    });
    
    test('should register an optimizer', () => {
      const unregister = integrationInstance.registerOptimizer(mockOptimizer);
      
      // Should have registered with system coherence
      expect(Prime.coherence.systemCoherence.register).toHaveBeenCalled();
      
      // Should have added to local tracking
      expect(integrationInstance.registeredComponents.length).toBe(1);
      expect(integrationInstance.registeredComponents[0].type).toBe('optimizer');
      
      // Test the wrapper's norm method
      const wrapper = integrationInstance.registeredComponents[0].component;
      expect(wrapper.norm()).toBeCloseTo(0.8);
      
      // Test the wrapper's optimize method
      wrapper.optimize();
      expect(mockOptimizer.solve).toHaveBeenCalled();
      
      // Unregister should remove from local tracking
      unregister();
      expect(integrationInstance.registeredComponents.length).toBe(0);
    });
    
    test('should register a pattern system', () => {
      const unregister = integrationInstance.registerPatternSystem(mockPatternSystem);
      
      // Should have registered with system coherence
      expect(Prime.coherence.systemCoherence.register).toHaveBeenCalled();
      
      // Should have added to local tracking
      expect(integrationInstance.registeredComponents.length).toBe(1);
      expect(integrationInstance.registeredComponents[0].type).toBe('patternSystem');
      
      // Test the wrapper's analyze method
      const wrapper = integrationInstance.registeredComponents[0].component;
      wrapper.analyzeData([1, 2, 3]);
      expect(mockPatternSystem.analyzeData).toHaveBeenCalled();
      expect(wrapper.coherenceValues).toEqual([0.7]);
      
      // Test the wrapper's norm method
      expect(wrapper.norm()).toBeCloseTo(0.7);
      
      // Unregister should remove from local tracking
      unregister();
      expect(integrationInstance.registeredComponents.length).toBe(0);
    });
    
    test('should validate component types', () => {
      const invalidComponent = { constructor: { name: 'InvalidType' } };
      
      expect(() => {
        integrationInstance.registerFiber(invalidComponent);
      }).toThrow();
      
      expect(() => {
        integrationInstance.registerOptimizer(invalidComponent);
      }).toThrow();
      
      expect(() => {
        integrationInstance.registerPatternSystem(invalidComponent);
      }).toThrow();
    });
  });
  
  describe('Coherence calculation', () => {
    let integrationInstance;
    
    beforeEach(() => {
      integrationInstance = new CoherenceIntegration();
      
      // Register some mock components
      integrationInstance.registeredComponents = [
        {
          component: {
            norm: () => 0.8
          },
          weight: 1,
          type: 'fiber'
        },
        {
          component: {
            norm: () => 0.6
          },
          weight: 2,
          type: 'optimizer'
        },
        {
          component: {
            norm: () => 0.9
          },
          weight: 1,
          type: 'patternSystem'
        }
      ];
    });
    
    test('should calculate local coherence with weighted RMS method', () => {
      const coherence = integrationInstance.calculateLocalCoherence();
      
      // Expected: sqrt((0.8^2 * 1 + 0.6^2 * 2 + 0.9^2 * 1) / 4) = sqrt(0.725) ≈ 0.85
      expect(coherence).toBeCloseTo(0.85, 2);
    });
    
    test('should calculate local coherence with geometric mean method', () => {
      const coherence = integrationInstance.calculateLocalCoherence({
        method: 'geometric_mean'
      });
      
      // Expected: (0.8^1 * 0.6^2 * 0.9^1)^(1/4) ≈ 0.71
      expect(coherence).toBeCloseTo(0.71, 2);
    });
    
    test('should get system coherence when available', () => {
      const coherence = integrationInstance.getSystemCoherence();
      
      // Should use system coherence
      expect(Prime.coherence.systemCoherence.calculateGlobalCoherence).toHaveBeenCalled();
      expect(coherence).toBe(0.75);
    });
    
    test('should fall back to local coherence when system coherence is unavailable', () => {
      // Temporarily remove system coherence
      const originalSystemCoherence = Prime.coherence.systemCoherence;
      Prime.coherence.systemCoherence = undefined;
      
      // Create new instance without system coherence
      const localInstance = new CoherenceIntegration();
      localInstance.registeredComponents = integrationInstance.registeredComponents;
      
      const coherence = localInstance.getSystemCoherence();
      
      // Should fall back to local coherence calculation
      expect(coherence).toBeCloseTo(0.85, 2);
      
      // Restore
      Prime.coherence.systemCoherence = originalSystemCoherence;
    });
  });
  
  describe('Component optimization', () => {
    let integrationInstance;
    let mockOptimizable;
    
    beforeEach(() => {
      integrationInstance = new CoherenceIntegration();
      
      // Create a mock optimizable component
      mockOptimizable = {
        optimize: jest.fn(),
        norm: () => 0.7
      };
      
      // Register some components
      integrationInstance.registeredComponents = [
        {
          component: {
            norm: () => 0.8
          },
          weight: 1,
          type: 'fiber'
        },
        {
          component: mockOptimizable,
          weight: 1,
          type: 'optimizer'
        }
      ];
    });
    
    test('should optimize components using system optimization when available', () => {
      integrationInstance.optimizeComponents();
      
      // Should use system optimization
      expect(Prime.coherence.systemCoherence.optimizeGlobal).toHaveBeenCalled();
    });
    
    test('should fall back to local optimization when system coherence is unavailable', () => {
      // Temporarily remove system coherence
      const originalSystemCoherence = Prime.coherence.systemCoherence;
      Prime.coherence.systemCoherence = undefined;
      
      // Create new instance without system coherence
      const localInstance = new CoherenceIntegration();
      localInstance.systemCoherenceAvailable = false;
      localInstance.registeredComponents = integrationInstance.registeredComponents;
      
      localInstance.optimizeComponents({ iterations: 3 });
      
      // Should have called optimize on the optimizable component 3 times
      expect(mockOptimizable.optimize).toHaveBeenCalledTimes(3);
      
      // Restore
      Prime.coherence.systemCoherence = originalSystemCoherence;
    });
  });
  
  describe('API factory functions', () => {
    test('should provide registerFiber through API', () => {
      const mockFiber = {
        constructor: { name: 'CliffordAlgebraFiber' },
        computeNorm: jest.fn().mockReturnValue(0.8)
      };
      
      const unregister = integration.registerFiber(mockFiber);
      expect(typeof unregister).toBe('function');
    });
    
    test('should provide registerOptimizer through API', () => {
      const mockOptimizer = {
        constructor: { name: 'CoherenceGradientDescent' },
        bestCoherence: 0.2,
        encodedProblem: { constraints: [] },
        solve: jest.fn()
      };
      
      const unregister = integration.registerOptimizer(mockOptimizer);
      expect(typeof unregister).toBe('function');
    });
    
    test('should provide registerPatternSystem through API', () => {
      const mockPatternSystem = {
        constructor: { name: 'FiberAlgebraPatternRecognition' },
        analyzeData: jest.fn().mockReturnValue({
          patterns: [{ coherence: 0.7 }],
          features: [],
          labels: [],
          nPatternsFound: 1
        })
      };
      
      const unregister = integration.registerPatternSystem(mockPatternSystem);
      expect(typeof unregister).toBe('function');
    });
    
    test('should provide getSystemCoherence through API', () => {
      const coherence = integration.getSystemCoherence();
      expect(typeof coherence).toBe('number');
    });
    
    test('should provide optimizeComponents through API', () => {
      const coherence = integration.optimizeComponents({ iterations: 2 });
      expect(typeof coherence).toBe('number');
    });
  });
});