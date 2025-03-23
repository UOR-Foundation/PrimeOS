/**
 * Unit tests for PrimeOS Framework - Base2 components
 */

const Prime = require("../../../src");
const { assertions, mocking } = require("../../utils");

describe("PrimeOS Framework - Base2", () => {
  let base0;
  let base1;

  beforeEach(() => {
    // Create Base 0 components
    base0 = Prime.Base0.createBase0Components();

    // Connect Base 1 to Base 0
    base1 = Prime.Base1.connectToBase0(base0);
  });

  describe("ResourceClient", () => {
    test("creates a resource client with correct properties", () => {
      // Create Resource Client
      const resourceClient = Prime.Base2.createResourceClient(base1);

      // Test properties
      expect(resourceClient.type).toBe("resourceClient");
      expect(resourceClient.runtime).toBeDefined();
      expect(resourceClient.observation).toBeDefined();
      expect(resourceClient.interaction).toBeDefined();
      expect(resourceClient.representation).toBeDefined();

      // Test getters
      expect(resourceClient.getRuntime()).toBe(base1.runtime);
      expect(resourceClient.getObservation()).toBe(base1.observation);
      expect(resourceClient.getInteraction()).toBe(base1.interaction);
      expect(resourceClient.getRepresentation()).toBe(base1.representation);

      // Mock the Base 1 components with spies
      const originalStart = base1.runtime.start;
      const originalRun = base1.runtime.run;
      const originalStop = base1.runtime.stop;

      let startCalled = false;
      let runCalled = false;
      let stopCalled = false;

      base1.runtime.start = function () {
        startCalled = true;
        return { _running: true };
      };

      base1.runtime.run = function () {
        runCalled = true;
        return "result";
      };

      base1.runtime.stop = function () {
        stopCalled = true;
        return true;
      };

      // Test delegated methods
      resourceClient.startModel({});
      expect(startCalled).toBe(true);

      resourceClient.runModel({}, "input");
      expect(runCalled).toBe(true);

      resourceClient.stopModel({});
      expect(stopCalled).toBe(true);

      // Restore original methods
      base1.runtime.start = originalStart;
      base1.runtime.run = originalRun;
      base1.runtime.stop = originalStop;
    });
  });

  describe("ApplicationManager", () => {
    test("creates an application manager with correct functionality", () => {
      // Create Application Manager
      const applicationManager = Prime.Base2.createApplicationManager({});

      // Test properties
      expect(applicationManager.type).toBe("applicationManager");
      expect(applicationManager.bundles.length).toBe(0);

      // Create a test bundle
      const bundle = {
        id: "testBundle",
        name: "Test Bundle",
        version: "1.0.0",
        initialState: { count: 0 },
        models: {
          counter: {
            process: (value) => value + 1,
          },
        },
      };

      // Test loadBundle function
      applicationManager.loadBundle(bundle);
      expect(applicationManager.bundles.length).toBe(1);

      // Test getBundle function
      const retrievedBundle = applicationManager.getBundle("testBundle");
      expect(retrievedBundle.id).toBe("testBundle");

      // Test startApplication function
      const app = applicationManager.startApplication("testBundle", {
        appId: "testApp",
      });
      expect(app.id).toBe("testApp");
      expect(app.bundle.id).toBe("testBundle");

      // Test getApplication function
      const retrievedApp = applicationManager.getApplication("testApp");
      expect(retrievedApp.id).toBe("testApp");

      // Test stopApplication function
      const stopped = applicationManager.stopApplication("testApp");
      expect(stopped).toBe(true);

      // Test getRunningApplications function
      const runningApps = applicationManager.getRunningApplications();
      expect(Object.keys(runningApps).length).toBe(0);

      // Test unloadBundle function
      applicationManager.unloadBundle("testBundle");
      expect(applicationManager.bundles.length).toBe(0);

      // Test loadBundle throws for invalid bundle
      expect(() => {
        applicationManager.loadBundle({});
      }).toThrow(Prime.ValidationError);

      // Test getBundle throws for nonexistent bundle
      expect(() => {
        applicationManager.getBundle("nonexistent");
      }).toThrow(Prime.InvalidOperationError);
    });
  });

  describe("SystemManager", () => {
    test("creates a system manager with correct functionality", () => {
      // Create System Manager
      const systemManager = Prime.Base2.createSystemManager({});

      // Test properties
      expect(systemManager.type).toBe("systemManager");

      // Test allocateMemory function
      const memory = systemManager.allocateMemory(1024);
      expect(memory.address).toBeDefined();
      expect(memory.size).toBe(1024);

      // Test freeMemory function
      const freed = systemManager.freeMemory(memory.address);
      expect(freed).toBe(true);

      // Test allocateResource function
      const resource = systemManager.allocateResource("database", {
        url: "test://db",
      });
      expect(resource.address).toBeDefined();
      expect(resource.type).toBe("database");
      expect(resource.config.url).toBe("test://db");

      // Test freeResource function
      const resourceFreed = systemManager.freeResource(resource.address);
      expect(resourceFreed).toBe(true);

      // Test getResourceUsage function
      const usage = systemManager.getResourceUsage();
      expect(usage.memory).toBeDefined();
      expect(usage.byType).toBeDefined();

      // Test allocateMemory throws for invalid size
      expect(() => {
        systemManager.allocateMemory(-1);
      }).toThrow(Prime.ValidationError);

      // Test freeMemory throws for invalid address
      expect(() => {
        systemManager.freeMemory("nonexistent");
      }).toThrow(Prime.InvalidOperationError);
    });

    test("correctly implements CIDR IP matching", () => {
      const systemManager = Prime.Base2.createSystemManager({
        security: {
          policy: {
            test: {
              networkRestrictions: {
                allowedIPs: [
                  "192.168.1.0/24",
                  "10.0.0.0/8",
                  "172.16.0.0/12",
                  "127.0.0.1",
                  "192.168.2.*",
                ],
                blockedIPs: [
                  "192.168.1.128/25", // Block second half of 192.168.1.0/24
                  "10.1.2.3",
                ],
              },
            },
          },
        },
      });

      // Test exact IP match
      expect(systemManager._checkIPInRange("127.0.0.1", ["127.0.0.1"])).toBe(
        true,
      );

      // Test IP not in list
      expect(
        systemManager._checkIPInRange("8.8.8.8", ["127.0.0.1", "10.0.0.1"]),
      ).toBe(false);

      // Test wildcard notation
      expect(
        systemManager._checkIPInRange("192.168.2.42", ["192.168.2.*"]),
      ).toBe(true);

      // Test CIDR notation
      expect(
        systemManager._checkIPInRange("192.168.1.42", ["192.168.1.0/24"]),
      ).toBe(true);
      expect(systemManager._checkIPInRange("10.20.30.40", ["10.0.0.0/8"])).toBe(
        true,
      );
      expect(
        systemManager._checkIPInRange("192.168.2.1", ["192.168.1.0/24"]),
      ).toBe(false);

      // Test edge cases
      expect(
        systemManager._checkIPInRange("192.168.1.42", ["192.168.1.42/32"]),
      ).toBe(true);
      expect(systemManager._checkIPInRange("0.0.0.0", ["0.0.0.0/0"])).toBe(
        true,
      );
      expect(
        systemManager._checkIPInRange("255.255.255.255", ["0.0.0.0/0"]),
      ).toBe(true);

      // Test IP to int conversion
      expect(systemManager._ipToInt("192.168.1.1")).toBe(3232235777);
      expect(systemManager._ipToInt("0.0.0.0")).toBe(0);
      expect(systemManager._ipToInt("255.255.255.255")).toBe(4294967295);
      expect(systemManager._ipToInt("invalid.ip")).toBeNull();
    });
  });

  describe("Syscalls", () => {
    test("registers and uses syscalls correctly", () => {
      // Clear existing syscalls
      Prime.Base2.syscalls = {};

      // Register syscalls
      Prime.Base2.registerSyscalls([
        { name: "echo", handler: (value) => value },
        { name: "add", handler: (a, b) => a + b },
      ]);

      // Test syscall function
      const echoed = Prime.Base2.syscall("echo", "hello");
      expect(echoed).toBe("hello");

      const sum = Prime.Base2.syscall("add", 2, 3);
      expect(sum).toBe(5);

      // Test syscall throws for nonexistent syscall
      expect(() => {
        Prime.Base2.syscall("nonexistent");
      }).toThrow(Prime.InvalidOperationError);
    });
  });

  describe("ConnectToBase1", () => {
    test("connects base2 components to base1 correctly", () => {
      // Connect Base 2 to Base 1
      const base2 = Prime.Base2.connectToBase1(base1);

      // Test all components exist
      expect(base2.resourceClient).toBeDefined();
      expect(base2.applicationManager).toBeDefined();
      expect(base2.systemManager).toBeDefined();

      // Test resourceClient is connected
      expect(base2.resourceClient.runtime).toBe(base1.runtime);
      expect(base2.resourceClient.observation).toBe(base1.observation);
      expect(base2.resourceClient.interaction).toBe(base1.interaction);
      expect(base2.resourceClient.representation).toBe(base1.representation);
    });
  });
});
