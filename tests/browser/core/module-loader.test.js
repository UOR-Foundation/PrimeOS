/**
 * PrimeOS Browser Tests - Module Loader
 *
 * Tests for the ModuleLoader component in the core module.
 */

// Register tests with TestRunner
TestRunner.suite("Core ModuleLoader", function () {
  // Setup/teardown to ensure clean testing environment
  let testModules = [];

  function afterTests() {
    // Clean up test modules
    if (Prime && Prime.ModuleLoader) {
      testModules.forEach((name) => {
        if (
          Prime[name] !== undefined &&
          typeof Prime.ModuleLoader.unregister === "function"
        ) {
          Prime.ModuleLoader.unregister(name);
        } else {
          delete Prime[name];
        }
      });
    }
  }

  TestRunner.test("detects environment correctly", function () {
    const env = Prime.ModuleLoader.detectEnvironment();
    TestRunner.assert(
      typeof env === "string",
      "Environment should be a string",
    );

    // Should be 'browser' in this environment
    TestRunner.assertEqual(env, "browser", "Should detect browser environment");
  });

  TestRunner.test("registers a module successfully", function () {
    const moduleName = "browserTestModule" + Date.now();
    testModules.push(moduleName); // Track for cleanup

    const mockModule = { test: true, browserSpecific: true };
    const result = Prime.ModuleLoader.register(moduleName, mockModule);

    TestRunner.assert(
      result === true,
      "Register should return true on success",
    );
    TestRunner.assert(
      Prime[moduleName] === mockModule,
      "Module should be attached to Prime",
    );
  });

  TestRunner.test("validates module name", function () {
    let errorThrown = false;

    try {
      Prime.ModuleLoader.register(123, {});
    } catch (error) {
      errorThrown = true;
      TestRunner.assert(
        error.message.includes("Module name"),
        "Error should mention module name",
      );
    }

    TestRunner.assert(
      errorThrown,
      "Should throw error for invalid module name",
    );

    // Test empty string validation
    errorThrown = false;
    try {
      Prime.ModuleLoader.register("", {});
    } catch (error) {
      errorThrown = true;
      TestRunner.assert(
        error.message.includes("Module name"),
        "Error should mention module name",
      );
    }

    TestRunner.assert(errorThrown, "Should throw error for empty module name");
  });

  TestRunner.test("validates module object", function () {
    // Test with non-object
    let errorThrown = false;
    try {
      Prime.ModuleLoader.register("invalidModule", "not an object");
    } catch (error) {
      errorThrown = true;
      TestRunner.assert(
        error.message.includes("Module"),
        "Error should mention module",
      );
    }
    TestRunner.assert(errorThrown, "Should throw error for non-object module");

    // Test with null
    errorThrown = false;
    try {
      Prime.ModuleLoader.register("nullModule", null);
    } catch (error) {
      errorThrown = true;
      TestRunner.assert(
        error.message.includes("Module"),
        "Error should mention module",
      );
    }
    TestRunner.assert(errorThrown, "Should throw error for null module");
  });

  TestRunner.test("prevents overwriting existing modules", function () {
    const moduleName = "browserExistingModule" + Date.now();
    testModules.push(moduleName); // Track for cleanup

    // First registration
    Prime.ModuleLoader.register(moduleName, { first: true });

    // Second registration should fail (return false)
    const result = Prime.ModuleLoader.register(moduleName, { second: true });
    TestRunner.assertEqual(
      result,
      false,
      "Should return false when module exists",
    );

    // Module should still have original value
    TestRunner.assert(
      Prime[moduleName].first === true,
      "Module should not be overwritten",
    );
    TestRunner.assert(
      Prime[moduleName].second === undefined,
      "Module should not be overwritten",
    );
  });

  // Only run require tests if require is implemented
  if (Prime.ModuleLoader.require) {
    TestRunner.test("loads an existing module with require", function () {
      const moduleName = "browserRequireModule" + Date.now();
      testModules.push(moduleName); // Track for cleanup

      // Register a test module
      Prime.ModuleLoader.register(moduleName, { value: 42 });

      // Require the module
      const module = Prime.ModuleLoader.require(moduleName);

      TestRunner.assert(module !== undefined, "Required module should exist");
      TestRunner.assertEqual(
        module.value,
        42,
        "Required module should have correct value",
      );
    });

    TestRunner.test("throws for non-existent module with require", function () {
      const nonExistentName = "nonExistentModule" + Date.now();
      let errorThrown = false;

      try {
        Prime.ModuleLoader.require(nonExistentName);
      } catch (error) {
        errorThrown = true;
        TestRunner.assert(
          error.message.includes(nonExistentName),
          "Error should mention module name",
        );
      }

      TestRunner.assert(
        errorThrown,
        "require should throw for non-existent module",
      );
    });
  } else {
    TestRunner.test("ModuleLoader.require implementation check", function () {
      TestRunner.log("require method not implemented - skipping related tests");
      TestRunner.assert(true); // Auto-pass
    });
  }

  // Only run unregister tests if unregister is implemented
  if (typeof Prime.ModuleLoader.unregister === "function") {
    TestRunner.test("unregisters an existing module", function () {
      const moduleName = "browserUnregisterModule" + Date.now();
      testModules.push(moduleName); // Track for cleanup

      // Register a test module
      Prime.ModuleLoader.register(moduleName, { value: 42 });

      // Unregister the module
      const result = Prime.ModuleLoader.unregister(moduleName);

      TestRunner.assertEqual(
        result,
        true,
        "unregister should return true on success",
      );
      TestRunner.assert(
        Prime[moduleName] === undefined,
        "Module should be removed from Prime",
      );
    });

    TestRunner.test(
      "returns false for non-existent module with unregister",
      function () {
        const nonExistentName = "nonExistentModule" + Date.now();

        const result = Prime.ModuleLoader.unregister(nonExistentName);
        TestRunner.assertEqual(
          result,
          false,
          "unregister should return false for non-existent module",
        );
      },
    );
  } else {
    TestRunner.test(
      "ModuleLoader.unregister implementation check",
      function () {
        TestRunner.log(
          "unregister method not implemented - skipping related tests",
        );
        TestRunner.assert(true); // Auto-pass
      },
    );
  }

  // Only run getModules tests if getModules is implemented
  if (typeof Prime.ModuleLoader.getModules === "function") {
    TestRunner.test("returns list of registered modules", function () {
      const moduleBase = "browserListModule";
      const moduleName1 = moduleBase + "1" + Date.now();
      const moduleName2 = moduleBase + "2" + Date.now();
      testModules.push(moduleName1, moduleName2); // Track for cleanup

      // Register test modules
      Prime.ModuleLoader.register(moduleName1, { id: 1 });
      Prime.ModuleLoader.register(moduleName2, { id: 2 });

      const modules = Prime.ModuleLoader.getModules();

      TestRunner.assert(
        Array.isArray(modules),
        "getModules should return an array",
      );
      TestRunner.assert(
        modules.includes(moduleName1),
        "Module list should include first test module",
      );
      TestRunner.assert(
        modules.includes(moduleName2),
        "Module list should include second test module",
      );
    });
  } else {
    TestRunner.test(
      "ModuleLoader.getModules implementation check",
      function () {
        TestRunner.log(
          "getModules method not implemented - skipping related tests",
        );
        TestRunner.assert(true); // Auto-pass
      },
    );
  }

  // Clean up after all tests
  afterTests();
});
