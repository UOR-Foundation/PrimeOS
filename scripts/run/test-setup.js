// Test setup for extreme conditions
process.env.NODE_ENV = "test";
process.env.EXTENDED_PRECISION = "true";
process.env.EXTREME_TESTING = "true";

// Configure global Math helpers if needed
if (!Math.nextafter) {
  // Add nextafter implementation for ULP-based testing
  // This is a simplified implementation for testing
  Math.nextafter = function (x, y) {
    if (x === y) return y;

    // Convert to IEEE-754 representation
    const buffer = new ArrayBuffer(8);
    const bytes = new Uint8Array(buffer);
    const doubles = new Float64Array(buffer);

    doubles[0] = x;

    // Increment or decrement the bit pattern based on direction
    const sign = y > x ? 1 : -1;

    // Handle special cases
    if (!Number.isFinite(x)) return x;

    if (x === 0) {
      // Handle positive/negative zero
      if (sign > 0) {
        return Number.MIN_VALUE;
      } else {
        return -Number.MIN_VALUE;
      }
    }

    // Increment or decrement the bit pattern
    let hiByte, loByte;
    if (sign > 0) {
      // Next number toward y (where y > x)
      loByte = bytes[0] + 1;
      hiByte = bytes[1];
      if (loByte > 255) {
        loByte = 0;
        hiByte++;
        if (hiByte > 255) {
          // Carry to higher bytes
          let i = 2;
          while (i < 8 && bytes[i] === 255) {
            bytes[i] = 0;
            i++;
          }
          if (i < 8) bytes[i]++;
        } else {
          bytes[1] = hiByte;
        }
      }
      bytes[0] = loByte;
    } else {
      // Next number toward y (where y < x)
      loByte = bytes[0];
      if (loByte === 0) {
        loByte = 255;
        hiByte = bytes[1] - 1;
        if (hiByte < 0) {
          // Borrow from higher bytes
          let i = 2;
          while (i < 8 && bytes[i] === 0) {
            bytes[i] = 255;
            i++;
          }
          if (i < 8) bytes[i]--;
        } else {
          bytes[1] = hiByte;
        }
      } else {
        bytes[0] = loByte - 1;
      }
    }

    return doubles[0];
  };
}

// Enhanced Kahan summation for better numerical stability
if (!Math.kahanSum) {
  Math.kahanSum = function (values) {
    let sum = 0;
    let compensation = 0;

    for (let i = 0; i < values.length; i++) {
      const y = values[i] - compensation;
      const t = sum + y;
      compensation = t - sum - y;
      sum = t;
    }

    return sum;
  };
}

// Augment console with memory usage reporting
const originalLog = console.log;
console.log = function (...args) {
  originalLog.apply(console, args);
  if (
    process.env.EXTREME_TESTING === "true" &&
    args[0] &&
    typeof args[0] === "string" &&
    args[0].includes("MEMORY")
  ) {
    const used = process.memoryUsage();
    originalLog("Memory usage:");
    for (const key in used) {
      originalLog(
        `  ${key}: ${Math.round((used[key] / 1024 / 1024) * 100) / 100} MB`,
      );
    }
  }
};

// Add global garbage collection request function
global.requestGC = function () {
  if (global.gc) {
    global.gc();
    console.log("Manual garbage collection performed");
  } else {
    console.log(
      "Garbage collection not available. Run node with --expose-gc flag",
    );
  }
};
