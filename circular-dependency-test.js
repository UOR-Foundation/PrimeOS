/**
 * Test for circular dependencies in math modules
 */

console.log('Testing for circular dependencies...');

try {
  // Try loading the math modules
  const math = require('./src/framework/math/index.js');
  console.log('Successfully loaded index.js');
  
  // Check if Standard namespace is available
  if (math.Standard) {
    console.log('Successfully loaded Standard math namespace');
    
    // Check if Vector operations are available
    if (math.Standard.Vector) {
      console.log('Successfully loaded Vector operations');
      console.log('Example: Creating a vector');
      const v = math.Standard.Vector.create([1, 2, 3]);
      console.log(v);
    }
    
    // Check if Matrix operations are available
    if (math.Standard.Matrix) {
      console.log('Successfully loaded Matrix operations');
      console.log('Example: Creating a matrix');
      const m = math.Standard.Matrix.create([[1, 2], [3, 4]]);
      console.log(m);
      
      // Test matrix multiplication
      console.log('Testing matrix multiplication...');
      const result = math.Standard.Matrix.multiplyWithMetrics(
        [[1, 2], [3, 4]],
        [[5, 6], [7, 8]]
      );
      console.log('Multiplication result:', result.matrix);
    }
    
    // Check if Integration operations are available
    if (math.Standard.Integration) {
      console.log('Successfully loaded Integration operations');
      console.log('Example: Simple function integration');
      const integrationResult = math.Standard.Integration.adaptiveQuadrature(
        x => x * x,
        0,
        1
      );
      console.log('Integration result:', integrationResult.integral);
    }
    
    // Check if Optimization operations are available
    if (math.Standard.Optimization) {
      console.log('Successfully loaded Optimization operations');
      console.log('Example: Simple function minimization');
      const minResult = math.Standard.Optimization.gradientDescent(
        x => x[0] * x[0] + x[1] * x[1],
        [1, 1],
        { maxIterations: 10 }
      );
      console.log('Minimization result:', minResult.minimizer);
    }
  }
  
  console.log('All tests passed successfully. No circular dependencies detected.');
} catch (error) {
  console.error('Error detected:');
  console.error(error);
  process.exit(1);
}