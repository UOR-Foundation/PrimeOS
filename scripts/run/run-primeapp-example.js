/**
 * PrimeOS - Run PrimeApp Example
 * Demonstrates loading and using a PrimeApp
 */

const path = require('path');
const Prime = require('../../src/core');
const { PrimeVeneer } = require('../../src/veneer/core');

// Configure logging
Prime.Logger.setLevel('DEBUG');

// Main function
async function main() {
  console.log('PrimeOS - PrimeApp Example');
  console.log('-------------------------');
  
  try {
    // Create veneer instance
    const veneer = new PrimeVeneer({
      debug: true,
      storageProvider: 'memory',
      appDirectories: [
        path.resolve(__dirname, '../../primeApps/examples')
      ]
    });
    
    // Initialize veneer
    console.log('Initializing PrimeOS Veneer...');
    await veneer.init();
    
    // Discover available apps
    console.log('\nDiscovering PrimeApps...');
    const availableApps = veneer.getAvailableApps();
    
    console.log(`Found ${availableApps.length} PrimeApps:`);
    for (const app of availableApps) {
      console.log(`- ${app.displayName || app.id} (${app.version})`);
    }
    
    // Load the simple example app
    console.log('\nLoading simple example app...');
    const appDir = path.resolve(__dirname, '../../primeApps/examples/simple');
    const app = await veneer.loadApp(appDir, { force: true });
    
    console.log('App loaded with ID:', app.metadata.name);
    
    // No need to override getResource now that we've properly implemented the resource system
    
    // Initialize the app
    console.log('\nInitializing app...');
    await app.init();
    
    // Start the app
    console.log('\nStarting app...');
    await app.start();
    
    // Use app functionality
    console.log('\nUsing app functionality...');
    const result = app.processMessage('Hello, PrimeOS!');
    console.log('Process message result:', result);
    
    // Pause the app
    console.log('\nPausing app...');
    await app.pause();
    
    // Resume the app
    console.log('\nResuming app...');
    await app.resume();
    
    // Process another message
    console.log('\nUsing app functionality again...');
    const result2 = app.processMessage('Another message from PrimeOS!');
    console.log('Process message result:', result2);
    
    // Calculate coherence
    console.log('\nCalculating app coherence...');
    const coherenceScore = app.calculateCoherence();
    console.log('App coherence score:', coherenceScore);
    
    // Calculate system coherence
    console.log('\nCalculating system coherence...');
    const systemCoherence = veneer.calculateSystemCoherence();
    console.log('System coherence score:', systemCoherence);
    
    // Wait for a bit
    await new Promise(resolve => setTimeout(resolve, 3000));
    
    // Stop the app
    console.log('\nStopping app...');
    await app.stop();
    
    // Unload the app
    console.log('\nUnloading app...');
    await veneer.unloadApp(app.metadata.name);
    
    // Shutdown veneer
    console.log('\nShutting down veneer...');
    await veneer.shutdown();
    
    console.log('\nExample completed successfully!');
  } catch (error) {
    console.error('Error running example:', error);
    process.exit(1);
  }
}

// Run the main function
main().catch(console.error);