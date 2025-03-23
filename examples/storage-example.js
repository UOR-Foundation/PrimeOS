/**
 * PrimeOS Storage Module Example
 * Demonstrates the usage of the storage module for large data processing
 */

const Prime = require('../src');

// Simple example of using the storage module
async function storageExample() {
  console.log('PrimeOS Storage Example');
  console.log('======================');

  // Create a storage manager
  const storageManager = Prime.Storage.createManager();
  
  // Initialize the manager
  await storageManager.init();
  
  console.log(`\nUsing storage provider: ${storageManager.getProviderType()}`);
  
  // Store some data
  const data = {
    name: 'Example Data',
    items: Array.from({ length: 1000 }, (_, i) => ({
      id: i,
      value: `Item ${i}`,
      timestamp: Date.now()
    })),
    metadata: {
      created: new Date().toISOString(),
      version: '1.0.0'
    }
  };
  
  console.log('\nStoring large dataset...');
  const id = await storageManager.store(data);
  console.log(`Data stored with ID: ${id}`);
  
  // Get storage info
  const storageInfo = await storageManager.getStorageInfo();
  console.log('\nStorage Information:');
  console.log(`- Provider: ${storageInfo.provider}`);
  console.log(`- Available: ${formatBytes(storageInfo.available)}`);
  console.log(`- Used: ${formatBytes(storageInfo.used)}`);
  console.log(`- Total: ${formatBytes(storageInfo.total)}`);
  
  // Load the data
  console.log('\nLoading data...');
  const loadedData = await storageManager.load(id);
  console.log(`Loaded data with ${loadedData.items.length} items`);
  console.log(`First item: ${JSON.stringify(loadedData.items[0])}`);
  console.log(`Last item: ${JSON.stringify(loadedData.items[loadedData.items.length - 1])}`);
  
  // Demonstrate streaming
  console.log('\nDemonstrating streaming API...');
  const stream = storageManager.createReadStream(id);
  
  let streamData = null;
  await new Promise((resolve) => {
    stream.on('data', (data) => {
      streamData = data;
      console.log('Stream data received');
    });
    
    stream.on('end', () => {
      console.log('Stream ended');
      resolve();
    });
  });
  
  // Demonstrate storing and accessing a large array without loading it entirely
  console.log('\nStoring and accessing a large array...');
  
  // Create a large array (but smaller than our example above)
  const largeArray = Array.from({ length: 10000 }, (_, i) => ({
    index: i,
    value: `Large item ${i}`,
    timestamp: Date.now()
  }));
  
  // Store the array
  const largeArrayId = await storageManager.store(largeArray);
  console.log(`Large array stored with ID: ${largeArrayId}`);
  
  // Access specific items without loading the whole array
  console.log('\nAccessing specific items:');
  const fullArray = await storageManager.load(largeArrayId);
  console.log(`Item 0: ${JSON.stringify(fullArray[0])}`);
  console.log(`Item 9999: ${JSON.stringify(fullArray[9999])}`);
  
  // Process the array in chunks using a stream
  console.log('\nProcessing array in chunks:');
  const arrayStream = storageManager.createReadStream(largeArrayId);
  
  let chunkCount = 0;
  await new Promise((resolve) => {
    arrayStream.on('data', (chunk) => {
      if (Array.isArray(chunk) && chunk.length > 0) {
        chunkCount++;
        console.log(`Processing chunk ${chunkCount} with ${chunk.length} items`);
      }
    });
    
    arrayStream.on('end', () => {
      console.log('Array processing complete');
      resolve();
    });
  });
  
  // Clean up
  console.log('\nCleaning up...');
  await Promise.all([
    storageManager.delete(id),
    storageManager.delete(largeArrayId)
  ]);
  console.log('Example completed!');
}

// Helper function to format bytes
function formatBytes(bytes, decimals = 2) {
  if (bytes === 0) return '0 Bytes';
  
  const k = 1024;
  const dm = decimals < 0 ? 0 : decimals;
  const sizes = ['Bytes', 'KB', 'MB', 'GB', 'TB', 'PB', 'EB', 'ZB', 'YB'];
  
  const i = Math.floor(Math.log(bytes) / Math.log(k));
  
  return parseFloat((bytes / Math.pow(k, i)).toFixed(dm)) + ' ' + sizes[i];
}

// Run the example
storageExample().catch(console.error);