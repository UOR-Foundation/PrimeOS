#!/bin/bash

# PrimeOS Browser Test Suite
# This script starts a server and runs all browser tests for the reference implementation

echo "╔═══════════════════════════════════════════════════════════╗"
echo "║                                                           ║"
echo "║   PrimeOS Reference Implementation                        ║"
echo "║   Browser Test Suite                                      ║"
echo "║                                                           ║"
echo "╚═══════════════════════════════════════════════════════════╝"
echo ""

# Kill any existing server process
echo "Stopping any existing servers..."
pkill -f "serve ." || true

# Check if puppeteer is installed
if ! [ -d "node_modules/puppeteer" ]; then
  echo "Installing puppeteer for browser testing..."
  npm install --no-save puppeteer
fi

# Create screenshots directory if it doesn't exist
if ! [ -d "tests/screenshots" ]; then
  mkdir -p tests/screenshots
  echo "Created screenshots directory"
fi

# Start the server
echo "Starting test server..."
npx serve . > server.log 2>&1 &
SERVER_PID=$!
echo "Server PID: $SERVER_PID"

# Wait for server to start
echo "Waiting for server to start..."
sleep 3

# Save server PID
echo $SERVER_PID > server.pid

# Verify the server is running
if kill -0 $SERVER_PID 2>/dev/null; then
  echo "Server is running successfully!"
  echo "Server is available at http://localhost:3000"
else
  echo "Failed to start server. Check server.log for details."
  exit 1
fi

# List browser test URLs
echo ""
echo "Browser test URLs:"
echo "1. Topology Visualizer: http://localhost:3000/tests/topology-visualizer-browser-test"
echo "2. Context Sharing: http://localhost:3000/tests/context-sharing-browser-test"
echo "3. Extension System: http://localhost:3000/tests/extension-system-browser-test"
echo "4. Manifold Import/Export: http://localhost:3000/tests/manifold-import-export-browser-test"
echo ""

# Run automated browser tests
echo "Running automated browser tests..."
node run-browser-tests.js

# Check if there's a GitHub Codespace URL
if [ -n "$CODESPACE_NAME" ] && [ -n "$GITHUB_CODESPACES_PORT_FORWARDING_DOMAIN" ]; then
  echo ""
  echo "GitHub Codespace URLs:"
  echo "1. Topology Visualizer: https://$CODESPACE_NAME-3000.$GITHUB_CODESPACES_PORT_FORWARDING_DOMAIN/tests/topology-visualizer-browser-test"
  echo "2. Context Sharing: https://$CODESPACE_NAME-3000.$GITHUB_CODESPACES_PORT_FORWARDING_DOMAIN/tests/context-sharing-browser-test"
  echo "3. Extension System: https://$CODESPACE_NAME-3000.$GITHUB_CODESPACES_PORT_FORWARDING_DOMAIN/tests/extension-system-browser-test"
  echo "4. Manifold Import/Export: https://$CODESPACE_NAME-3000.$GITHUB_CODESPACES_PORT_FORWARDING_DOMAIN/tests/manifold-import-export-browser-test"
fi

# Instructions for manual testing
echo ""
echo "To manually test the components:"
echo "1. Open the URLs above in your browser"
echo "2. Interact with the UI elements to test functionality"
echo "3. Check the logs displayed in the UI"
echo ""
echo "Press Ctrl+C to stop the server"

# Wait for user to press Ctrl+C
trap "kill $SERVER_PID; rm -f server.pid; exit 0" INT TERM EXIT
while [ -e /proc/$SERVER_PID ]; do
  sleep 1
done