// Forge.CLI.Network FFI

import * as net from 'net';

// Check server via HTTP request
export const checkServerFFI = (url) => (timeout) => async () => {
  try {
    const controller = new AbortController();
    const timeoutId = setTimeout(() => controller.abort(), timeout);
    
    const response = await fetch(url, { 
      method: 'HEAD',
      signal: controller.signal 
    });
    
    clearTimeout(timeoutId);
    return { tag: 'Right', value: response.status };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};

// Check if port is available
export const isPortAvailableFFI = (port) => async () => {
  return new Promise((resolve) => {
    const server = net.createServer();
    
    server.once('error', (err) => {
      if (err.code === 'EADDRINUSE') {
        resolve(false);
      } else {
        resolve(false);
      }
    });
    
    server.once('listening', () => {
      server.close();
      resolve(true);
    });
    
    server.listen(port, '127.0.0.1');
  });
};

// Find available port starting from given port
export const findAvailablePortFFI = (startPort) => (maxTries) => async () => {
  for (let port = startPort; port < startPort + maxTries; port++) {
    const available = await isPortAvailableFFI(port)();
    if (available) {
      return port;
    }
  }
  return -1; // No available port found
};

// Convert int to number
export const toNumberFFI = (n) => n;
