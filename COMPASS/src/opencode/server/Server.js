// FFI for Opencode.Server.Server
// Provides HTTP server functionality via Node.js http module

"use strict";

let currentServer = null;

// Start HTTP server
export const startHttpServer = (config) => () => {
  return new Promise((resolve, reject) => {
    try {
      const http = require('http');
      
      const server = http.createServer((req, res) => {
        // Basic request handling
        const url = new URL(req.url, `http://${config.hostname}:${config.port}`);
        
        // CORS headers
        res.setHeader('Access-Control-Allow-Origin', '*');
        res.setHeader('Access-Control-Allow-Methods', 'GET, POST, PUT, PATCH, DELETE, OPTIONS');
        res.setHeader('Access-Control-Allow-Headers', 'Content-Type, Authorization, X-OpenCode-Directory');
        
        if (req.method === 'OPTIONS') {
          res.writeHead(204);
          res.end();
          return;
        }
        
        // Route to appropriate handler
        // For now, return 501 Not Implemented
        res.writeHead(501, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ error: 'Route not implemented in FFI layer' }));
      });
      
      server.listen(config.port, config.hostname, () => {
        currentServer = server;
        resolve({ value0: undefined }); // Right unit
      });
      
      server.on('error', (err) => {
        resolve({ value0: `Server error: ${err.message}` }); // Left error
      });
    } catch (err) {
      resolve({ value0: `Failed to start server: ${err.message}` }); // Left error
    }
  });
};

// Stop HTTP server
export const stopHttpServer = () => {
  return new Promise((resolve) => {
    if (currentServer) {
      currentServer.close(() => {
        currentServer = null;
        resolve();
      });
    } else {
      resolve();
    }
  });
};
