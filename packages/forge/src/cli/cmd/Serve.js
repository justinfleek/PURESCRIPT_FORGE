// Forge.CLI.Cmd.Serve FFI

import * as http from 'http';

export const startServerFFI = (port) => (host) => (cors) => async () => {
  try {
    const server = http.createServer((req, res) => {
      if (cors) {
        res.setHeader('Access-Control-Allow-Origin', '*');
        res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
        res.setHeader('Access-Control-Allow-Headers', 'Content-Type, Authorization');
        if (req.method === 'OPTIONS') {
          res.writeHead(204);
          res.end();
          return;
        }
      }
      res.writeHead(200, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ status: 'ok', service: 'forge' }));
    });

    await new Promise((resolve, reject) => {
      server.listen(port, host, () => {
        console.log('Forge server listening on ' + host + ':' + port);
        resolve();
      });
      server.on('error', reject);
    });
    return { tag: 'Right', value: {} };
  } catch (err) {
    return { tag: 'Left', value: err.message };
  }
};
