"use strict";

const net = require("net");

/**
 * Find an available port starting from startPort
 */
exports.findAvailablePortFFI = function (startPort) {
  return function () {
    return findAvailablePort(startPort);
  };
  
  function findAvailablePort(port) {
    return new Promise((resolve) => {
      const server = net.createServer();
      
      server.listen(port, () => {
        const actualPort = server.address().port;
        server.close(() => {
          resolve(actualPort);
        });
      });
      
      server.on("error", () => {
        findAvailablePort(port + 1).then(resolve);
      });
    });
  }
};
