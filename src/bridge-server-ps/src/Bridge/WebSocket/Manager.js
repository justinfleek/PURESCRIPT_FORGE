// WebSocket Manager FFI Implementation


// Helper: Explicit default value (replaces banned || pattern)
function explicitDefault(value, defaultValue) {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
}

// Removed: require("crypto")

export const setHandlerContext = function(manager) {
  return function(contextJson) {
    return function() {
      manager.handlerContext = JSON.parse(contextJson);
    };
  };
};

export const broadcast = function(manager) {
  return function(messageJson) {
    return function() {
      var message = JSON.parse(messageJson);
      var messageStr = JSON.stringify(message);
      
      // Broadcast to all connected clients
      if (manager.clients && manager.clients.value) {
        var clients = manager.clients.value;
        var clientArray = [];
        
        // Convert Map to array if needed
        if (clients.forEach) {
          clients.forEach(function(client, id) {
            clientArray.push({ id: id, connection: client });
          });
        } else if (Array.isArray(clients)) {
          clientArray = clients;
        } else if (typeof clients === "object") {
          Object.keys(clients).forEach(function(id) {
            clientArray.push({ id: id, connection: clients[id] });
          });
        }
        
        // Send to all connected clients
        clientArray.forEach(function(clientEntry) {
          var client = clientEntry.connection;
          if (client && client.ws) {
            try {
              var readyState = client.ws.readyState;
              if (readyState === 1) { // OPEN
                client.ws.send(messageStr);
              }
            } catch (e) {
              console.error("Failed to send to client:", e);
            }
          }
        });
      }
    };
  };
};

export const handleMessage = function(logger) {
  return function(store) {
    return function(message) {
      return function(ws) {
        return function() {
          try {
            var request = JSON.parse(message);
            
            // Route to handler
            if (request.jsonrpc === "2.0" && request.method) {
              // Call PureScript handler via handler context
              // The handler context should be set via setHandlerContext
              // For now, handle basic requests
              
              if (request.method === "state.get") {
                // Get state from store
                var state = store.state ? store.state.value : {};
                var response = {
                  jsonrpc: "2.0",
                  id: request.id,
                  result: state
                };
                
                if (ws.readyState === 1) {
                  ws.send(JSON.stringify(response));
                }
              } else {
                // For other methods, would call PureScript handler
                // This requires the handler context to be properly set
                logger.info("JSON-RPC request: " + request.method);
                
                // Send acknowledgment
                var response = {
                  jsonrpc: "2.0",
                  id: request.id,
                  result: { received: true, method: request.method }
                };
                
                if (ws.readyState === 1) {
                  ws.send(JSON.stringify(response));
                }
              }
            } else {
              // Invalid request
              var errorResponse = {
                jsonrpc: "2.0",
                id: explicitDefault(request.id, null),
                error: {
                  code: -32600,
                  message: "Invalid Request"
                }
              };
              
              if (ws.readyState === 1) {
                ws.send(JSON.stringify(errorResponse));
              }
            }
          } catch (e) {
            var errorMessage = e.message !== undefined && e.message !== null ? e.message : String(e);
            logger.error("Failed to handle message: " + errorMessage);
            
            // Send parse error
            try {
              var errorResponse = {
                jsonrpc: "2.0",
                id: null,
                error: {
                  code: -32700,
                  message: "Parse error",
                  data: errorMessage
                }
              };
              
              if (ws && ws.readyState === 1) {
                ws.send(JSON.stringify(errorResponse));
              }
            } catch (sendError) {
              // Ignore send errors
            }
          }
        };
      };
    };
  };
};
