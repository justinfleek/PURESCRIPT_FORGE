// Bridge Server FFI Implementation


export const encodeHandlerContext = function(ctx) {
  // Pure function - returns String directly (no Effect wrapper)
  return JSON.stringify({
    store: ctx.store,
    veniceClient: ctx.veniceClient,
    leanProxy: ctx.leanProxy,
    db: ctx.db,
    duckdb: ctx.duckdb,
    notificationService: ctx.notificationService
  });
};

export const setNEXUSWebSocketManager = function(wsManager) {
  return function() {
    // Set global WebSocket manager for NEXUS
    try {
      // Removed: require("../../NEXUS/bridge-server-ps/src/Bridge/NEXUS/WebSocket.js")
      if (nexusWebSocket.setGlobalWebSocketManager) {
        nexusWebSocket.setGlobalWebSocketManager(wsManager)();
      }
    } catch (e) {
      // NEXUS module may not be available in all builds
      console.warn("NEXUS WebSocket module not available:", e.message);
    }
  };
};

export const subscribeStateChanges = function(store) {
  return function(wsManager) {
    return function() {
      // Subscribe to state changes and broadcast to all WebSocket clients
      var unsubscribe = store.onStateChange(function(path, value) {
        try {
          // Broadcast state change notification to all connected clients
          var message = JSON.stringify({
            jsonrpc: "2.0",
            method: "state." + path + ".update",
            params: JSON.parse(value)
          });
          wsManager.broadcast(message)();
        } catch (e) {
          console.error("Failed to broadcast state change:", e);
        }
      })();
      
      // Monitor balance for low balance notifications
      var balanceUnsubscribe = store.onStateChange(function(path, value) {
        if (path === "balance") {
          try {
            var balanceData = JSON.parse(value);
            var diem = balanceData.venice && balanceData.venice.diem;
            var alertLevel = balanceData.alertLevel;
            
            // Check for low balance conditions
            if (typeof diem === "number") {
              if (diem < 0.01 && alertLevel !== "Critical") {
                // Critical balance - notify
                var criticalMessage = JSON.stringify({
                  jsonrpc: "2.0",
                  method: "notification.create",
                  params: {
                    type: "error",
                    title: "Critical Balance",
                    message: "Balance is critically low: " + diem.toFixed(4) + " Diem",
                    persistent: true
                  }
                });
                wsManager.broadcast(criticalMessage)();
              } else if (diem < 0.1 && alertLevel !== "Warning" && alertLevel !== "Critical") {
                // Warning balance - notify
                var warningMessage = JSON.stringify({
                  jsonrpc: "2.0",
                  method: "notification.create",
                  params: {
                    type: "warning",
                    title: "Low Balance",
                    message: "Balance is low: " + diem.toFixed(4) + " Diem",
                    persistent: false
                  }
                });
                wsManager.broadcast(warningMessage)();
              }
            }
          } catch (e) {
            console.error("Failed to process balance change:", e);
          }
        }
      })();
      
      // Store unsubscribe functions for cleanup (if needed)
      // These would be called on server shutdown
      return { unsubscribe: unsubscribe, balanceUnsubscribe: balanceUnsubscribe };
    };
  };
};
