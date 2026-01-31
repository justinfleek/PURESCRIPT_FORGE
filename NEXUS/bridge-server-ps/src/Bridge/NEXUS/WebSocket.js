// | FFI JavaScript bindings for NEXUS WebSocket notifications

// Global WebSocket manager registry (set by Bridge.Server)
let globalWebSocketManager = null;
let notificationHandlers = [];

// | Set global WebSocket manager (called by Bridge.Server)
exports.setGlobalWebSocketManager = function(manager) {
  return function() {
    globalWebSocketManager = manager;
  };
};

// | Convert Foreign to JSON string
exports.foreignToJsonString = function(foreignValue) {
  return function() {
    try {
      return JSON.stringify(foreignValue);
    } catch (err) {
      return "{}";
    }
  };
};

// | Convert JSON string to Foreign
exports.jsonStringToForeign = function(jsonStr) {
  return function() {
    try {
      return JSON.parse(jsonStr);
    } catch (err) {
      return {};
    }
  };
};

// | Subscribe to NEXUS notifications
exports.subscribeNEXUS_ = function(handler) {
  return function() {
    notificationHandlers.push(handler);
  };
};

// | Unsubscribe from NEXUS notifications
exports.unsubscribeNEXUS_ = function() {
  return function() {
    notificationHandlers = [];
  };
};

// | Unsubscribe specific handler (for proper cleanup)
exports.unsubscribeNEXUSHandler_ = function(handler) {
  return function() {
    notificationHandlers = notificationHandlers.filter(function(h) {
      return h !== handler;
    });
  };
};

// | Broadcast NEXUS notification
exports.broadcastNEXUS_ = function(jsonStr, foreignJson) {
  return function() {
    if (!globalWebSocketManager) {
      return;
    }
    
    try {
      const notification = JSON.parse(jsonStr);
      const message = {
        jsonrpc: "2.0",
        method: "nexus.notification",
        params: notification
      };
      
      // Broadcast via WebSocket manager
      if (globalWebSocketManager.broadcast) {
        globalWebSocketManager.broadcast(JSON.stringify(message))();
      }
      
      // Call registered handlers
      notificationHandlers.forEach(function(handler) {
        try {
          handler(foreignJson)();
        } catch (e) {
          console.error("Notification handler error:", e);
        }
      });
    } catch (e) {
      console.error("Failed to broadcast NEXUS notification:", e);
    }
  };
};
