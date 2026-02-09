// Notification Service FFI Implementation
"use strict";

// Helper: Explicit default value (replaces banned || pattern)
function explicitDefault(value, defaultValue) {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
}

var crypto = require("crypto");

exports.create = function(wsManager) {
  return function(logger) {
    return function() {
      return {
        wsManager: wsManager,
        logger: logger,
        notifications: []
      };
    };
  };
};

exports.notify = function(service) {
  return function(notificationJson) {
    return function() {
      try {
        var notification = JSON.parse(notificationJson);
        notification.id = explicitDefault(notification.id, crypto.randomUUID());
        notification.timestamp = explicitDefault(notification.timestamp, new Date().toISOString());
        
        // Store notification
        if (!service.notifications) {
          service.notifications = [];
        }
        service.notifications.push(notification);
        
        // Broadcast to all connected clients via WebSocket manager
        if (service.wsManager && typeof service.wsManager.broadcast === "function") {
          var broadcastMessage = JSON.stringify({
            jsonrpc: "2.0",
            method: "notification",
            params: notification
          });
          service.wsManager.broadcast(broadcastMessage)();
        } else if (service.wsManager && service.wsManager.broadcast) {
          // Handle PureScript FFI function
          var broadcastMessage = JSON.stringify({
            jsonrpc: "2.0",
            method: "notification",
            params: notification
          });
          service.wsManager.broadcast(broadcastMessage)();
        }
        
        // Log notification
        if (service.logger) {
          service.logger.info("Notification: " + notification.title);
        }
      } catch (e) {
        console.error("Failed to send notification:", e);
      }
    };
  };
};

exports.encodeNotification = function(notification) {
  return JSON.stringify({
    type: notification.type_,
    level: notification.level,
    title: notification.title,
    message: explicitDefault(notification.message, null)
  });
};

exports.dismiss = function(service) {
  return function(id) {
    return function() {
      try {
        // Remove notification from list
        if (service.notifications && Array.isArray(service.notifications)) {
          service.notifications = service.notifications.filter(function(n) {
            return n.id !== id;
          });
        }
        
        // Broadcast dismissal to clients
        if (service.wsManager && typeof service.wsManager.broadcast === "function") {
          var broadcastMessage = JSON.stringify({
            jsonrpc: "2.0",
            method: "notification.dismissed",
            params: { id: id }
          });
          service.wsManager.broadcast(broadcastMessage)();
        } else if (service.wsManager && service.wsManager.broadcast) {
          var broadcastMessage = JSON.stringify({
            jsonrpc: "2.0",
            method: "notification.dismissed",
            params: { id: id }
          });
          service.wsManager.broadcast(broadcastMessage)();
        }
        
        // Log dismissal
        if (service.logger) {
          service.logger.info("Notification dismissed: " + id);
        }
      } catch (e) {
        console.error("Failed to dismiss notification:", e);
      }
    };
  };
};

exports.dismissAll = function(service) {
  return function() {
    try {
      // Clear all notifications
      if (service.notifications) {
        service.notifications = [];
      }
      
      // Broadcast dismissal to clients
      if (service.wsManager && typeof service.wsManager.broadcast === "function") {
        var broadcastMessage = JSON.stringify({
          jsonrpc: "2.0",
          method: "notification.dismissedAll",
          params: {}
        });
        service.wsManager.broadcast(broadcastMessage)();
      } else if (service.wsManager && service.wsManager.broadcast) {
        var broadcastMessage = JSON.stringify({
          jsonrpc: "2.0",
          method: "notification.dismissedAll",
          params: {}
        });
        service.wsManager.broadcast(broadcastMessage)();
      }
      
      // Log dismissal
      if (service.logger) {
        service.logger.info("All notifications dismissed");
      }
    } catch (e) {
      console.error("Failed to dismiss all notifications:", e);
    }
  };
};
