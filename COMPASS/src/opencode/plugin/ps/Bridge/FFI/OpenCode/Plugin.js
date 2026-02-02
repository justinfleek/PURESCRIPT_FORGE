// OpenCode Plugin SDK FFI Implementation
// These functions interact with the OpenCode SDK runtime environment
"use strict";

// | Get event type from OpenCode Event object
// | Event is provided by OpenCode SDK at runtime
exports.getEventType = function(event) {
  return function() {
    // OpenCode SDK provides event.type or event.eventType
    if (event && typeof event === "object") {
      return event.type || event.eventType || "unknown";
    }
    return "unknown";
  };
};

// | Get event payload as JSON string
// | Event is provided by OpenCode SDK at runtime
exports.getEventPayload = function(event) {
  return function() {
    // Extract payload from OpenCode Event object
    if (event && typeof event === "object") {
      // OpenCode SDK provides event.payload or event.data
      var payload = event.payload || event.data || event;
      try {
        return JSON.stringify(payload);
      } catch (e) {
        return "{}";
      }
    }
    return "{}";
  };
};
