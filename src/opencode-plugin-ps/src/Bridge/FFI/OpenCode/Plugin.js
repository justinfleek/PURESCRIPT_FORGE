// OpenCode Plugin SDK FFI Implementation
// These functions interact with the OpenCode SDK runtime environment

// | Get event type from OpenCode Event object
// | Event is provided by OpenCode SDK at runtime
export const getEventType = (event) => () => {
  // OpenCode SDK provides event.type or event.eventType
  if (event && typeof event === "object") {
    return event.type || event.eventType || "unknown";
  }
  return "unknown";
};

// | Get event payload as JSON string
// | Event is provided by OpenCode SDK at runtime
export const getEventPayload = (event) => () => {
  // Extract payload from OpenCode Event object
  if (event && typeof event === "object") {
    // OpenCode SDK provides event.payload or event.data
    const payload = event.payload || event.data || event;
    try {
      return JSON.stringify(payload);
    } catch (e) {
      return "{}";
    }
  }
  return "{}";
};
