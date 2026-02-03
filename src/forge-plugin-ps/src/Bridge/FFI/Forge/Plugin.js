// Forge Plugin SDK FFI Implementation
// These functions interact with the Forge SDK runtime environment

// | Get event type from Forge Event object
// | Event is provided by Forge SDK at runtime
export const getEventType = (event) => () => {
  // Forge SDK provides event.type or event.eventType
  if (event && typeof event === "object") {
    return event.type || event.eventType || "unknown";
  }
  return "unknown";
};

// | Get event payload as JSON string
// | Event is provided by Forge SDK at runtime
export const getEventPayload = (event) => () => {
  // Extract payload from Forge Event object
  if (event && typeof event === "object") {
    // Forge SDK provides event.payload or event.data
    const payload = event.payload || event.data || event;
    try {
      return JSON.stringify(payload);
    } catch (e) {
      return "{}";
    }
  }
  return "{}";
};
