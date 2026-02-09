// Forge.Bus.Global FFI - Global event bus
// 1:1 parity with opencode-dev/packages/opencode/src/bus/index.ts

// Event bus state
const subscribers = new Map(); // Map<eventType, Set<handler>>
const history = [];
const MAX_HISTORY = 100;

// Publish event to all subscribers (PureScript FFI)
export const publishFFI = (event) => () => {
  // Add to history
  history.push(event);
  if (history.length > MAX_HISTORY) {
    history.shift();
  }
  
  // Notify subscribers for this event type
  const handlers = subscribers.get(event.type) || new Set();
  for (const handler of handlers) {
    try {
      handler(event)();
    } catch (err) {
      console.error('Bus subscriber error:', err);
    }
  }
  
  // Notify wildcard subscribers
  const wildcardHandlers = subscribers.get("*") || new Set();
  for (const handler of wildcardHandlers) {
    try {
      handler(event)();
    } catch (err) {
      console.error('Bus subscriber error:', err);
    }
  }
};

// Subscribe to events (PureScript FFI)
export const subscribeFFI = (handler) => () => {
  if (!subscribers.has("*")) {
    subscribers.set("*", new Set());
  }
  subscribers.get("*").add(handler);
  
  // Return unsubscribe function
  return () => {
    subscribers.get("*").delete(handler);
  };
};

// Get event history
export const getHistoryFFI = () => {
  return [...history];
};

// Clear event history
export const clearHistoryFFI = () => {
  history.length = 0;
};

// Reset bus
export const resetFFI = () => {
  subscribers.clear();
  history.length = 0;
};

// Get subscriber count
export const getSubscriberCountFFI = () => {
  let count = 0;
  for (const [, handlers] of subscribers) {
    count += handlers.size;
  }
  return count;
};

// Get current timestamp
export const nowFFI = () => {
  return Date.now();
};

// ============================================================================
// Direct JavaScript API (for use by other JS modules like Session.js)
// ============================================================================

// Subscribe to a specific event type
export function subscribe(eventType, handler) {
  if (!subscribers.has(eventType)) {
    subscribers.set(eventType, new Set());
  }
  subscribers.get(eventType).add(handler);
  
  // Return unsubscribe function
  return () => {
    subscribers.get(eventType).delete(handler);
  };
}

// Publish an event (direct JS call)
export function publish(eventType, payload) {
  const event = {
    type: eventType,
    payload,
    timestamp: Date.now(),
  };
  
  // Add to history
  history.push(event);
  if (history.length > MAX_HISTORY) {
    history.shift();
  }
  
  // Notify subscribers for this event type
  const handlers = subscribers.get(eventType) || new Set();
  for (const handler of handlers) {
    try {
      // Handle both sync and async handlers
      const result = handler(payload);
      if (result && typeof result.catch === "function") {
        result.catch((err) => console.error("Bus handler error:", err));
      }
    } catch (err) {
      console.error("Bus subscriber error:", err);
    }
  }
  
  // Notify wildcard subscribers
  const wildcardHandlers = subscribers.get("*") || new Set();
  for (const handler of wildcardHandlers) {
    try {
      const result = handler(event);
      if (result && typeof result.catch === "function") {
        result.catch((err) => console.error("Bus handler error:", err));
      }
    } catch (err) {
      console.error("Bus subscriber error:", err);
    }
  }
}

// Namespace export for direct usage
export const Bus = {
  subscribe,
  publish,
  getHistory: () => [...history],
  clearHistory: () => { history.length = 0; },
  reset: () => { subscribers.clear(); history.length = 0; },
};
