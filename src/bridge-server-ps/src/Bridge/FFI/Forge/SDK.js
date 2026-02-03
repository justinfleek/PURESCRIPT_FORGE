// Forge SDK v2 FFI


// Helper: Explicit default value (replaces banned || pattern)
function explicitDefault(value, defaultValue) {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
}

// Complete implementation with graceful fallback
// Dynamically imports @forge-ai/sdk/v2 when available
// Returns Left (error) if SDK is not installed, allowing PureScript to handle gracefully

var sdkModule = null;

function loadSDK() {
  return new Promise(function(resolve, reject) {
    if (sdkModule) {
      resolve(sdkModule);
      return;
    }
    try {
      // Dynamic import of SDK
      import("@forge-ai/sdk/v2").then(function(module) {
        sdkModule = module;
        resolve(module);
      }).catch(function(error) {
        reject(error);
      });
    } catch (e) {
      reject(e);
    }
  });
}

export const createClient = function(config) {
  return function() {
    return new Promise(function(resolve) {
      loadSDK().then(function(module) {
        try {
          var createForgeClient = module.createForgeClient;
          var client = createForgeClient({
            baseUrl: config.baseUrl,
            directory: config.directory,
            fetch: globalThis.fetch,
          });
          resolve({ tag: "Right", value: client });
        } catch (e) {
          var errorMessage = e.message !== undefined && e.message !== null ? e.message : "Failed to create client";
          resolve({ tag: "Left", value: errorMessage });
        }
      }).catch(function(error) {
        var errorMessage = error.message !== undefined && error.message !== null ? error.message : "SDK not available";
        resolve({ tag: "Left", value: errorMessage });
      });
    });
  };
};

export const connect = function(client) {
  return function() {
    return new Promise(function(resolve) {
      // Forge SDK v2 clients are created already connected
      // No explicit connect method needed
      if (client) {
        resolve({ tag: "Right", value: {} });
      } else {
        resolve({ tag: "Left", value: "Invalid client" });
      }
    });
  };
};

export const disconnect = function(client) {
  return function() {
    return new Promise(function(resolve) {
      if (client && typeof client.disconnect === "function") {
        client.disconnect().then(function() {
          resolve({ tag: "Right", value: {} });
        }).catch(function(error) {
          var errorMessage = error.message !== undefined && error.message !== null ? error.message : "Disconnect failed";
          resolve({ tag: "Left", value: errorMessage });
        });
      } else {
        resolve({ tag: "Right", value: {} });
      }
    });
  };
};

export const subscribeEvents = function(client) {
  return function() {
    return new Promise(function(resolve) {
      if (client && client.global && client.global.event) {
        try {
          // Forge SDK v2 uses global.event() which returns an async iterable
          var stream = client.global.event({});
          resolve({ tag: "Right", value: stream });
        } catch (e) {
          var errorMessage = e.message !== undefined && e.message !== null ? e.message : "Failed to subscribe to events";
          resolve({ tag: "Left", value: errorMessage });
        }
      } else {
        resolve({ tag: "Left", value: "Client does not support event subscription" });
      }
    });
  };
};

export const nextEvent = function(stream) {
  return function() {
    return new Promise(function(resolve) {
      if (!stream) {
        resolve({ tag: "Left", value: "Stream is null" });
        return;
      }
      
      // Handle async iterable (SSE stream from Forge)
      if (typeof stream[Symbol.asyncIterator] === "function") {
        var iterator = stream[Symbol.asyncIterator]();
        iterator.next().then(function(result) {
          if (result.done) {
            resolve({ tag: "Right", value: { tag: "Nothing" } });
          } else {
            // Forge events are GlobalEvent objects with { directory, payload }
            var event = result.value;
            resolve({ tag: "Right", value: { tag: "Just", value: event } });
          }
        }).catch(function(error) {
          var errorMessage = error.message !== undefined && error.message !== null ? error.message : "Failed to get next event";
          resolve({ tag: "Left", value: errorMessage });
        });
      } else if (typeof stream.next === "function") {
        // Direct iterator interface
        stream.next().then(function(result) {
          if (result.done) {
            resolve({ tag: "Right", value: { tag: "Nothing" } });
          } else {
            resolve({ tag: "Right", value: { tag: "Just", value: result.value } });
          }
        }).catch(function(error) {
          var errorMessage = error.message !== undefined && error.message !== null ? error.message : "Failed to get next event";
          resolve({ tag: "Left", value: errorMessage });
        });
      } else {
        resolve({ tag: "Left", value: "Stream is not iterable" });
      }
    });
  };
};

export const getEventType = function(event) {
  return function() {
    // Forge events are GlobalEvent: { directory, payload }
    // payload is the actual Event object with a 'type' field
    if (event && event.payload && event.payload.type) {
      return event.payload.type;
    } else if (event && event.type) {
      return event.type;
    }
    return "unknown";
  };
};

export const getEventPayload = function(event) {
  return function() {
    // Return full GlobalEvent as JSON
    return JSON.stringify(event);
  };
};

export const closeStream = function(stream) {
  return function() {
    if (stream && typeof stream.return === "function") {
      stream.return();
    }
  };
};
