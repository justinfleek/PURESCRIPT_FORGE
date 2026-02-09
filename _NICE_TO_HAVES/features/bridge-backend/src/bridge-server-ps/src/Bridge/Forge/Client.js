// Forge Client FFI Implementation


export const wrapClient = function(sdkClient) {
  return sdkClient;
};

export const processEventStream = function(store) {
  return function(logger) {
    return function(stream) {
      return function() {
        return new Promise(function(resolve) {
          // Process event stream asynchronously
          (async function() {
            try {
              // Removed: require("./Bridge/FFI/Forge/SDK.js")
              while (true) {
                var eventResult = await sdk.nextEvent(stream)();
                if (eventResult.tag === "Right") {
                  if (eventResult.value.tag === "Just") {
                    var globalEvent = eventResult.value.value;
                    var eventType = sdk.getEventType(globalEvent)();
                    var eventPayload = sdk.getEventPayload(globalEvent)();
                    
                    // Forward event to state store via PureScript handler
                    // This would call: Bridge.Forge.Events.handleForgeEvent(store, eventPayload)
                    // Removed: require("./Bridge/Forge/Events.js")
                    eventsModule.handleForgeEvent(store)(eventPayload)();
                    
                    console.log("Forge event:", eventType, globalEvent.directory);
                  } else {
                    // Stream ended
                    break;
                  }
                } else {
                  console.error("Event stream error:", eventResult.value);
                  break;
                }
              }
            } catch (e) {
              console.error("Event stream processing error:", e);
            }
            resolve({});
          })();
        });
      };
    };
  };
};
