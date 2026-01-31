// OpenCode Client FFI Implementation
"use strict";

exports.wrapClient = function(sdkClient) {
  return sdkClient;
};

exports.processEventStream = function(store) {
  return function(logger) {
    return function(stream) {
      return function() {
        return new Promise(function(resolve) {
          // Process event stream asynchronously
          (async function() {
            try {
              var sdk = require("./Bridge/FFI/OpenCode/SDK.js");
              while (true) {
                var eventResult = await sdk.nextEvent(stream)();
                if (eventResult.tag === "Right") {
                  if (eventResult.value.tag === "Just") {
                    var globalEvent = eventResult.value.value;
                    var eventType = sdk.getEventType(globalEvent)();
                    var eventPayload = sdk.getEventPayload(globalEvent)();
                    
                    // Forward event to state store via PureScript handler
                    // This would call: Bridge.Opencode.Events.handleOpenCodeEvent(store, eventPayload)
                    var eventsModule = require("./Bridge/Opencode/Events.js");
                    eventsModule.handleOpenCodeEvent(store)(eventPayload)();
                    
                    console.log("OpenCode event:", eventType, globalEvent.directory);
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
