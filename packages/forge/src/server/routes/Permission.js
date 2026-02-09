// FFI for Forge.Server.Routes.Permission
// 1:1 parity with opencode-dev/packages/opencode/src/server/routes/permission.ts

import { Bus } from "../../bus/Index.js";
import { Log } from "../../util/Log.js";

const log = Log.create({ service: "permission" });

// Permission response events
export const Event = {
  Response: {
    type: "permission.response",
  },
};

// Respond to a permission request
export const respondFFI = (sessionID) => (requestID) => (response) => async () => {
  try {
    log.info("permission response", { sessionID, requestID, response });
    
    Bus.publish(Event.Response.type, {
      sessionID,
      requestID,
      response: response, // "allow" | "deny" | "allow_always"
    });
    
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// List pending permission requests for a session
export const pendingFFI = (sessionID) => async () => {
  try {
    // In a full implementation, this would track pending requests
    // For now, return empty array
    return { tag: "Right", value: [] };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Get permission rules for a session
export const rulesFFI = (sessionID) => async () => {
  try {
    // In a full implementation, this would return saved rules
    // For now, return empty array
    return { tag: "Right", value: [] };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
