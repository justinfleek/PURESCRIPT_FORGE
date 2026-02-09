// FFI for Forge.Session.Status
// 1:1 parity with opencode-dev/packages/opencode/src/session/status.ts

import { BusEvent } from "../bus/BusEvent.js";
import { Bus } from "../bus/Index.js";
import { Instance } from "../project/Instance.js";

export const Event = {
  Status: BusEvent.define("session.status", {
    sessionID: "string",
    status: "object",
  }),
  // deprecated
  Idle: BusEvent.define("session.idle", {
    sessionID: "string",
  }),
};

const state = Instance.state(() => ({}));

export const get = (sessionID) => () => 
  state()[sessionID] ?? { type: "idle" };

export const list = () => state();

export const set = (sessionID) => (status) => () => {
  Bus.publish(Event.Status, {
    sessionID,
    status,
  });
  if (status.type === "idle") {
    // deprecated
    Bus.publish(Event.Idle, {
      sessionID,
    });
    delete state()[sessionID];
    return;
  }
  state()[sessionID] = status;
};
