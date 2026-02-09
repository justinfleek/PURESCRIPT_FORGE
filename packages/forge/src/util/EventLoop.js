// FFI for Forge.Util.EventLoop
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/eventloop.ts

import { defaultLogger as Log } from "./Log.js";

export const wait = () => {
  return new Promise((resolve) => {
    const check = () => {
      const active = [...process._getActiveHandles(), ...process._getActiveRequests()];
      Log.info("eventloop")({ active })();
      if (process._getActiveHandles().length === 0 && process._getActiveRequests().length === 0) {
        resolve();
      } else {
        setImmediate(check);
      }
    };
    check();
  });
};
