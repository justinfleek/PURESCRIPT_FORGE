// FFI for Forge.Util.Signal
// 1:1 port from _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/util/signal.ts

export const create = () => {
  let resolve;
  const promise = new Promise((r) => (resolve = r));
  return {
    trigger: () => {
      return resolve();
    },
    wait: () => promise,
  };
};

export const trigger = (signal) => () => {
  signal.trigger();
};

export const wait = (signal) => () => signal.wait();
